/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Basic

/-!
# Probabilistic forward simulation and weak transitions

A probabilistic forward simulation between two PLTS over a common label
alphabet is a state relation `R` such that initial concrete states are
matched by initial abstract states with which they are `R`-related, and every
concrete transition can be matched by an abstract transition whose resulting
distribution is related to the concrete one in the sense of a *coupling*: a
joint distribution with the appropriate marginals whose support lies in `R`.

This file:
* defines `PMFRel R` — the lifting of a state relation `R : α → β → Prop` to a
  relation on `PMF α × PMF β` via the existence of a joint PMF;
* defines `StrongProbabilisticSimulation sys_C sys_A R` — the strong
  probabilistic forward simulation from `sys_C` to `sys_A`;
* defines `LabelledSystem State Label` — a system enriched with an
  `internal : Label → Prop` predicate partitioning labels into internal
  (silent) and external (observable);
* defines `WeakScheduler sys` — a path-dependent scheduler that may stop, only
  schedules internal labels, and is bounded so that any prefix of length at
  least `runtime` is forced to stop;
* defines `weakTau` — the weak (internal) transition relation `μ_init ⇒^τ μ`
  on initial distributions, obtained by binding a `WeakScheduler`'s run;
* defines `hyperStep` — the convex-closed lifting of `sys.step` to a
  hyper-transition `μ_pre -[l]→ μ_post` on distributions;
* defines `weakStep` — the weak external step `μ_init ⇒^l μ_final`, composing
  τ-closure, hyper-step, τ-closure;
* defines `WeakProbabilisticSimulation sys_C sys_A R` — the weak probabilistic
  forward simulation, where each concrete transition is matched by `weakTau`
  or `weakStep` on the abstract side, according to whether its label is
  internal in `sys_C`;
* defines `ProbabilisticForwardSimulation sys_C sys_A R` — a variant of
  `WeakProbabilisticSimulation` whose relation `R : State_C → PMF State_A →
  Prop` links each concrete state to a *distribution* over abstract states;
  equivalent modulo typing;
* defines `Stream'.Seq.filter` — a generic noncomputable filter on
  possibly-infinite sequences;
* defines `LabelledSystem.trace` — the (possibly infinite) sequence of
  external labels appearing in an execution;
* defines `LabelledSystem.traceProb` — the probability that a probabilistic
  execution produces a given trace, as the sum of execution probabilities
  over all finite executions whose trace equals the target.
-/

open Stream'

namespace Stream'.Seq

universe u
variable {α : Type u}

/-- Filter a (possibly infinite) sequence by a predicate, keeping only the
elements that satisfy it. Noncomputable: locating the next satisfying element
requires non-constructively inspecting arbitrarily many positions when the
predicate fails on a long run. -/
noncomputable def filter (p : α → Prop) (s : Seq α) : Seq α :=
  open Classical in
  Seq.corec (fun cur : Seq α =>
    if h : ∃ n, ∃ a, cur.get? n = some a ∧ p a then
      some ((Nat.find_spec h).choose, cur.drop (Nat.find h + 1))
    else none) s

/-- Filtering the empty sequence yields the empty sequence. -/
@[simp] theorem filter_nil (p : α → Prop) : (nil : Seq α).filter p = nil := by
  classical
  unfold filter
  apply corec_nil
  show (if _ : ∃ n, ∃ a, (nil : Seq α).get? n = some a ∧ p a then _ else none) = none
  rw [dif_neg]
  rintro ⟨n, a, h_eq, _⟩
  simp at h_eq

/-- Mapping the empty sequence yields the empty sequence. -/
@[simp] theorem map_nil {β : Type v} (f : α → β) :
    (nil : Seq α).map f = (nil : Seq β) := by
  ext n
  simp [map, get?, nil]

/-- Filtering `cons a s` by a predicate that holds at `a`: the result is
`cons a (s.filter p)`. -/
theorem filter_cons_pos {p : α → Prop} (a : α) (s : Seq α) (h : p a) :
    (cons a s).filter p = cons a (s.filter p) := by
  classical
  unfold filter
  apply corec_cons
  have h_ex : ∃ n, ∃ a', (cons a s).get? n = some a' ∧ p a' :=
    ⟨0, a, by simp, h⟩
  have h_find_zero : Nat.find h_ex = 0 :=
    (Nat.find_eq_zero h_ex).mpr ⟨a, by simp, h⟩
  change (if h' : ∃ n, ∃ a', (cons a s).get? n = some a' ∧ p a' then
         some ((Nat.find_spec h').choose, (cons a s).drop (Nat.find h' + 1))
       else none) = some (a, s)
  rw [dif_pos h_ex]
  have h_choose_eq : (Nat.find_spec h_ex).choose = a := by
    have h_spec_get : (cons a s).get? (Nat.find h_ex) =
        some (Nat.find_spec h_ex).choose := (Nat.find_spec h_ex).choose_spec.1
    have h_at_zero : (cons a s).get? (Nat.find h_ex) = some a := by
      rw [h_find_zero]; simp
    have : some a = some (Nat.find_spec h_ex).choose := h_at_zero.symm.trans h_spec_get
    exact (Option.some_inj.mp this).symm
  rw [h_choose_eq, h_find_zero]
  rfl

/-- Mapping a function over `cons a s` gives `cons (f a) (s.map f)`. -/
@[simp] theorem map_cons {β : Type v} (f : α → β) (a : α) (s : Seq α) :
    (cons a s).map f = cons (f a) (s.map f) := by
  apply Subtype.ext
  funext n
  cases n <;> rfl

/-- `(cons a s).drop (n + 1) = s.drop n`: dropping one more from `cons a s` is
the same as dropping one from `s`. -/
private theorem drop_cons_succ (a : α) (s : Seq α) (n : ℕ) :
    (cons a s).drop (n + 1) = s.drop n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change tail ((cons a s).drop (k + 1)) = tail (s.drop k)
    rw [ih]

/-- Filtering `cons a s` by a predicate that fails at `a`: the result equals
`s.filter p`. -/
theorem filter_cons_neg {p : α → Prop} (a : α) (s : Seq α) (h : ¬ p a) :
    (cons a s).filter p = s.filter p := by
  classical
  apply Seq.eq_of_bisim
    (R := fun t₁ t₂ =>
      t₁ = t₂ ∨ ∃ a' s', ¬ p a' ∧ t₁ = (cons a' s').filter p ∧ t₂ = s'.filter p)
  · -- IsBisimulation
    have bisim_refl : ∀ x, BisimO
        (fun t₁ t₂ => t₁ = t₂ ∨ ∃ a' s', ¬ p a' ∧
          t₁ = (cons a' s').filter p ∧ t₂ = s'.filter p) x x := by
      intro x
      cases x with
      | none => trivial
      | some pr =>
        obtain ⟨v, t'⟩ := pr
        exact ⟨rfl, Or.inl rfl⟩
    rintro t₁ t₂ (rfl | ⟨a', s', h', rfl, rfl⟩)
    · exact bisim_refl _
    · -- Show: destruct ((cons a' s').filter p) = destruct (s'.filter p),
      -- then BisimO follows by reflexivity.
      suffices h_de : destruct ((cons a' s').filter p) = destruct (s'.filter p) by
        rw [h_de]; exact bisim_refl _
      unfold filter
      rw [corec_eq, corec_eq]
      -- Goal: omap _ (body (cons a' s')) = omap _ (body s')
      congr 1
      -- Goal: body (cons a' s') = body s', by case analysis.
      by_cases h_s_ex : ∃ m, ∃ a'', s'.get? m = some a'' ∧ p a''
      · -- Case A: `s'` has a `p`-satisfying element.
        have h_cons_ex : ∃ n, ∃ a'', (cons a' s').get? n = some a'' ∧ p a'' := by
          obtain ⟨m, a'', h_get, h_p⟩ := h_s_ex
          exact ⟨m + 1, a'', by simp [h_get], h_p⟩
        -- `Nat.find h_cons_ex = Nat.find h_s_ex + 1`.
        have h_find_eq : Nat.find h_cons_ex = Nat.find h_s_ex + 1 := by
          apply le_antisymm
          · apply Nat.find_min' h_cons_ex
            obtain ⟨a'', h_get, h_p⟩ := Nat.find_spec h_s_ex
            exact ⟨a'', by simp [h_get], h_p⟩
          · -- Extract a witness `a''` at `Nat.find h_cons_ex` in `cons a' s'`,
            -- then split that position as `m + 1` (it's positive since `¬ p a'`).
            obtain ⟨a'', h_get, h_p⟩ := Nat.find_spec h_cons_ex
            -- `Nat.find h_cons_ex ≥ 1`.
            have h_pos : 1 ≤ Nat.find h_cons_ex := by
              rcases Nat.eq_zero_or_pos (Nat.find h_cons_ex) with h_zero | h_pos
              · exfalso
                rw [h_zero] at h_get
                have h_eq : a' = a'' := by simpa using h_get
                subst h_eq
                exact h' h_p
              · exact h_pos
            obtain ⟨m, hm⟩ : ∃ m, Nat.find h_cons_ex = m + 1 :=
              Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp h_pos)
            rw [hm]
            apply Nat.succ_le_succ
            apply Nat.find_min' h_s_ex
            rw [hm] at h_get
            exact ⟨a'', by simpa using h_get, h_p⟩
        change (if h : ∃ n, ∃ a'', (cons a' s').get? n = some a'' ∧ p a'' then
                  some ((Nat.find_spec h).choose, (cons a' s').drop (Nat.find h + 1))
                else none) =
               (if h : ∃ n, ∃ a'', s'.get? n = some a'' ∧ p a'' then
                  some ((Nat.find_spec h).choose, s'.drop (Nat.find h + 1))
                else none)
        rw [dif_pos h_cons_ex, dif_pos h_s_ex]
        -- Drop equality.
        have h_drop_eq : (cons a' s').drop (Nat.find h_cons_ex + 1) =
            s'.drop (Nat.find h_s_ex + 1) := by
          rw [h_find_eq]
          exact drop_cons_succ a' s' (Nat.find h_s_ex + 1)
        -- Choose equality.
        have h_choose_eq : (Nat.find_spec h_cons_ex).choose =
            (Nat.find_spec h_s_ex).choose := by
          have h_cons_at_succ : (cons a' s').get? (Nat.find h_s_ex + 1) =
              some (Nat.find_spec h_cons_ex).choose := by
            rw [← h_find_eq]; exact (Nat.find_spec h_cons_ex).choose_spec.1
          have h_shift : (cons a' s').get? (Nat.find h_s_ex + 1) =
              s'.get? (Nat.find h_s_ex) := by simp
          have h_s_via : s'.get? (Nat.find h_s_ex) =
              some (Nat.find_spec h_cons_ex).choose := h_shift ▸ h_cons_at_succ
          have h_s_get : s'.get? (Nat.find h_s_ex) =
              some (Nat.find_spec h_s_ex).choose :=
            (Nat.find_spec h_s_ex).choose_spec.1
          exact Option.some_inj.mp (h_s_via.symm.trans h_s_get)
        rw [h_choose_eq, h_drop_eq]
      · -- Case B: neither `s'` nor `cons a' s'` has a `p`-satisfying element.
        have h_cons_neg :
            ¬ ∃ n, ∃ a'', (cons a' s').get? n = some a'' ∧ p a'' := by
          rintro ⟨n, a'', h_get, h_p⟩
          cases n with
          | zero =>
            have h_eq : a' = a'' := by simpa using h_get
            subst h_eq
            exact h' h_p
          | succ k =>
            exact h_s_ex ⟨k, a'', by simpa using h_get, h_p⟩
        change (if h : ∃ n, ∃ a'', (cons a' s').get? n = some a'' ∧ p a'' then
                  some ((Nat.find_spec h).choose, (cons a' s').drop (Nat.find h + 1))
                else none) =
               (if h : ∃ n, ∃ a'', s'.get? n = some a'' ∧ p a'' then
                  some ((Nat.find_spec h).choose, s'.drop (Nat.find h + 1))
                else none)
        rw [dif_neg h_cons_neg, dif_neg h_s_ex]
  · right
    exact ⟨a, s, h, rfl, rfl⟩

end Stream'.Seq

namespace PLTS

variable {α β State State_C State_A Label : Type}

/-- Lifting of a state relation `R : α → β → Prop` to a relation on PMFs.
`PMFRel R μ₁ μ₂` holds iff there is a joint PMF `ω` on `α × β` whose first
marginal is `μ₁`, second marginal is `μ₂`, and whose support is contained
in `R`. -/
def PMFRel (R : α → β → Prop) (μ₁ : PMF α) (μ₂ : PMF β) : Prop :=
  ∃ ω : PMF (α × β),
    PMF.map Prod.fst ω = μ₁ ∧
    PMF.map Prod.snd ω = μ₂ ∧
    ∀ p ∈ ω.support, R p.1 p.2

/-- A *strong* probabilistic forward simulation from `sys_C` to `sys_A` along
the state relation `R : State_C → State_A → Prop`:

* `init`: every initial concrete state is matched by some initial abstract
  state with which it is `R`-related;
* `step`: every concrete transition `s_C -[l]→ μ_C` from an `R`-related pair
  `(s_C, s_A)` can be matched by an abstract *strong* transition
  `s_A -[l]→ μ_A` such that `μ_C` and `μ_A` are related by the PMF-lifting of
  `R`. -/
structure StrongProbabilisticSimulation
    (sys_C : System State_C Label) (sys_A : System State_A Label)
    (R : State_C → State_A → Prop) where
  init : ∀ s_C, sys_C.init s_C → ∃ s_A, sys_A.init s_A ∧ R s_C s_A
  step : ∀ s_C s_A, R s_C s_A →
    ∀ l μ_C, sys_C.step s_C l μ_C →
    ∃ μ_A, sys_A.step s_A l μ_A ∧ PMFRel R μ_C μ_A

/-! ### Internal/external labels and weak transitions -/

/-- A system together with a partition of its labels into internal (silent)
and external (observable) labels: `ls.internal l` says that `l` is internal,
and external labels are exactly the labels `l` with `¬ ls.internal l`. -/
structure LabelledSystem (State Label : Type) extends System State Label where
  internal : Label → Prop

/-- A weak scheduler for a labelled system. It may stop (`none` in its output
PMF), only schedules internal labels (`internal_only`), only proposes valid
system steps (`valid`), and is forced to stop on every prefix of length at
least `runtime` (`stops`). -/
structure WeakScheduler (sys : LabelledSystem State Label) where
  next : AlterSeq State Label → PMF (Option (Label × PMF State))
  internal_only : ∀ (e : AlterSeq State Label) (lμ : Label × PMF State),
    some lμ ∈ (next e).support → sys.internal lμ.1
  valid : ∀ (e : AlterSeq State Label) (n : ℕ) (s : State),
    e.trans.TerminatedAt n → e.stateAt n = some s →
    ∀ lμ, some lμ ∈ (next e).support → sys.step s lμ.1 lμ.2
  runtime : ℕ
  stops : ∀ (e : AlterSeq State Label) (h : e.trans.Terminates),
    e.trans.length h ≥ runtime → next e = PMF.pure none

namespace WeakScheduler

variable {sys : LabelledSystem State Label}

/-- Run the weak scheduler from a prefix `e` with current state `s`, for `n`
iterations. After `n` recursions (or upon hitting a `none` output) the result
is the Dirac on the current state. -/
noncomputable def runFromState (σ : WeakScheduler sys) :
    ℕ → AlterSeq State Label → State → PMF State
  | 0,     _, s => PMF.pure s
  | n + 1, e, s => (σ.next e).bind fun
    | none           => PMF.pure s
    | some (l, μ_q) => μ_q.bind fun s' =>
        σ.runFromState n ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s'

/-- Run the weak scheduler from a single state `s` for `σ.runtime` iterations,
starting from the trivial prefix `⟨s, Seq.nil⟩`. -/
noncomputable def run (σ : WeakScheduler sys) (s : State) : PMF State :=
  σ.runFromState σ.runtime ⟨s, Seq.nil⟩ s

/-- The weak scheduler that immediately stops on every prefix. Used to witness
reflexivity of weak transitions: it takes no τ-steps, so its run from any state
`s` is the Dirac `PMF.pure s`. -/
noncomputable def stop (sys : LabelledSystem State Label) : WeakScheduler sys where
  next _ := PMF.pure none
  internal_only e lμ h := by simp at h
  valid e n s _ _ lμ h := by simp at h
  runtime := 0
  stops _ _ _ := rfl

@[simp] theorem run_stop (sys : LabelledSystem State Label) (s : State) :
    (stop sys).run s = PMF.pure s := rfl

end WeakScheduler

/-- Weak (internal) transition `μ_init ⇒^τ μ` on initial distributions: there
exists a weak scheduler whose run, sampled over starting states from `μ_init`,
produces the distribution `μ`. The "from a single state" case is recovered as
`weakTau sys (PMF.pure s) μ`. -/
def weakTau (sys : LabelledSystem State Label)
    (μ_init : PMF State) (μ : PMF State) : Prop :=
  ∃ σ : WeakScheduler sys, μ_init.bind σ.run = μ

/-- Reflexivity of `weakTau`: every distribution is weak-τ-related to itself,
witnessed by the stop-everywhere weak scheduler. -/
theorem weakTau_refl (ls : LabelledSystem State Label) (μ : PMF State) :
    weakTau ls μ μ := by
  refine ⟨WeakScheduler.stop ls, ?_⟩
  show μ.bind _ = μ
  have heq : (WeakScheduler.stop ls).run = PMF.pure := funext fun _ => rfl
  rw [heq]
  exact PMF.bind_pure μ

/-- The lifting of `sys.step` from `State → Label → PMF State → Prop` to a
relation on initial and final distributions, parameterised by a label, *closed
under convex combinations* of valid system steps.

`hyperStep sys μ_pre l μ_post` holds iff there is an assignment
`p : State → PMF (PMF State)` choosing, for every starting state, a
randomised mixture of valid successor distributions, such that

* every starting state `s ∈ μ_pre.support` has every distribution `μ` in the
  support of `p s` satisfying `sys.step s l μ`, and
* `μ_post` is the resulting bind:
  `μ_post = μ_pre.bind (fun s => (p s).bind id)`.

This is the natural lifting of a strong system step to *hyper-transitions* on
distributions. Allowing `p s` to be a `PMF (PMF State)` (rather than a single
`PMF State`) makes the relation closed under convex combinations of hyper-steps:
given two witnesses `p₁, p₂` producing `μ_post₁, μ_post₂`, any
`α • μ_post₁ + (1-α) • μ_post₂` is witnessed by `α • p₁ s + (1-α) • p₂ s` at
each state, using linearity of `PMF.bind`. In the singleton case
`μ_pre = PMF.pure s` it reduces to: `μ_post` is in the convex hull of
`{μ | sys.step s l μ}`. -/
def hyperStep (sys : System State Label)
    (μ_pre : PMF State) (l : Label) (μ_post : PMF State) : Prop :=
  ∃ p : State → PMF (PMF State),
    (∀ s ∈ μ_pre.support, ∀ μ ∈ (p s).support, sys.step s l μ) ∧
    μ_post = μ_pre.bind (fun s => (p s).bind id)

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
def weakStep (sys : LabelledSystem State Label)
    (μ_init : PMF State) (l : Label) (μ_final : PMF State) : Prop :=
  ∃ μ μ' : PMF State,
    weakTau sys μ_init μ ∧
    hyperStep sys.toSystem μ l μ' ∧
    weakTau sys μ' μ_final

/-- A strong system step lifts to a weak step on a singleton initial
distribution: if `sys.step s l μ`, then `weakStep sys (PMF.pure s) l μ`. Both
τ-closure layers are trivial reflexivities. -/
theorem weakStep_strong {ls : LabelledSystem State Label}
    {s : State} {l : Label} {μ : PMF State}
    (h_step : ls.step s l μ) :
    weakStep ls (PMF.pure s) l μ :=
  ⟨PMF.pure s, μ, weakTau_refl ls (PMF.pure s),
    hyperStep_pure_of_step h_step, weakTau_refl ls μ⟩

/-- A *weak* probabilistic forward simulation from `sys_C` to `sys_A` along the
state relation `R : State_C → State_A → Prop`. Both systems carry an
internal/external label partition.

* `init`: every initial concrete state is matched by some initial abstract
  state with which it is `R`-related;
* `step`: every concrete transition `s_C -[l]→ μ_C` from an `R`-related pair
  `(s_C, s_A)` is matched on the abstract side by:
  - a `weakTau` (a τ-closure from `PMF.pure s_A`) when `l` is *internal* in
    `sys_C` — the concrete invisible step is matched by zero-or-more invisible
    abstract steps;
  - a `weakStep` with the same label `l` from `PMF.pure s_A` when `l` is
    *external* in `sys_C` — the concrete visible step is matched by
    τ-closure + one strong `l`-step + τ-closure on the abstract side;

  in both cases the resulting abstract distribution `μ_A` must be related to
  `μ_C` by `PMFRel R`. -/
structure WeakProbabilisticSimulation
    (sys_C : LabelledSystem State_C Label) (sys_A : LabelledSystem State_A Label)
    (R : State_C → State_A → Prop) where
  init : ∀ s_C, sys_C.init s_C → ∃ s_A, sys_A.init s_A ∧ R s_C s_A
  step : ∀ s_C s_A, R s_C s_A →
    ∀ l μ_C, sys_C.step s_C l μ_C →
    ∃ μ_A : PMF State_A,
      ((sys_C.internal l ∧ weakTau sys_A (PMF.pure s_A) μ_A) ∨
       (¬ sys_C.internal l ∧ weakStep sys_A (PMF.pure s_A) l μ_A)) ∧
      PMFRel R μ_C μ_A

/-- A *probabilistic* forward simulation from `sys_C` to `sys_A`, parameterised
by a relation `R : State_C → PMF State_A → Prop` linking each concrete state to
a *distribution* over abstract states (rather than to a single abstract state
as in `WeakProbabilisticSimulation`).

* `init`: every initial concrete state is matched by some abstract distribution
  supported on initial abstract states;
* `step`: from an `R`-related pair `(s_C, μ_A)` with `μ_A : PMF State_A`, every
  concrete transition `s_C -[l]→ μ_C` is matched on the abstract side by a
  weak transition from `μ_A` to `ω.bind id`, where `ω : PMF (PMF State_A)` is
  a coupling of `μ_C` with `R`-related abstract distributions (i.e.
  `PMFRel R μ_C ω`). The choice between `weakTau` and `weakStep` depends, as
  in `WeakProbabilisticSimulation`, on whether `l` is internal in `sys_C`.

Modulo the typing of `R` (`State_C → PMF State_A → Prop` here vs.
`State_C → State_A → Prop` there), the matching pattern is exactly the same as
in `WeakProbabilisticSimulation`: `PMFRel R` couples the concrete outcome with
the abstract outcome, and the case split on `sys_C.internal l` picks between
the τ-only and the external weak transition. The notion is equivalent to
`WeakProbabilisticSimulation` (the latter is the special case where each `μ_A`
is concentrated on a single abstract state). -/
structure ProbabilisticForwardSimulation
    (sys_C : LabelledSystem State_C Label) (sys_A : LabelledSystem State_A Label)
    (R : State_C → PMF State_A → Prop) where
  init : ∀ s_C, sys_C.init s_C →
    ∃ μ_A, (∀ s_A ∈ μ_A.support, sys_A.init s_A) ∧ R s_C μ_A
  step : ∀ s_C μ_A, R s_C μ_A →
    ∀ l μ_C, sys_C.step s_C l μ_C →
    ∃ ω : PMF (PMF State_A),
      PMFRel R μ_C ω ∧
      ((sys_C.internal l ∧ weakTau sys_A μ_A (ω.bind id)) ∨
       (¬ sys_C.internal l ∧ weakStep sys_A μ_A l (ω.bind id)))

/-! ### Traces -/

/-- The trace of a (possibly infinite) execution `e` under a labelled system
`ls`: the sequence of external labels appearing in `e.trans`, in order, with
internal (τ) labels dropped. Finite if `e` has finitely many external
transitions, infinite otherwise. -/
noncomputable def LabelledSystem.trace (ls : LabelledSystem State Label)
    (e : AlterSeq State Label) : Seq Label :=
  (e.trans.filter (fun p => ¬ ls.internal p.1)).map Prod.fst

/-- The trace of an execution with no transitions is the empty sequence. -/
@[simp] theorem LabelledSystem.trace_init
    (ls : LabelledSystem State Label) (s : State) :
    ls.trace ⟨s, (Seq.nil : Seq (Label × State))⟩ = (Seq.nil : Seq Label) := by
  simp [LabelledSystem.trace]

/-- The trace of an execution whose first transition has an *external* label
`l` starts with `l`, followed by the trace from the rest of the execution. -/
@[simp] theorem LabelledSystem.trace_cons_external
    (ls : LabelledSystem State Label) (s : State) (l : Label) (s' : State)
    (rest : Seq (Label × State)) (h : ¬ ls.internal l) :
    ls.trace ⟨s, Seq.cons (l, s') rest⟩ = Seq.cons l (ls.trace ⟨s', rest⟩) := by
  unfold LabelledSystem.trace
  rw [Seq.filter_cons_pos (l, s') rest h, Seq.map_cons]

/-- The trace of an execution whose first transition has an *internal* label
`l` equals the trace from the rest of the execution (the internal label is
dropped). -/
@[simp] theorem LabelledSystem.trace_cons_internal
    (ls : LabelledSystem State Label) (s : State) (l : Label) (s' : State)
    (rest : Seq (Label × State)) (h : ls.internal l) :
    ls.trace ⟨s, Seq.cons (l, s') rest⟩ = ls.trace ⟨s', rest⟩ := by
  unfold LabelledSystem.trace
  rw [Seq.filter_cons_neg (l, s') rest (fun h' => h' h)]

/-- The probability that the probabilistic execution `pe` produces a finite
execution whose trace under `ls` equals `τ`: the (countable) sum of
`pe.probOf` over all finite executions `e` with `ls.trace e = τ`.

For finite `τ` this is the standard trace probability. For infinite `τ` the
sum is `0` since no finite execution can produce an infinite trace; capturing
infinite-trace probabilities would require moving to a measure-theoretic
setting on the σ-algebra generated by trace cones. -/
noncomputable def LabelledSystem.traceProb (ls : LabelledSystem State Label)
    (pe : ProbabilisticExecution ls.toSystem) (τ : Seq Label) : ENNReal :=
  ∑' e : {e : AlterSeq State Label // e.trans.Terminates ∧ ls.trace e = τ},
    pe.probOf e.1 e.2.1

/-! ### Trace coupling and Segala's trace inclusion theorem -/

/-- Two probabilistic executions over labelled systems are *trace-coupled* if
they assign equal probability to every finite trace. -/
def TraceCoupled
    (sys_C : LabelledSystem State_C Label) (sys_A : LabelledSystem State_A Label)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (pe_A : ProbabilisticExecution sys_A.toSystem) : Prop :=
  ∀ τ : Seq Label, sys_C.traceProb pe_C τ = sys_A.traceProb pe_A τ

/-- Reflexivity of `TraceCoupled`. -/
theorem TraceCoupled.refl (ls : LabelledSystem State Label)
    (pe : ProbabilisticExecution ls.toSystem) :
    TraceCoupled ls ls pe pe := fun _ => rfl

/-- Symmetry of `TraceCoupled` (across systems). -/
theorem TraceCoupled.symm {ls₁ : LabelledSystem State Label}
    {ls₂ : LabelledSystem State_A Label}
    {pe₁ : ProbabilisticExecution ls₁.toSystem}
    {pe₂ : ProbabilisticExecution ls₂.toSystem}
    (h : TraceCoupled ls₁ ls₂ pe₁ pe₂) : TraceCoupled ls₂ ls₁ pe₂ pe₁ :=
  fun τ => (h τ).symm

/-- Transitivity of `TraceCoupled` (across systems). -/
theorem TraceCoupled.trans {ls₁ : LabelledSystem State Label}
    {ls₂ : LabelledSystem State_A Label} {ls₃ : LabelledSystem State_C Label}
    {pe₁ : ProbabilisticExecution ls₁.toSystem}
    {pe₂ : ProbabilisticExecution ls₂.toSystem}
    {pe₃ : ProbabilisticExecution ls₃.toSystem}
    (h₁₂ : TraceCoupled ls₁ ls₂ pe₁ pe₂)
    (h₂₃ : TraceCoupled ls₂ ls₃ pe₂ pe₃) :
    TraceCoupled ls₁ ls₃ pe₁ pe₃ :=
  fun τ => (h₁₂ τ).trans (h₂₃ τ)

/-- **Inductive reduction lemma**: `TraceCoupled` is determined by its
behaviour on the empty trace and on cons-extensions. Any inductive proof of
`TraceCoupled` can split into a `nil` case plus a `cons` case via this lemma. -/
theorem TraceCoupled.of_nil_and_cons
    {sys_C : LabelledSystem State_C Label} {sys_A : LabelledSystem State_A Label}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {pe_A : ProbabilisticExecution sys_A.toSystem}
    (h_nil : sys_C.traceProb pe_C Seq.nil = sys_A.traceProb pe_A Seq.nil)
    (h_cons : ∀ (l : Label) (τ : Seq Label),
      sys_C.traceProb pe_C (Seq.cons l τ) = sys_A.traceProb pe_A (Seq.cons l τ)) :
    TraceCoupled sys_C sys_A pe_C pe_A := by
  intro τ
  cases τ with
  | nil => exact h_nil
  | cons l τ' => exact h_cons l τ'

/-- The trace probability of any trace is at most `1`. Proof requires
summing over finite executions and bounding by `pe.init`'s mass, plus
arguing that the conditional probabilities along the kernel sum to `≤ 1`
at each step. (Currently unproved — needed for Session C's quantitative
arguments.) -/
theorem LabelledSystem.traceProb_le_one
    (ls : LabelledSystem State Label)
    (pe : ProbabilisticExecution ls.toSystem) (τ : Seq Label) :
    ls.traceProb pe τ ≤ 1 := by
  sorry

/-- A *coupling* extending a concrete probabilistic execution along a
probabilistic forward simulation: an abstract probabilistic execution whose
init is supported on `sys_A`-initial states and which is trace-coupled to the
concrete one. This is the data produced by Segala's trace-inclusion
construction. -/
structure Coupling
    {sys_C : LabelledSystem State_C Label} {sys_A : LabelledSystem State_A Label}
    {R : State_C → PMF State_A → Prop}
    (_sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem) where
  /-- The abstract probabilistic execution paired with `pe_C`. -/
  pe_A : ProbabilisticExecution sys_A.toSystem
  /-- The abstract initial distribution is supported on `sys_A`-initial states. -/
  init_initial : ∀ s_A ∈ pe_A.init.support, sys_A.init s_A
  /-- The two executions assign equal probability to every finite trace. -/
  trace_coupled : TraceCoupled sys_C sys_A pe_C pe_A

/-- **Coupling existence (heart of Segala's theorem)**: every probabilistic
forward simulation extends a `sys_C`-rooted concrete probabilistic execution
to a trace-coupled abstract one. This is the main content; `traceInclusion`
follows by projecting the `pe_A` out of a `Coupling`.

Proof strategy (Session B + Session C, not yet formalised):
* **Session B (construction)**: build `pe_A` by composing `pe_C` with `sim`.
  - `pe_A.init` is `pe_C.init.bind init_match` where `init_match` is built from
    `sim.init` via `Classical.choose` (STEP 1, done in `traceInclusion`).
  - `pe_A.scheduler` is constructed step-by-step. At each abstract prefix `e_A`,
    `σ_A.next e_A` is determined by:
    * identifying the "concrete trajectory class" matching `e_A`
      (via `Classical.choose` on the trajectories whose `obs`-projection
      yields the same trace as `e_A`);
    * applying `pe_C.scheduler` at a representative concrete prefix to get the
      next concrete step `(l, μ_C)`;
    * using `sim.step` to derive a weak abstract transition matching `(l, μ_C)`;
    * extracting the *current* abstract step of the weak transition (the
      transition spans multiple abstract steps; `e_A` records which one we're
      on, so we can pick the right one).
  - Validity of `σ_A` (every step in support is a valid `sys_A.step`) follows
    from `sim.step`'s conclusions about `sys_A.step` inside the `hyperStep`
    and `weakTau` components of `weakStep`/`weakTau`.
* **Session C (trace equality)**: prove `TraceCoupled` by induction on
  trace length, using `PMFRel`-coupling preservation at each step and the
  fact that the `internal` half of the case split contributes nothing to
  the external trace. -/
theorem ProbabilisticForwardSimulation.exists_coupling
    {sys_C : LabelledSystem State_C Label} {sys_A : LabelledSystem State_A Label}
    {R : State_C → PMF State_A → Prop}
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (h_init : ∀ s_C ∈ pe_C.init.support, sys_C.init s_C) :
    Nonempty (Coupling sim pe_C) := by
  -- STEP 0: `Nonempty State_A` (extract a witness from `sim.init` applied to
  -- any element of `pe_C.init.support`).
  haveI hne_A : Nonempty State_A := by
    obtain ⟨s_C₀, h_s_C₀⟩ := pe_C.init.support_nonempty
    obtain ⟨μ_A, _, _⟩ := sim.init s_C₀ (h_init s_C₀ h_s_C₀)
    obtain ⟨s_A, _⟩ := μ_A.support_nonempty
    exact ⟨s_A⟩
  -- STEP 1: Build the initial-distribution matching function.
  obtain ⟨init_match, h_match_R, h_match_init⟩ :
      ∃ f : State_C → PMF State_A,
        (∀ s_C ∈ pe_C.init.support, R s_C (f s_C)) ∧
        (∀ s_C ∈ pe_C.init.support, ∀ s_A ∈ (f s_C).support, sys_A.init s_A) := by
    classical
    refine ⟨fun s_C =>
      if h : sys_C.init s_C then (sim.init s_C h).choose
      else PMF.pure (Classical.arbitrary _), ?_, ?_⟩
    · intro s_C h_s_C
      have h := h_init s_C h_s_C
      dsimp only
      rw [dif_pos h]
      exact (sim.init s_C h).choose_spec.2
    · intro s_C h_s_C s_A h_s_A
      have h := h_init s_C h_s_C
      dsimp only at h_s_A
      rw [dif_pos h] at h_s_A
      exact (sim.init s_C h).choose_spec.1 s_A h_s_A
  -- STEP 2: `pe_A.init`.
  let pe_A_init : PMF State_A := pe_C.init.bind init_match
  -- STEP 3 (sorry — the core scheduler construction + trace-equality proof):
  -- build `σ_A : Scheduler sys_A.toSystem` such that the resulting
  -- `⟨pe_A_init, σ_A⟩` is trace-coupled to `pe_C`.
  obtain ⟨pe_A_scheduler, h_traces⟩ :
      ∃ σ_A : Scheduler sys_A.toSystem,
        TraceCoupled sys_C sys_A pe_C ⟨pe_A_init, σ_A⟩ := by
    sorry
  -- Assemble the `Coupling`.
  refine ⟨{
    pe_A := ⟨pe_A_init, pe_A_scheduler⟩
    init_initial := ?_
    trace_coupled := h_traces
  }⟩
  intro s_A h_s_A
  rw [PMF.mem_support_bind_iff] at h_s_A
  obtain ⟨s_C, h_s_C, h_s_A_in⟩ := h_s_A
  exact h_match_init s_C h_s_C s_A h_s_A_in

/-- **Segala's main theorem (trace inclusion)**: if `R` is a probabilistic
forward simulation from `sys_C` to `sys_A`, then every concrete probabilistic
execution `pe_C` starting from initial states of `sys_C` is matched, trace by
trace, by some abstract probabilistic execution `pe_A` over `sys_A`.

Informally: the simulation suffices to transport the entire trace distribution
of any concrete adversary to a matching abstract adversary.

This is now an immediate corollary of `exists_coupling` — projecting the
`pe_A` field of a `Coupling` and using its `trace_coupled` witness.

Compared to Segala's original statement, ours is restricted to finite-runtime
schedulers on the abstract side (our `weakTau` is finite-bounded, whereas
Segala admits AS-terminating ones). The conclusion is consequently stated on
finite-trace `traceProb`; the infinite-trace measure-theoretic version awaits
a later upgrade to `MeasureTheory.Measure`. -/
theorem traceInclusion
    {sys_C : LabelledSystem State_C Label} {sys_A : LabelledSystem State_A Label}
    {R : State_C → PMF State_A → Prop}
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (h_init : ∀ s_C ∈ pe_C.init.support, sys_C.init s_C) :
    ∃ pe_A : ProbabilisticExecution sys_A.toSystem,
      ∀ τ : Seq Label, sys_C.traceProb pe_C τ = sys_A.traceProb pe_A τ := by
  obtain ⟨c⟩ := sim.exists_coupling pe_C h_init
  exact ⟨c.pe_A, c.trace_coupled⟩

end PLTS
