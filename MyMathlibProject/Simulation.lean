/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Basic
import Mathlib.Data.Seq.Basic

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

/-- `toList` of an `append` is the list-level concatenation of the two
constituent `toList`s. -/
theorem toList_append {α : Type*} (s s' : Seq α) (h_s : s.Terminates)
    (h_s' : s'.Terminates) (h_combined : (s.append s').Terminates) :
    (s.append s').toList h_combined = s.toList h_s ++ s'.toList h_s' := by
  -- Induct on s.length h_s, with s, h_s, h_combined universally quantified.
  suffices h_aux : ∀ (n : ℕ) (s : Seq α) (h_s : s.Terminates),
      s.length h_s = n → ∀ (h_combined : (s.append s').Terminates),
      (s.append s').toList h_combined = s.toList h_s ++ s'.toList h_s' from
    h_aux (s.length h_s) s h_s rfl h_combined
  intro n
  induction n with
  | zero =>
    intro s h_s h_len h_combined
    have h_s_nil : s = Seq.nil := length_eq_zero.mp h_len
    subst h_s_nil
    -- Goal: (nil.append s').toList h_combined = nil.toList h_s ++ s'.toList h_s'.
    -- nil.toList = []. (nil.append s') = s'. Goal reduces to s'.toList = s'.toList.
    have h_nil_toList : (Seq.nil : Seq α).toList h_s = [] := toList_nil
    rw [h_nil_toList, List.nil_append]
    -- Goal: (nil.append s').toList h_combined = s'.toList h_s'.
    -- Use proof irrelevance + nil_append.
    congr 1
    exact nil_append s'
  | succ n ih =>
    intro s h_s h_len h_combined
    have h_ne : s ≠ Seq.nil := by
      intro h_nil
      subst h_nil
      rw [length_nil] at h_len
      exact Nat.succ_ne_zero n h_len.symm
    cases s with
    | nil =>
      exact absurd rfl h_ne
    | cons a t =>
      have h_t_term : t.Terminates := terminates_tail_of_cons h_s
      have h_t_len : t.length h_t_term = n := by
        have : (cons a t).length h_s = t.length h_t_term + 1 := length_cons h_t_term
        rw [this] at h_len
        omega
      -- (cons a t).append s' = cons a (t.append s') (cons_append).
      have h_cons_app : (cons a t).append s' = cons a (t.append s') := cons_append a t s'
      -- Use this to compute both sides.
      -- LHS: (cons a t).append s'.toList h_combined.
      -- By proof irrelevance, this equals (cons a (t.append s')).toList h_combined'
      -- where h_combined' is the corresponding Terminates proof.
      have h_tail_combined : (t.append s').Terminates := by
        have : ((cons a t).append s').Terminates := h_combined
        rw [h_cons_app] at this
        exact terminates_tail_of_cons this
      have h_cons_tail_combined : (cons a (t.append s')).Terminates := by
        rw [← h_cons_app]; exact h_combined
      -- LHS: rewrite via the seq equality, then apply toList_cons.
      have h_LHS : ((cons a t).append s').toList h_combined =
          a :: (t.append s').toList h_tail_combined := by
        rw [show ((cons a t).append s').toList h_combined =
              (cons a (t.append s')).toList h_cons_tail_combined from by
          congr 1]
        exact toList_cons h_cons_tail_combined
      rw [h_LHS]
      rw [toList_cons h_s]
      rw [ih t h_t_term h_t_len h_tail_combined]
      rfl

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
  init : R sys_C.init sys_A.init
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

namespace weakTau

variable {sys : LabelledSystem State Label} {μ_init μ : PMF State}

/-- Classical extraction of the underlying `WeakScheduler` from a `weakTau`
proof. -/
noncomputable def witness (h : weakTau sys μ_init μ) : WeakScheduler sys :=
  h.choose

/-- The extracted scheduler, when run from `μ_init`, reaches `μ`. -/
theorem witness_run (h : weakTau sys μ_init μ) :
    μ_init.bind h.witness.run = μ :=
  h.choose_spec

end weakTau

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
def weakStep (sys : LabelledSystem State Label)
    (μ_init : PMF State) (l : Label) (μ_final : PMF State) : Prop :=
  ∃ μ μ' : PMF State,
    weakTau sys μ_init μ ∧
    hyperStep sys.toSystem μ l μ' ∧
    weakTau sys μ' μ_final

namespace weakStep

variable {sys : LabelledSystem State Label} {μ_init μ_final : PMF State} {l : Label}

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
    hyperStep sys.toSystem h.preDist l h.postDist :=
  h.choose_spec.choose_spec.2.1

/-- The τ-closure after the external step. -/
theorem weakTau_post (h : weakStep sys μ_init l μ_final) :
    weakTau sys h.postDist μ_final :=
  h.choose_spec.choose_spec.2.2

end weakStep

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
  init : R sys_C.init sys_A.init
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
  init : ∃ μ_A, (∀ s_A ∈ μ_A.support, s_A = sys_A.init) ∧ R sys_C.init μ_A
  step : ∀ s_C μ_A, R s_C μ_A →
    ∀ l μ_C, sys_C.step s_C l μ_C →
    ∃ ω : PMF (PMF State_A),
      PMFRel R μ_C ω ∧
      ((sys_C.internal l ∧ weakTau sys_A μ_A (ω.bind id)) ∨
       (¬ sys_C.internal l ∧ weakStep sys_A μ_A l (ω.bind id)))

namespace ProbabilisticForwardSimulation

variable {sys_C : LabelledSystem State_C Label} {sys_A : LabelledSystem State_A Label}
  {R : State_C → PMF State_A → Prop}

/-- The abstract distribution-over-distributions `ω` extracted from `sim.step`
at an R-related pair `(s_C, μ_A)` and a concrete step `s_C -[l]→ μ_C`. The
"flattened" version `(stepWitness …).bind id` is the abstract distribution
reached after simulating the concrete step. -/
noncomputable def stepWitness (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    {s_C : State_C} {μ_A : PMF State_A} (h_R : R s_C μ_A)
    {l : Label} {μ_C : PMF State_C} (h_step : sys_C.step s_C l μ_C) :
    PMF (PMF State_A) :=
  (sim.step s_C μ_A h_R l μ_C h_step).choose

/-- The `stepWitness` is `PMFRel`-coupled to the concrete next-state
distribution `μ_C`. -/
theorem stepWitness_pmfRel (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    {s_C : State_C} {μ_A : PMF State_A} (h_R : R s_C μ_A)
    {l : Label} {μ_C : PMF State_C} (h_step : sys_C.step s_C l μ_C) :
    PMFRel R μ_C (sim.stepWitness h_R h_step) :=
  (sim.step s_C μ_A h_R l μ_C h_step).choose_spec.1

/-- When the concrete label is internal, the abstract side reaches the
flattened `stepWitness` via a τ-closure. -/
theorem stepWitness_weakTau (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    {s_C : State_C} {μ_A : PMF State_A} (h_R : R s_C μ_A)
    {l : Label} {μ_C : PMF State_C} (h_step : sys_C.step s_C l μ_C)
    (h_int : sys_C.internal l) :
    weakTau sys_A μ_A ((sim.stepWitness h_R h_step).bind id) := by
  rcases (sim.step s_C μ_A h_R l μ_C h_step).choose_spec.2 with ⟨_, h_tau⟩ | ⟨h_ext, _⟩
  · exact h_tau
  · exact absurd h_int h_ext

/-- When the concrete label is external, the abstract side reaches the
flattened `stepWitness` via a weak step with the same label. -/
theorem stepWitness_weakStep (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    {s_C : State_C} {μ_A : PMF State_A} (h_R : R s_C μ_A)
    {l : Label} {μ_C : PMF State_C} (h_step : sys_C.step s_C l μ_C)
    (h_ext : ¬ sys_C.internal l) :
    weakStep sys_A μ_A l ((sim.stepWitness h_R h_step).bind id) := by
  rcases (sim.step s_C μ_A h_R l μ_C h_step).choose_spec.2 with ⟨h_int, _⟩ | ⟨_, h_step_w⟩
  · exact absurd h_int h_ext
  · exact h_step_w

end ProbabilisticForwardSimulation

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

/-- A finite execution is *trace-tight* under `ls` if either it has no
transitions, or its last transition is external. Tight executions correspond
to "trace cone boundaries": each trajectory has at most one tight prefix per
finite trace.

This rules out the artefact where a single trajectory contributes to the
trace probability *infinitely many times* via nested cylinders — a finite
prefix and any of its extensions by trailing internal transitions all have
the same trace, but only one of them (the shortest, ending right after the
last external transition or with no transitions at all) is tight. -/
def LabelledSystem.IsTight
    (ls : LabelledSystem State Label) (e : AlterSeq State Label) : Prop :=
  e.trans.TerminatedAt 0 ∨
  ∃ (n : ℕ) (l : Label) (s : State),
    e.trans.get? n = some (l, s) ∧
    e.trans.TerminatedAt (n + 1) ∧
    ¬ ls.internal l

/-- The probability that the probabilistic execution `pe` produces the finite
trace `τ` under `ls`: the (countable) sum of `pe.probOf` over all
*trace-tight* finite executions `e` with `ls.trace e = τ`.

The tightness condition (`IsTight`) ensures the summands correspond to
disjoint cylinders in the trace cone for `τ`: a trajectory contributes
exactly once via its unique tight prefix (the shortest prefix with trace `τ`,
ending right after the last external transition). Without tightness, internal
loops would cause double-counting — see the docstring of `IsTight` for the
artefact this prevents.

For finite `τ` this is the standard trace-cone probability (i.e. the
probability that the trajectory's first `|τ|` external labels are exactly
`τ`). For infinite `τ` the sum is `0` since no finite execution has an
infinite trace; capturing infinite-trace probabilities would require moving
to a measure-theoretic setting on the σ-algebra generated by trace cones. -/
noncomputable def LabelledSystem.traceProb (ls : LabelledSystem State Label)
    (pe : ProbabilisticExecution ls.toSystem) (τ : Seq Label) : ENNReal :=
  ∑' e : {e : AlterSeq State Label //
      e.trans.Terminates ∧ ls.trace e = τ ∧ ls.IsTight e},
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

/-- If `e.trans.get? n = some (l, s)` with `l` external, then `ls.trace e`
is non-empty: the external label at position `n` contributes to the trace.

Proved by induction on `n`. The base case (`n = 0`) decomposes
`e.trans = cons (l, s) e.trans.tail` via `Seq.head_eq_some`, then uses
`trace_cons_external` to expose the trace's `cons l _` head. The inductive
case (`n = k+1`) peels off the actual head transition: if its label is
external, the trace immediately starts with that label; if internal, the
trace equals the trace of the tail, to which IH applies. -/
private theorem trace_ne_nil_of_external_at
    (ls : LabelledSystem State Label) :
    ∀ (n : ℕ) (e : AlterSeq State Label) (l : Label) (s : State),
      e.trans.get? n = some (l, s) → ¬ ls.internal l →
      ls.trace e ≠ Seq.nil := by
  intro n
  induction n with
  | zero =>
    intro e l s h_get h_ext
    have h_cons : e.trans = Seq.cons (l, s) e.trans.tail :=
      Stream'.Seq.head_eq_some h_get
    have h_eq : ls.trace e = Seq.cons l (ls.trace ⟨s, e.trans.tail⟩) := by
      conv_lhs =>
        rw [show e = ⟨e.init, Seq.cons (l, s) e.trans.tail⟩ from by
          rcases e with ⟨init, trans⟩; congr]
      exact ls.trace_cons_external e.init l s e.trans.tail h_ext
    rw [h_eq]
    exact Stream'.Seq.cons_ne_nil
  | succ k ih =>
    intro e l s h_get h_ext
    -- `e.trans` is non-empty (position `k+1` is occupied), so it's
    -- `cons (l₀, s₀) tail` for some `(l₀, s₀)`.
    obtain ⟨⟨l₀, s₀⟩, h_get_0⟩ : ∃ a, e.trans.get? 0 = some a :=
      Stream'.Seq.ge_stable e.trans (Nat.zero_le _) h_get
    have h_cons : e.trans = Seq.cons (l₀, s₀) e.trans.tail :=
      Stream'.Seq.head_eq_some h_get_0
    have h_tail_get : e.trans.tail.get? k = some (l, s) := by
      rw [Stream'.Seq.get?_tail]; exact h_get
    by_cases h_int_0 : ls.internal l₀
    · -- Head transition internal: trace e = trace ⟨s₀, tail⟩. Apply IH.
      have h_trace_eq : ls.trace e = ls.trace ⟨s₀, e.trans.tail⟩ := by
        conv_lhs =>
          rw [show e = ⟨e.init, Seq.cons (l₀, s₀) e.trans.tail⟩ from by
            rcases e with ⟨init, trans⟩; congr]
        exact ls.trace_cons_internal e.init l₀ s₀ e.trans.tail h_int_0
      rw [h_trace_eq]
      exact ih ⟨s₀, e.trans.tail⟩ l s h_tail_get h_ext
    · -- Head transition external: trace e starts with l₀.
      have h_trace_eq : ls.trace e = Seq.cons l₀ (ls.trace ⟨s₀, e.trans.tail⟩) := by
        conv_lhs =>
          rw [show e = ⟨e.init, Seq.cons (l₀, s₀) e.trans.tail⟩ from by
            rcases e with ⟨init, trans⟩; congr]
        exact ls.trace_cons_external e.init l₀ s₀ e.trans.tail h_int_0
      rw [h_trace_eq]
      exact Stream'.Seq.cons_ne_nil

/-- Key algebraic fact: a tight prefix whose trace is empty has no
transitions. The first disjunct of `IsTight` (TerminatedAt 0) gives this
directly via `Seq.get?_zero_eq_none`; the second disjunct (external last
transition) contradicts trace nil via `trace_ne_nil_of_external_at`. -/
private theorem trans_nil_of_tight_trace_nil
    (ls : LabelledSystem State Label) (e : AlterSeq State Label)
    (h_trace : ls.trace e = Seq.nil) (h_tight : ls.IsTight e) :
    e.trans = Seq.nil := by
  rcases h_tight with h_term0 | ⟨n, l, s, h_get, _h_term_succ, h_ext⟩
  · exact Stream'.Seq.get?_zero_eq_none.mp h_term0
  · exact absurd h_trace (trace_ne_nil_of_external_at ls n e l s h_get h_ext)

/-- The trace probability of the empty trace is exactly `1`: every trajectory
trivially has `Seq.nil` as a prefix of its trace, so the trace cone for
`Seq.nil` is the whole space.

Concretely: under `IsTight`, only `⟨s, Seq.nil⟩` (the empty-trans prefixes,
one per `s : State`) have trace `Seq.nil` (`trans_nil_of_tight_trace_nil`).
Their `probOf` values are `pe.init s * 1 = pe.init s`, summing via
`Equiv.tsum_eq` and `PMF.tsum_coe` to `1`. -/
theorem LabelledSystem.traceProb_nil_eq_one
    (ls : LabelledSystem State Label)
    (pe : ProbabilisticExecution ls.toSystem) :
    ls.traceProb pe Seq.nil = 1 := by
  unfold LabelledSystem.traceProb
  -- Build the bijection {e // Terminates ∧ trace = nil ∧ IsTight} ≃ State.
  let e_equiv : {e : AlterSeq State Label //
      e.trans.Terminates ∧ ls.trace e = Seq.nil ∧ ls.IsTight e} ≃ State :=
    { toFun := fun e => e.1.init
      invFun := fun s =>
        ⟨⟨s, Seq.nil⟩,
          Stream'.Seq.terminates_nil,
          ls.trace_init s,
          Or.inl Stream'.Seq.terminatedAt_nil⟩
      left_inv := by
        rintro ⟨⟨init, trans⟩, hTerm, hTrace, hTight⟩
        have h_trans_nil : trans = Seq.nil :=
          trans_nil_of_tight_trace_nil ls ⟨init, trans⟩ hTrace hTight
        subst h_trans_nil
        rfl
      right_inv := fun _ => rfl }
  -- For each element of the subtype, `probOf = pe.init e.1.init`.
  have h_probOf : ∀ (a : {e : AlterSeq State Label //
      e.trans.Terminates ∧ ls.trace e = Seq.nil ∧ ls.IsTight e}),
      pe.probOf a.1 a.2.1 = pe.init a.1.init := by
    rintro ⟨⟨init, trans⟩, hTerm, hTrace, hTight⟩
    have h_trans_nil : trans = Seq.nil :=
      trans_nil_of_tight_trace_nil ls ⟨init, trans⟩ hTrace hTight
    subst h_trans_nil
    -- Goal: pe.probOf ⟨init, Seq.nil⟩ hTerm = pe.init init
    unfold ProbabilisticExecution.probOf
    -- toList of nil is [].
    change pe.init init * pe.probOfRemaining ⟨init, Seq.nil⟩
        ((Seq.nil : Seq (Label × State)).toList hTerm) = pe.init init
    have h_toList : (Seq.nil : Seq (Label × State)).toList hTerm = [] :=
      Stream'.Seq.toList_nil
    rw [h_toList]
    unfold ProbabilisticExecution.probOfRemaining
    simp
  -- Rewrite the tsum and conclude.
  rw [tsum_congr h_probOf]
  -- Goal: ∑' a : Subtype, pe.init a.1.init = 1
  rw [show
      (∑' a : {e : AlterSeq State Label //
          e.trans.Terminates ∧ ls.trace e = Seq.nil ∧ ls.IsTight e},
        pe.init a.1.init) = ∑' s, pe.init s from e_equiv.tsum_eq pe.init]
  exact pe.init.tsum_coe

/-- Local helper: `∑'` over a sum type decomposes into the two
sub-`tsum`s. Proved via `Equiv.sumEquivSigmaBool` + `ENNReal.tsum_sigma'`
+ `Fintype.sum_bool`. Should arguably live in Mathlib. -/
theorem tsum_sum_type {α β : Type u} (f : α ⊕ β → ENNReal) :
    ∑' x : α ⊕ β, f x = ∑' a, f (Sum.inl a) + ∑' b, f (Sum.inr b) := by
  rw [show (∑' x : α ⊕ β, f x) =
      ∑' s : Σ b : Bool, bif b then β else α,
        f ((Equiv.sumEquivSigmaBool α β).symm s) from
    ((Equiv.sumEquivSigmaBool α β).symm.tsum_eq f).symm]
  rw [ENNReal.tsum_sigma']
  rw [tsum_fintype]
  rw [Fintype.sum_bool]
  -- After Fintype.sum_bool: `true`-term + `false`-term. Swap to match RHS.
  exact add_comm _ _

/-- The `traceProb` of a `continuationFrom`-execution restricts to the
sub-subtype where `e.init = history.endState`: the other elements have
`probOf = 0` via `probOf_continuationFrom_zero_of_init_ne`.

Proof: `Equiv.sumCompl` splits the LHS subtype into "init = endState"
(B') and "init ≠ endState" (A_no). Apply `tsum_sum_type` to split the
sum. The A_no side is 0 (each summand is 0 via
`probOf_continuationFrom_zero_of_init_ne`). The B' side maps
bijectively to the desired init-constrained subtype. -/
theorem LabelledSystem.traceProb_continuationFrom_init_restrict
    (ls : LabelledSystem State Label) (pe : ProbabilisticExecution ls.toSystem)
    (history : AlterSeq State Label) (h_term : history.trans.Terminates)
    (τ : Seq Label) :
    ls.traceProb (pe.continuationFrom history h_term) τ =
      ∑' (e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ ls.trace e = τ ∧ ls.IsTight e ∧
          e.init = history.endState h_term}),
        (pe.continuationFrom history h_term).probOf e.1 e.2.1 := by
  classical
  unfold LabelledSystem.traceProb
  set A := {e : AlterSeq State Label //
    e.trans.Terminates ∧ ls.trace e = τ ∧ ls.IsTight e} with hA_def
  set p : A → Prop := fun a => a.1.init = history.endState h_term with hp_def
  -- Split A via Equiv.sumCompl p.
  rw [show
      (∑' (a : A), (pe.continuationFrom history h_term).probOf a.1 a.2.1) =
      ∑' (x : {a : A // p a} ⊕ {a : A // ¬ p a}),
        (pe.continuationFrom history h_term).probOf
          ((Equiv.sumCompl p) x).1 ((Equiv.sumCompl p) x).2.1 from
    ((Equiv.sumCompl p).tsum_eq _).symm]
  rw [tsum_sum_type]
  -- The right (A_no) summand is 0.
  have h_zero : (∑' (a : {a : A // ¬ p a}),
      (pe.continuationFrom history h_term).probOf
        ((Equiv.sumCompl p) (Sum.inr a)).1
        ((Equiv.sumCompl p) (Sum.inr a)).2.1) = 0 := by
    apply ENNReal.tsum_eq_zero.mpr
    rintro ⟨⟨e, h_term', h_trace', h_tight'⟩, h_ne⟩
    -- (Equiv.sumCompl p) (Sum.inr ⟨⟨e, …⟩, h_ne⟩) = ⟨e, …⟩.
    exact ProbabilisticExecution.probOf_continuationFrom_zero_of_init_ne
      pe history h_term e h_term' h_ne
  rw [h_zero, add_zero]
  -- The left (B') summand: bijection with the desired subtype.
  let e_B' : {a : A // p a} ≃ {e : AlterSeq State Label //
      e.trans.Terminates ∧ ls.trace e = τ ∧ ls.IsTight e ∧
      e.init = history.endState h_term} :=
    { toFun := fun ⟨⟨e, h_term', h_trace', h_tight'⟩, h_init'⟩ =>
        ⟨e, h_term', h_trace', h_tight', h_init'⟩
      invFun := fun ⟨e, h_term', h_trace', h_tight', h_init'⟩ =>
        ⟨⟨e, h_term', h_trace', h_tight'⟩, h_init'⟩
      left_inv := fun ⟨⟨_, _, _, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _, _⟩ => rfl }
  -- The LHS expression `probOf ((sumCompl p) (Sum.inl a)).1 …` reduces to
  -- `probOf a.1.1 a.1.2.1` since `sumCompl p` on `Sum.inl ⟨a, _⟩` is `a`.
  -- The Equiv `e_B'` rebrackets the constraint conjunction. After bridging
  -- via `tsum_congr`, apply `e_B'.tsum_eq`.
  refine (tsum_congr (fun a => ?_)).trans
    (e_B'.tsum_eq (fun e => (pe.continuationFrom history h_term).probOf e.1 e.2.1))
  rcases a with ⟨⟨e, _, _, _⟩, _⟩
  rfl

/-- "After the scheduler emits a transition with label `l₀`, the remaining
trace becomes…": internal labels drop out (trace unchanged); external labels
must match the next external label of `τ` and are consumed; an external
mismatch makes the continuation impossible (`none`). -/
noncomputable def LabelledSystem.consumeLabel (ls : LabelledSystem State Label)
    (l₀ : Label) (τ : Seq Label) : Option (Seq Label) := by
  classical
  exact
    if ls.internal l₀ then some τ
    else
      match τ.head with
      | some l => if l = l₀ then some τ.tail else none
      | none   => none

/-- `consumeLabel` on an internal label: returns the trace unchanged. -/
@[simp] theorem LabelledSystem.consumeLabel_internal
    (ls : LabelledSystem State Label) (l₀ : Label) (τ : Seq Label)
    (h : ls.internal l₀) : ls.consumeLabel l₀ τ = some τ := by
  unfold LabelledSystem.consumeLabel
  classical
  simp [h]

/-- `consumeLabel` on an external label matching the head of `Seq.cons l τ`:
returns `some τ`. -/
theorem LabelledSystem.consumeLabel_external_match
    (ls : LabelledSystem State Label) (l : Label) (τ : Seq Label)
    (h : ¬ ls.internal l) : ls.consumeLabel l (Seq.cons l τ) = some τ := by
  unfold LabelledSystem.consumeLabel
  classical
  simp [h, Stream'.Seq.head_cons, Stream'.Seq.tail_cons]

/-- `consumeLabel` on an external label *not* matching the head:
returns `none`. -/
theorem LabelledSystem.consumeLabel_external_no_match
    (ls : LabelledSystem State Label) (l₀ l : Label) (τ : Seq Label)
    (h_ext : ¬ ls.internal l₀) (h_ne : l ≠ l₀) :
    ls.consumeLabel l₀ (Seq.cons l τ) = none := by
  unfold LabelledSystem.consumeLabel
  classical
  simp [h_ext, Stream'.Seq.head_cons, h_ne]

/-- IsTight characterization for a prefix starting with `(l₀, s₁)` followed
by `e_rest_trans`: tight iff its tail-prefix is tight, with the extra
constraint that when the tail is empty, `l₀` must be external (since the
last transition of the full prefix is then `(l₀, s₁)` itself). -/
theorem LabelledSystem.IsTight_cons_iff (ls : LabelledSystem State Label)
    (s₀ : State) (l₀ : Label) (s₁ : State) (e_rest_trans : Seq (Label × State)) :
    ls.IsTight ⟨s₀, Seq.cons (l₀, s₁) e_rest_trans⟩ ↔
      ls.IsTight ⟨s₁, e_rest_trans⟩ ∧
        (¬ ls.internal l₀ ∨ e_rest_trans ≠ Seq.nil) := by
  constructor
  · rintro (h_term0 | ⟨n, l, s, h_get, h_term_succ, h_ext⟩)
    · exact absurd h_term0 Stream'.Seq.cons_not_terminatedAt_zero
    · refine ⟨?_, ?_⟩
      · rcases n with _ | n'
        · have h_e_rest_nil : e_rest_trans.TerminatedAt 0 := by
            rw [← Stream'.Seq.cons_terminatedAt_succ_iff (x := (l₀, s₁))]
            exact h_term_succ
          exact Or.inl h_e_rest_nil
        · refine Or.inr ⟨n', l, s, ?_, ?_, h_ext⟩
          · rw [← Stream'.Seq.get?_cons_succ (a := (l₀, s₁))]; exact h_get
          · rw [← Stream'.Seq.cons_terminatedAt_succ_iff (x := (l₀, s₁))]
            exact h_term_succ
      · rcases n with _ | n'
        · have h_pair_eq : l = l₀ := by
            have h_zero : (Seq.cons (l₀, s₁) e_rest_trans).get? 0 = some (l₀, s₁) := rfl
            rw [h_zero] at h_get
            exact ((Prod.mk.injEq _ _ _ _).mp (Option.some.inj h_get) |>.1).symm
          exact Or.inl (h_pair_eq ▸ h_ext)
        · refine Or.inr ?_
          intro h_nil
          rw [h_nil] at h_get
          have h_none : (Seq.cons (l₀, s₁) Seq.nil).get? (n' + 1) = none := by
            rw [Stream'.Seq.get?_cons_succ]; exact Stream'.Seq.terminatedAt_nil
          rw [h_none] at h_get
          exact absurd h_get (by simp)
  · rintro ⟨h_tight_rest, h_aux⟩
    rcases h_tight_rest with h_e_rest_nil | ⟨n', l, s, h_get', h_term_succ', h_ext'⟩
    · have h_e_rest_eq : e_rest_trans = Seq.nil :=
        Stream'.Seq.terminatedAt_zero_iff.mp h_e_rest_nil
      have h_not_internal : ¬ ls.internal l₀ :=
        h_aux.resolve_right (by intro h_ne; exact h_ne h_e_rest_eq)
      refine Or.inr ⟨0, l₀, s₁, ?_, ?_, h_not_internal⟩
      · rfl
      · change (Seq.cons (l₀, s₁) e_rest_trans).get? 1 = none
        rw [Stream'.Seq.get?_cons_succ]; rw [h_e_rest_eq]; exact Stream'.Seq.terminatedAt_nil
    · refine Or.inr ⟨n' + 1, l, s, ?_, ?_, h_ext'⟩
      · rw [Stream'.Seq.get?_cons_succ]; exact h_get'
      · rw [Stream'.Seq.cons_terminatedAt_succ_iff]; exact h_term_succ'

/-- **The trace-decomposition codomain** for `traceProb_first_step`'s
bijection: a triple `(s₀, l₀, s₁)` together with a constrained tail prefix
`e_rest` whose `init` is `s₁` and whose trace matches whatever
`consumeLabel l₀ (cons l τ)` produces.

The `consumeLabel … = some (ls.trace e_rest)` constraint encodes two
cases simultaneously:
* `l₀` internal: `ls.consumeLabel l₀ … = some (cons l τ)`, forcing
  `ls.trace e_rest = cons l τ`.
* `l₀` external with `l₀ = l`: `ls.consumeLabel = some τ`, forcing
  `ls.trace e_rest = τ`.
* `l₀` external with `l₀ ≠ l`: `ls.consumeLabel = none`, so the
  constraint `none = some (ls.trace e_rest)` is unsatisfiable — the
  subtype is empty for such `l₀`, matching the "0 contribution" branch
  of `consumeLabel.elim` on the RHS. -/
def LabelledSystem.TraceDecomp (ls : LabelledSystem State Label)
    (l : Label) (τ : Seq Label) : Type :=
  Σ' (_ : State) (l₀ : Label) (s₁ : State),
    {e_rest : AlterSeq State Label //
      e_rest.init = s₁ ∧
      e_rest.trans.Terminates ∧
      ls.IsTight e_rest ∧
      ls.consumeLabel l₀ (Seq.cons l τ) = some (ls.trace e_rest)}

/-- Forward map of the trace-decomposition bijection: decompose a tight
prefix with trace `cons l τ` into `(e.init, head label, head state, tail
prefix)`. Constraint translation uses `IsTight_cons_iff` and the
`trace_cons_*` lemmas. -/
noncomputable def LabelledSystem.TraceDecomp.ofTight
    (ls : LabelledSystem State Label) (l : Label) (τ : Seq Label)
    (e : AlterSeq State Label)
    (h_term : e.trans.Terminates) (h_trace : ls.trace e = Seq.cons l τ)
    (h_tight : ls.IsTight e) :
    ls.TraceDecomp l τ :=
  -- Trace is non-empty ⇒ `e.trans` is non-empty.
  have h_trans_ne_nil : e.trans ≠ Seq.nil := fun h_nil => by
    have h_trace_nil : ls.trace e = Seq.nil := by
      rcases e with ⟨init, _⟩; cases h_nil; exact ls.trace_init init
    rw [h_trace] at h_trace_nil
    exact Stream'.Seq.cons_ne_nil h_trace_nil
  have h_head_isSome : e.trans.head.isSome := by
    rcases h_eq : e.trans.head with _ | _
    · exact absurd (Stream'.Seq.terminatedAt_zero_iff.mp h_eq) h_trans_ne_nil
    · rfl
  -- The head pair `(l₀, s₁) = pair`.  Now a clean `let`-bound term.
  let pair : Label × State := e.trans.head.get h_head_isSome
  have h_cons : e.trans = Seq.cons pair e.trans.tail :=
    Stream'.Seq.head_eq_some (Option.eq_some_of_isSome _)
  ⟨e.init, pair.1, pair.2,
    ⟨⟨pair.2, e.trans.tail⟩,
      rfl,
      Stream'.Seq.terminates_tail_of_cons (h_cons ▸ h_term),
      ((ls.IsTight_cons_iff e.init pair.1 pair.2 e.trans.tail).mp (by
        rcases e with ⟨init, trans⟩
        simp only at h_cons
        rw [h_cons] at h_tight
        exact h_tight)).1,
      by
        classical
        by_cases h_int : ls.internal pair.1
        · -- Internal: consumeLabel = some (cons l τ); trace e_rest = cons l τ.
          have h_trace_rest : ls.trace ⟨pair.2, e.trans.tail⟩ = Seq.cons l τ := by
            rw [← h_trace]
            rcases e with ⟨init, trans⟩
            simp only at h_cons
            rw [h_cons]
            exact (ls.trace_cons_internal init pair.1 pair.2 trans.tail h_int).symm
          rw [h_trace_rest]
          change ls.consumeLabel pair.1 (Seq.cons l τ) = some (Seq.cons l τ)
          unfold LabelledSystem.consumeLabel
          simp [h_int]
        · -- External: `l = pair.1`, consumeLabel = some τ, trace e_rest = τ.
          have h_trace_full : ls.trace e =
              Seq.cons pair.1 (ls.trace ⟨pair.2, e.trans.tail⟩) := by
            rcases e with ⟨init, trans⟩
            simp only at h_cons ⊢
            rw [h_cons]
            exact ls.trace_cons_external init pair.1 pair.2 trans.tail h_int
          rw [h_trace] at h_trace_full
          have h_l_eq : l = pair.1 := ((Stream'.Seq.cons_eq_cons).mp h_trace_full).1
          have h_trace_rest_eq : ls.trace ⟨pair.2, e.trans.tail⟩ = τ :=
            ((Stream'.Seq.cons_eq_cons).mp h_trace_full).2.symm
          rw [h_trace_rest_eq]
          change ls.consumeLabel pair.1 (Seq.cons l τ) = some τ
          unfold LabelledSystem.consumeLabel
          simp only [if_neg h_int]
          change (if l = pair.1 then some (Seq.cons l τ).tail else none) = some τ
          rw [if_pos h_l_eq, Stream'.Seq.tail_cons]⟩⟩

/-- Inverse map of the trace-decomposition bijection: assemble a tight prefix
with trace `cons l τ` from its decomposed pieces. Constraint translation runs
in reverse of `ofTight`. -/
def LabelledSystem.TraceDecomp.toTight
    (ls : LabelledSystem State Label) (l : Label) (τ : Seq Label)
    (d : ls.TraceDecomp l τ) :
    {e : AlterSeq State Label //
      e.trans.Terminates ∧ ls.trace e = Seq.cons l τ ∧ ls.IsTight e} :=
  -- Projection-based to make iota reduction transparent.
  let s₀ := d.1
  let l₀ := d.2.1
  let s₁ := d.2.2.1
  let e_rest := d.2.2.2.1
  let h_init : e_rest.init = s₁ := d.2.2.2.2.1
  let h_term : e_rest.trans.Terminates := d.2.2.2.2.2.1
  let h_tight : ls.IsTight e_rest := d.2.2.2.2.2.2.1
  let h_consume : ls.consumeLabel l₀ (Seq.cons l τ) = some (ls.trace e_rest) :=
    d.2.2.2.2.2.2.2
  -- e_rest = ⟨s₁, e_rest.trans⟩ by h_init.
  have h_e_rest_eq : e_rest = ⟨s₁, e_rest.trans⟩ := by
    rw [← h_init]
  ⟨⟨s₀, Seq.cons (l₀, s₁) e_rest.trans⟩,
    Stream'.Seq.terminates_cons_iff.mpr h_term,
    (by
      classical
      by_cases h_int : ls.internal l₀
      · have h_consume_internal :
            ls.consumeLabel l₀ (Seq.cons l τ) = some (Seq.cons l τ) := by
          unfold LabelledSystem.consumeLabel; simp [h_int]
        rw [h_consume_internal] at h_consume
        have h_trace_e_rest : ls.trace e_rest = Seq.cons l τ :=
          (Option.some.inj h_consume).symm
        rw [ls.trace_cons_internal s₀ l₀ s₁ e_rest.trans h_int, ← h_e_rest_eq]
        exact h_trace_e_rest
      · have h_consume_external :
            ls.consumeLabel l₀ (Seq.cons l τ) = (if l = l₀ then some τ else none) := by
          unfold LabelledSystem.consumeLabel; simp [h_int]
        rw [h_consume_external] at h_consume
        by_cases h_l_eq : l = l₀
        · rw [if_pos h_l_eq] at h_consume
          have h_trace_e_rest : ls.trace e_rest = τ := (Option.some.inj h_consume).symm
          rw [ls.trace_cons_external s₀ l₀ s₁ e_rest.trans h_int, ← h_l_eq, ← h_e_rest_eq]
          exact congrArg (Seq.cons l) h_trace_e_rest
        · rw [if_neg h_l_eq] at h_consume
          exact absurd h_consume (by simp)),
    (ls.IsTight_cons_iff s₀ l₀ s₁ e_rest.trans).mpr ⟨
      h_e_rest_eq ▸ h_tight,
      by
        classical
        by_cases h_int : ls.internal l₀
        · refine Or.inr ?_
          intro h_nil
          have h_consume_internal :
              ls.consumeLabel l₀ (Seq.cons l τ) = some (Seq.cons l τ) := by
            unfold LabelledSystem.consumeLabel; simp [h_int]
          rw [h_consume_internal] at h_consume
          have h_trace_e_rest : ls.trace e_rest = Seq.cons l τ :=
            (Option.some.inj h_consume).symm
          rw [h_e_rest_eq, h_nil] at h_trace_e_rest
          rw [ls.trace_init] at h_trace_e_rest
          exact Stream'.Seq.cons_ne_nil h_trace_e_rest.symm
        · exact Or.inl h_int⟩⟩

/-- The trace-decomposition `Equiv` between tight prefixes with trace `cons l
τ` and their `(s₀, l₀, s₁, e_rest)` decomposition. -/
noncomputable def LabelledSystem.TraceDecomp.equiv
    (ls : LabelledSystem State Label) (l : Label) (τ : Seq Label) :
    {e : AlterSeq State Label //
      e.trans.Terminates ∧ ls.trace e = Seq.cons l τ ∧ ls.IsTight e} ≃
    ls.TraceDecomp l τ where
  toFun e := LabelledSystem.TraceDecomp.ofTight ls l τ e.1 e.2.1 e.2.2.1 e.2.2.2
  invFun := LabelledSystem.TraceDecomp.toTight ls l τ
  left_inv := by
    rintro ⟨e, h_term, h_trace, h_tight⟩
    apply Subtype.ext
    dsimp only [LabelledSystem.TraceDecomp.toTight, LabelledSystem.TraceDecomp.ofTight]
    rcases e with ⟨e_init, e_trans⟩
    congr 1
    -- Goal: cons ((e_trans.head.get _).1, (e_trans.head.get _).2) e_trans.tail = e_trans
    exact (Stream'.Seq.head_eq_some (Option.eq_some_of_isSome _)).symm
  right_inv := by
    rintro ⟨s₀, l₀, s₁, ⟨e_rest, h_init, h_term, h_tight, h_consume⟩⟩
    dsimp only [LabelledSystem.TraceDecomp.toTight, LabelledSystem.TraceDecomp.ofTight]
    -- First three PSigma components (s₀, l₀, s₁) match definitionally;
    -- the inner Subtype reduces to the AlterSeq equality `⟨s₁, e_rest.trans⟩
    -- = e_rest` via `h_init`.
    congr 1
    congr 1
    congr 1
    apply Subtype.ext
    change ({init := s₁, trans := e_rest.trans} : AlterSeq State Label) = e_rest
    rw [← h_init]

/-- **One-step trace-cone decomposition.** The trace probability for a
non-empty trace `cons l τ` decomposes over the first transition `(l₀, s₁)`
taken from each initial state `s₀`:

* the joint mass `pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁)` is the
  probability of starting at `s₀` and emitting first transition `(l₀, s₁)`,
* `consumeLabel l₀ (cons l τ)` says how the trace remaining to be produced
  shrinks (or fails) given `l₀`,
* the recursive `traceProb (pe.continuationFrom …) (consumeLabel …)` is the
  conditional trace probability of completing the remainder.

When `consumeLabel l₀ (cons l τ) = none` (external label `l₀ ≠ l`) the
contribution is `0` via `Option.elim`. This is the recursion engine for
inducting `traceProb` equalities along the trace.

The continuation's `history` is the singleton transition just emitted; its
`endState` is `s₁`, matching the next initial state. -/
theorem LabelledSystem.traceProb_first_step
    (ls : LabelledSystem State Label)
    (pe : ProbabilisticExecution ls.toSystem)
    (l : Label) (τ : Seq Label) :
    ls.traceProb pe (Seq.cons l τ) =
      ∑' (s₀ : State) (l₀ : Label) (s₁ : State),
        pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
        (ls.consumeLabel l₀ (Seq.cons l τ)).elim 0
          (fun τ' => ls.traceProb
            (pe.continuationFrom
              ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
              ⟨1, by
                change (Seq.cons (l₀, s₁) Seq.nil).get? 1 = none
                rw [Stream'.Seq.get?_cons_succ]
                exact Stream'.Seq.terminatedAt_nil⟩)
            τ') := by
  classical
  -- Step 1: Use the trace-decomposition Equiv to reindex the LHS tsum
  -- from the LHS subtype over TraceDecomp. We assert the LHS in its sum
  -- form via `change`, so the inner `traceProb` in the RHS stays folded.
  change (∑' (e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ ls.trace e = Seq.cons l τ ∧ ls.IsTight e}),
        pe.probOf e.1 e.2.1) = _
  rw [show
      (∑' (e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ ls.trace e = Seq.cons l τ ∧ ls.IsTight e}),
        pe.probOf e.1 e.2.1)
      = ∑' (d : ls.TraceDecomp l τ),
          pe.probOf (LabelledSystem.TraceDecomp.toTight ls l τ d).1
            (LabelledSystem.TraceDecomp.toTight ls l τ d).2.1 from
    ((LabelledSystem.TraceDecomp.equiv ls l τ).symm.tsum_eq
      (fun e => pe.probOf e.1 e.2.1)).symm]
  -- Step 2: factor each summand via `probOf_cons`.
  rw [tsum_congr (fun d : ls.TraceDecomp l τ =>
    show pe.probOf (LabelledSystem.TraceDecomp.toTight ls l τ d).1
        (LabelledSystem.TraceDecomp.toTight ls l τ d).2.1 =
      pe.init d.1 * pe.kernel ⟨d.1, Seq.nil⟩ (d.2.1, d.2.2.1) *
        (pe.continuationFrom ⟨d.1, Seq.cons (d.2.1, d.2.2.1) Seq.nil⟩
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
        ⟨d.2.2.1, d.2.2.2.1.trans⟩
        (Stream'.Seq.terminates_tail_of_cons
          (LabelledSystem.TraceDecomp.toTight ls l τ d).2.1)
    from ProbabilisticExecution.probOf_cons pe d.1 d.2.1 d.2.2.1 d.2.2.2.1.trans _)]
  -- Step 3: apply `traceProb_continuationFrom_init_restrict` inside the
  -- RHS's `consumeLabel.elim`. Pointwise rewrite per `(s₀, l₀, s₁)`.
  have h_inner_restrict : ∀ (s₀ : State) (l₀ : Label) (s₁ : State),
      (ls.consumeLabel l₀ (Seq.cons l τ)).elim 0
        (fun τ' => ls.traceProb
          (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)) τ') =
      (ls.consumeLabel l₀ (Seq.cons l τ)).elim 0
        (fun τ' => ∑' (e_rest : {e_rest : AlterSeq State Label //
            e_rest.trans.Terminates ∧ ls.trace e_rest = τ' ∧ ls.IsTight e_rest ∧
            e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
              (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)}),
          (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
            e_rest.1 e_rest.2.1) := by
    intros s₀ l₀ s₁
    rcases Option.eq_none_or_eq_some (ls.consumeLabel l₀ (Seq.cons l τ))
      with h | ⟨τ', h⟩
    · rw [h]; rfl
    · rw [h, Option.elim_some, Option.elim_some]
      exact ls.traceProb_continuationFrom_init_restrict pe _ _ τ'
  rw [tsum_congr (fun s₀ => tsum_congr (fun l₀ => tsum_congr (fun s₁ => by
    rw [h_inner_restrict s₀ l₀ s₁])))]
  -- Step 4a: push `init * kernel` inside `Option.elim` and the inner tsum.
  have h_distrib : ∀ (s₀ : State) (l₀ : Label) (s₁ : State),
      pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
        (ls.consumeLabel l₀ (Seq.cons l τ)).elim 0
          (fun τ' => ∑' (e_rest : {e_rest : AlterSeq State Label //
              e_rest.trans.Terminates ∧ ls.trace e_rest = τ' ∧ ls.IsTight e_rest ∧
              e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
                (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)}),
            (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
              (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
              e_rest.1 e_rest.2.1) =
      (ls.consumeLabel l₀ (Seq.cons l τ)).elim 0
        (fun τ' => ∑' (e_rest : {e_rest : AlterSeq State Label //
            e_rest.trans.Terminates ∧ ls.trace e_rest = τ' ∧ ls.IsTight e_rest ∧
            e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
              (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)}),
          pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
          (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
            e_rest.1 e_rest.2.1) := by
    intros s₀ l₀ s₁
    rcases Option.eq_none_or_eq_some (ls.consumeLabel l₀ (Seq.cons l τ))
      with h | ⟨τ', h⟩
    · rw [h]; simp
    · rw [h]; simp only [Option.elim_some]
      rw [ENNReal.tsum_mul_left]
  rw [tsum_congr (fun s₀ => tsum_congr (fun l₀ => tsum_congr (fun s₁ =>
    h_distrib s₀ l₀ s₁)))]
  -- Step 4b: combine `Option.elim` + inner sum into a single inner sum
  -- with the constraint `consumeLabel = some (trace e_rest)`.
  have h_combine : ∀ (s₀ : State) (l₀ : Label) (s₁ : State),
      (ls.consumeLabel l₀ (Seq.cons l τ)).elim 0
        (fun τ' => ∑' (e_rest : {e_rest : AlterSeq State Label //
            e_rest.trans.Terminates ∧ ls.trace e_rest = τ' ∧ ls.IsTight e_rest ∧
            e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
              (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)}),
          pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
          (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
            e_rest.1 e_rest.2.1) =
      ∑' (e_rest : {e_rest : AlterSeq State Label //
          e_rest.trans.Terminates ∧ ls.IsTight e_rest ∧
          e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) ∧
          ls.consumeLabel l₀ (Seq.cons l τ) = some (ls.trace e_rest)}),
        pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
        (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
          e_rest.1 e_rest.2.1 := by
    intros s₀ l₀ s₁
    rcases Option.eq_none_or_eq_some (ls.consumeLabel l₀ (Seq.cons l τ))
      with h_none | ⟨τ', h_some⟩
    · -- none case: LHS = 0; RHS has empty subtype, sum = 0.
      conv_lhs => rw [h_none, Option.elim_none]
      symm
      apply ENNReal.tsum_eq_zero.mpr
      rintro ⟨_, _, _, _, h_consume⟩
      rw [h_none] at h_consume
      exact absurd h_consume (by simp)
    · -- some τ' case: surgical `conv_lhs` so RHS's binder stays symbolic.
      conv_lhs => rw [h_some]; rw [Option.elim_some]
      -- Goal: ∑' (e : {term ∧ trace = τ' ∧ …}), F = ∑' (e : {term ∧ tight ∧ init ∧
      -- consumeLabel = some (trace e)}), F. Build Equiv source ≃ target.
      let e_inner : {e_rest : AlterSeq State Label //
          e_rest.trans.Terminates ∧ ls.trace e_rest = τ' ∧ ls.IsTight e_rest ∧
          e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)} ≃
          {e_rest : AlterSeq State Label //
          e_rest.trans.Terminates ∧ ls.IsTight e_rest ∧
          e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) ∧
          ls.consumeLabel l₀ (Seq.cons l τ) = some (ls.trace e_rest)} :=
        { toFun := fun ⟨e, h_term', h_trace', h_tight', h_init'⟩ =>
            ⟨e, h_term', h_tight', h_init', h_trace' ▸ h_some⟩
          invFun := fun ⟨e, h_term', h_tight', h_init', h_consume'⟩ =>
            ⟨e, h_term', by
              have : some τ' = some (ls.trace e) := h_some ▸ h_consume'
              exact (Option.some.inj this).symm,
             h_tight', h_init'⟩
          left_inv := fun ⟨_, _, _, _, _⟩ => rfl
          right_inv := fun ⟨_, _, _, _, _⟩ => rfl }
      let F : {e_rest : AlterSeq State Label //
          e_rest.trans.Terminates ∧ ls.IsTight e_rest ∧
          e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) ∧
          ls.consumeLabel l₀ (Seq.cons l τ) = some (ls.trace e_rest)} → ENNReal :=
        fun e_rest => pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
          (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
            e_rest.1 e_rest.2.1
      calc (∑' (c : {e_rest // e_rest.trans.Terminates ∧ ls.trace e_rest = τ' ∧
              ls.IsTight e_rest ∧ e_rest.init = _}),
            pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
            (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ _).probOf c.1 c.2.1)
          = ∑' c, F (e_inner c) := by
            apply tsum_congr
            rintro ⟨_, _, _, _, _⟩
            rfl
        _ = ∑' b, F b := e_inner.tsum_eq F
  rw [tsum_congr (fun s₀ => tsum_congr (fun l₀ => tsum_congr (fun s₁ =>
    h_combine s₀ l₀ s₁)))]
  -- Step 4c.1: in the LHS summand, substitute `⟨d.2.2.1, d.2.2.2.1.trans⟩`
  -- with `d.2.2.2.1` (= e_rest), justified by `d.2.2.2.2.1 : e_rest.init = s₁`.
  have h_summand_eq : ∀ d : ls.TraceDecomp l τ,
      pe.init d.1 * pe.kernel ⟨d.1, Seq.nil⟩ (d.2.1, d.2.2.1) *
        (pe.continuationFrom ⟨d.1, Seq.cons (d.2.1, d.2.2.1) Seq.nil⟩
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
          ⟨d.2.2.1, d.2.2.2.1.trans⟩
          (Stream'.Seq.terminates_tail_of_cons
            (LabelledSystem.TraceDecomp.toTight ls l τ d).2.1) =
      pe.init d.1 * pe.kernel ⟨d.1, Seq.nil⟩ (d.2.1, d.2.2.1) *
        (pe.continuationFrom ⟨d.1, Seq.cons (d.2.1, d.2.2.1) Seq.nil⟩
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
          d.2.2.2.1
          d.2.2.2.2.2.1 := by
    rintro ⟨s₀, l₀, s₁, ⟨e_rest, h_init, h_term, h_tight, h_consume⟩⟩
    rcases e_rest with ⟨init, trans⟩
    simp only at h_init
    subst h_init
    rfl
  rw [tsum_congr h_summand_eq]
  -- Step 4c.2: master Equiv between `TraceDecomp l τ` and the Σ-form.
  -- Constraint order is rearranged + `init = s₁` ↔ `init = endState ⟨s₀,
  -- cons (l₀, s₁) nil⟩ _` via `endState_singleton_cons`.
  let e_master : ls.TraceDecomp l τ ≃
      Σ s₀ : State, Σ l₀ : Label, Σ s₁ : State,
        {e_rest : AlterSeq State Label //
          e_rest.trans.Terminates ∧ ls.IsTight e_rest ∧
          e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) ∧
          ls.consumeLabel l₀ (Seq.cons l τ) = some (ls.trace e_rest)} :=
    { toFun := fun ⟨s₀, l₀, s₁, e_rest, h_init, h_term, h_tight, h_consume⟩ =>
        ⟨s₀, l₀, s₁, ⟨e_rest, h_term, h_tight,
          h_init.trans (AlterSeq.endState_singleton_cons s₀ l₀ s₁).symm,
          h_consume⟩⟩
      invFun := fun ⟨s₀, l₀, s₁, e_rest, h_term, h_tight, h_init_endState, h_consume⟩ =>
        ⟨s₀, l₀, s₁, ⟨e_rest,
          h_init_endState.trans (AlterSeq.endState_singleton_cons s₀ l₀ s₁),
          h_term, h_tight, h_consume⟩⟩
      left_inv := fun ⟨_, _, _, ⟨_, _, _, _, _⟩⟩ => rfl
      right_inv := fun ⟨_, _, _, ⟨_, _, _, _, _⟩⟩ => rfl }
  -- Step 4c.3: define the per-Sigma-element summand G and chain.
  let G : (Σ s₀ : State, Σ l₀ : Label, Σ s₁ : State,
      {e_rest : AlterSeq State Label //
        e_rest.trans.Terminates ∧ ls.IsTight e_rest ∧
        e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) ∧
        ls.consumeLabel l₀ (Seq.cons l τ) = some (ls.trace e_rest)}) → ENNReal :=
    fun b => pe.init b.1 * pe.kernel ⟨b.1, Seq.nil⟩ (b.2.1, b.2.2.1) *
      (pe.continuationFrom ⟨b.1, Seq.cons (b.2.1, b.2.2.1) Seq.nil⟩
        (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
        b.2.2.2.1 b.2.2.2.2.1
  -- Final chain: LHS = ∑' d, G (e_master d) = ∑' b, G b = (RHS).
  calc (∑' d : ls.TraceDecomp l τ,
          pe.init d.1 * pe.kernel ⟨d.1, Seq.nil⟩ (d.2.1, d.2.2.1) *
            (pe.continuationFrom ⟨d.1, Seq.cons (d.2.1, d.2.2.1) Seq.nil⟩
              (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
              d.2.2.2.1 d.2.2.2.2.2.1)
      = ∑' d, G (e_master d) := by
        apply tsum_congr
        rintro ⟨_, _, _, ⟨_, _, _, _, _⟩⟩
        rfl
    _ = ∑' b, G b := e_master.tsum_eq G
    _ = _ := by
        rw [ENNReal.tsum_sigma']
        apply tsum_congr; intro s₀
        rw [ENNReal.tsum_sigma']
        apply tsum_congr; intro l₀
        rw [ENNReal.tsum_sigma']

/-- The trace probability of any trace is at most `1`.

The bound holds because: (i) `probOfRemaining ≤ 1` (each kernel value
≤ 1, so a product of them is `≤ 1`); (ii) `probOf e ≤ pe.init e.init`
(direct corollary); (iii) tight prefixes with a given trace correspond
to *disjoint* trace-cone cylinders, so the sum over them is bounded by
the measure of the cone, which is in `[0, 1]`.

The disjoint-cylinder argument (iii) is non-trivial without explicit
measure theory. A combinatorial route: split the sum by the `e.init`
factor, then bound the resulting per-state sums over interleavings of
internal transitions and external label transitions by inducting on the
length of `τ`. (Currently sorry — to be discharged once we have
either a measure-theoretic framework or the kernel-sum lemmas needed
for the induction.)

The supporting lemmas `probOfRemaining_le_one` and `probOf_le_init` are
proved in `MyMathlibProject.Basic`. -/
theorem LabelledSystem.traceProb_le_one
    (ls : LabelledSystem State Label)
    (pe : ProbabilisticExecution ls.toSystem) (τ : Seq Label) :
    ls.traceProb pe τ ≤ 1 := by
  sorry


/-! ### Faithful (PMF) scheduler and probabilistic execution

The standard `Scheduler.next : AlterSeq → Option (PMF (Label × PMF State))`
collapses the halt-vs-emit choice: it can emit "halt" or one Dirac on a
particular distribution, but not assign probability to both halt and emit.

`PMFScheduler` lifts the outer `Option` inside the PMF, giving
`next : AlterSeq → PMF (Option (Label × PMF State))`. This admits weighted
halt mass — essential for the v4 trace-coupling construction, where pe_A's
halt mass at a history reflects the posterior weight of concrete prefixes
that have already halted. -/

/-- **Faithful scheduler**: like `Scheduler` but `next` returns a full
PMF over emit/halt outcomes (rather than `Option (PMF …)`). The `valid`
condition asserts that every emitted `some (l, μ)` is a valid system
step at the prefix's end state. -/
structure PMFScheduler (sys : System State Label) where
  next : AlterSeq State Label → PMF (Option (Label × PMF State))
  valid : ∀ (e : AlterSeq State Label) (n : ℕ) (s : State),
    e.trans.TerminatedAt n → e.stateAt n = some s →
    ∀ (l : Label) (μ : PMF State),
      some (l, μ) ∈ (next e).support → sys.step s l μ

/-- **Faithful probabilistic execution**: an initial distribution `init`
(a PMF, not necessarily Dirac) plus a `PMFScheduler`. Note: the
initial distribution is general here (a change from the older
ProbabilisticExecution structure, which used a single `initState`).
This is needed for v4 trace inclusion where `pe_A.init = μ_A_init`. -/
structure PMFProbabilisticExecution (sys : System State Label) where
  /-- The initial distribution over states. -/
  init : PMF State
  scheduler : PMFScheduler sys

namespace PMFProbabilisticExecution

variable {sys : System State Label}

/-- The faithful one-step kernel. Given a prefix `e` and a step `(l, s')`,
the probability mass is:
  `kernel pe e (l, s') = ∑' μ, (pe.scheduler.next e) (some (l, μ)) * μ s'`
i.e., aggregating over all distributions μ that the scheduler might emit
alongside label `l`, weighted by the emission probability and the
state-sample probability. -/
noncomputable def kernel (pe : PMFProbabilisticExecution sys)
    (e : AlterSeq State Label) (step : Label × State) : ENNReal :=
  ∑' μ, pe.scheduler.next e (some (step.1, μ)) * μ step.2

/-- The faithful kernel is bounded by `1`. -/
theorem kernel_le_one (pe : PMFProbabilisticExecution sys)
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

/-- Faithful `probOfRemaining`: foldl product of `kernel` masses across `xs`. -/
noncomputable def probOfRemaining (pe : PMFProbabilisticExecution sys)
    (pre : AlterSeq State Label) (xs : List (Label × State)) : ENNReal :=
  xs.foldl
    (fun (acc : ENNReal × AlterSeq State Label) hd =>
      (acc.1 * pe.kernel acc.2 hd,
       ⟨acc.2.init, acc.2.trans.append (Seq.cons hd Seq.nil)⟩))
    (1, pre)
    |>.1

/-- Faithful `probOf`: `pe.init e.init` times `probOfRemaining` along `e`'s
transitions. -/
noncomputable def probOf (pe : PMFProbabilisticExecution sys)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates) : ENNReal :=
  pe.init e.init * pe.probOfRemaining ⟨e.init, Seq.nil⟩ (e.trans.toList hFin)

/-- Auxiliary: `probOfRemaining`'s foldl-acc stays `≤ 1`. -/
private theorem probOfRemaining_aux_le_one (pe : PMFProbabilisticExecution sys)
    (xs : List (Label × State)) :
    ∀ acc : ENNReal × AlterSeq State Label, acc.1 ≤ 1 →
    (xs.foldl
      (fun (acc : ENNReal × AlterSeq State Label) hd =>
        (acc.1 * pe.kernel acc.2 hd,
         ⟨acc.2.init, acc.2.trans.append (Seq.cons hd Seq.nil)⟩)) acc).1 ≤ 1 := by
  induction xs with
  | nil => intro acc h_acc; exact h_acc
  | cons hd rest ih =>
    intro acc h_acc
    apply ih
    change acc.1 * pe.kernel acc.2 hd ≤ 1
    calc acc.1 * pe.kernel acc.2 hd
        ≤ 1 * 1 := by gcongr; exact pe.kernel_le_one _ _
      _ = 1 := one_mul 1

/-- `probOfRemaining` is bounded by `1`. -/
theorem probOfRemaining_le_one (pe : PMFProbabilisticExecution sys)
    (pre : AlterSeq State Label) (xs : List (Label × State)) :
    pe.probOfRemaining pre xs ≤ 1 :=
  pe.probOfRemaining_aux_le_one xs (1, pre) (le_refl _)

/-- `probOf e ≤ pe.init e.init`. -/
theorem probOf_le_init (pe : PMFProbabilisticExecution sys)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates) :
    pe.probOf e hFin ≤ pe.init e.init := by
  unfold probOf
  calc pe.init e.init * pe.probOfRemaining ⟨e.init, Seq.nil⟩ (e.trans.toList hFin)
      ≤ pe.init e.init * 1 := by gcongr; exact pe.probOfRemaining_le_one _ _
    _ = pe.init e.init := mul_one _

/-- The initial-accumulator value factors linearly out of `probOfRemaining`'s foldl. -/
private theorem foldl_acc_linear (pe : PMFProbabilisticExecution sys) :
    ∀ (xs : List (Label × State)) (c : ENNReal) (pre : AlterSeq State Label),
    (xs.foldl
      (fun (acc : ENNReal × AlterSeq State Label) hd =>
        (acc.1 * pe.kernel acc.2 hd,
         ⟨acc.2.init, acc.2.trans.append (Seq.cons hd Seq.nil)⟩)) (c, pre)).1 =
    c * (xs.foldl
      (fun (acc : ENNReal × AlterSeq State Label) hd =>
        (acc.1 * pe.kernel acc.2 hd,
         ⟨acc.2.init, acc.2.trans.append (Seq.cons hd Seq.nil)⟩)) (1, pre)).1 := by
  intro xs
  induction xs with
  | nil => intro c pre; simp [List.foldl]
  | cons hd rest ih =>
    intro c pre
    simp only [List.foldl]
    rw [ih (c * pe.kernel pre hd) _, ih (1 * pe.kernel pre hd) _]
    ring

/-- `probOfRemaining` decomposes at the head. -/
theorem probOfRemaining_cons (pe : PMFProbabilisticExecution sys)
    (pre : AlterSeq State Label) (hd : Label × State) (rest : List (Label × State)) :
    pe.probOfRemaining pre (hd :: rest) =
      pe.kernel pre hd *
        pe.probOfRemaining ⟨pre.init, pre.trans.append (Seq.cons hd Seq.nil)⟩ rest := by
  unfold probOfRemaining
  simp only [List.foldl]
  rw [pe.foldl_acc_linear rest (1 * pe.kernel pre hd) _]
  ring

/-- The faithful `continuationFrom`: a probabilistic execution starting at the
end-state of `history`, with its scheduler shifted so it queries `pe.scheduler`
on prefixes extended by `history` on the left. -/
noncomputable def continuationFrom (pe : PMFProbabilisticExecution sys)
    (history : AlterSeq State Label) (h_term : history.trans.Terminates) :
    PMFProbabilisticExecution sys where
  init := PMF.pure (history.endState h_term)
  scheduler :=
    { next := fun e' =>
        open Classical in
        if e'.init = history.endState h_term then
          pe.scheduler.next ⟨history.init, history.trans.append e'.trans⟩
        else
          PMF.pure none
      valid := by
        classical
        intro e' n s h_term_e' h_state_e' l μ h_supp
        by_cases h_init : e'.init = history.endState h_term
        swap
        · rw [if_neg h_init] at h_supp
          rw [PMF.support_pure] at h_supp
          exact absurd h_supp (by simp)
        rw [if_pos h_init] at h_supp
        set m := Nat.find h_term with hm_def
        refine pe.scheduler.valid
          ⟨history.init, history.trans.append e'.trans⟩ (m + n) s ?_ ?_ l μ h_supp
        · exact Stream'.Seq.terminatedAt_append_find h_term h_term_e'
        · rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
          · subst hn0
            have h_e'_init : s = e'.init := by
              have : e'.stateAt 0 = some e'.init := rfl
              rw [this] at h_state_e'
              exact (Option.some.inj h_state_e').symm
            have h_s_eq : s = history.endState h_term := by rw [h_e'_init]; exact h_init
            rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
            · rw [Nat.add_zero, hm0]
              change some history.init = some s
              have h_endState_eq : history.endState h_term = history.init := by
                have h_eq := history.stateAt_find_eq_endState h_term
                rw [← hm_def, hm0] at h_eq
                have h_zero : history.stateAt 0 = some history.init := rfl
                rw [h_zero] at h_eq
                exact (Option.some.inj h_eq).symm
              rw [h_s_eq, h_endState_eq]
            · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm_pos.ne'
              have hj' : m = j + 1 := hj
              rw [Nat.add_zero, hj']
              change ((history.trans.append e'.trans).get? j).map Prod.snd = some s
              have h_lt_find : j < Nat.find h_term := by
                rw [← hm_def]; rw [hj']; exact Nat.lt_succ_self j
              have h_before : (history.trans.append e'.trans).get? j =
                  history.trans.get? j :=
                Stream'.Seq.get?_append_before_length (Nat.find_min h_term h_lt_find)
              rw [h_before]
              change history.stateAt (j + 1) = some s
              rw [← hj', hm_def, history.stateAt_find_eq_endState h_term, h_s_eq]
          · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn_pos.ne'
            have hk' : n = k + 1 := hk
            rw [hk']
            change ((history.trans.append e'.trans).get? (m + k)).map Prod.snd = some s
            have h_after : (history.trans.append e'.trans).get? (m + k) =
                e'.trans.get? k :=
              Stream'.Seq.get?_append_find h_term e'.trans k
            rw [h_after]
            change (e'.trans.get? k).map Prod.snd = some s
            rw [hk'] at h_state_e'
            exact h_state_e' }

/-- The `continuationFrom`'s kernel at a local prefix starting at
`history.endState` equals `pe`'s kernel at the history-extended prefix. -/
theorem kernel_continuationFrom (pe : PMFProbabilisticExecution sys)
    (history : AlterSeq State Label) (h_term : history.trans.Terminates)
    (extra_trans : Seq (Label × State)) (step : Label × State) :
    (pe.continuationFrom history h_term).kernel
        ⟨history.endState h_term, extra_trans⟩ step =
      pe.kernel ⟨history.init, history.trans.append extra_trans⟩ step := by
  classical
  unfold kernel
  change ∑' μ, (if (⟨history.endState h_term, extra_trans⟩ :
        AlterSeq State Label).init = history.endState h_term then
        pe.scheduler.next ⟨history.init, history.trans.append extra_trans⟩
      else PMF.pure none) (some (step.1, μ)) * μ step.2
      = ∑' μ, pe.scheduler.next ⟨history.init, history.trans.append extra_trans⟩
          (some (step.1, μ)) * μ step.2
  rw [if_pos rfl]

/-- The `continuationFrom`'s `probOfRemaining`, on a local prefix starting at
`history.endState`, equals `pe`'s `probOfRemaining` from the history-extended
prefix. -/
theorem probOfRemaining_continuationFrom (pe : PMFProbabilisticExecution sys)
    (history : AlterSeq State Label) (h_term : history.trans.Terminates)
    (xs : List (Label × State)) :
    (pe.continuationFrom history h_term).probOfRemaining
        ⟨history.endState h_term, Seq.nil⟩ xs =
      pe.probOfRemaining ⟨history.init, history.trans⟩ xs := by
  have h_aux : ∀ (xs : List (Label × State)) (c : ENNReal)
      (extra : Seq (Label × State)),
      (xs.foldl (fun acc hd =>
        (acc.1 * (pe.continuationFrom history h_term).kernel acc.2 hd,
         ⟨acc.2.init, acc.2.trans.append (Seq.cons hd Seq.nil)⟩))
        (c, ⟨history.endState h_term, extra⟩)).1 =
      (xs.foldl (fun acc hd =>
        (acc.1 * pe.kernel acc.2 hd,
         ⟨acc.2.init, acc.2.trans.append (Seq.cons hd Seq.nil)⟩))
        (c, ⟨history.init, history.trans.append extra⟩)).1 := by
    intro xs
    induction xs with
    | nil => intros; rfl
    | cons hd rest ih =>
      intro c extra
      simp only [List.foldl]
      rw [kernel_continuationFrom pe history h_term extra hd]
      have h_assoc : history.trans.append (extra.append (Seq.cons hd Seq.nil)) =
          (history.trans.append extra).append (Seq.cons hd Seq.nil) :=
        (Stream'.Seq.append_assoc _ _ _).symm
      rw [← h_assoc]
      exact ih _ _
  unfold probOfRemaining
  exact h_aux xs 1 Seq.nil |>.trans (by rw [Stream'.Seq.append_nil])

/-- The `continuationFrom`'s `probOf`, at a local prefix starting at
`history.endState`, equals `pe`'s `probOfRemaining` from `history`'s trans
on the local prefix's transition list. -/
theorem probOf_continuationFrom (pe : PMFProbabilisticExecution sys)
    (history : AlterSeq State Label) (h_term : history.trans.Terminates)
    (e_local : AlterSeq State Label) (h_e_local : e_local.trans.Terminates)
    (h_init : e_local.init = history.endState h_term) :
    (pe.continuationFrom history h_term).probOf e_local h_e_local =
      pe.probOfRemaining ⟨history.init, history.trans⟩ (e_local.trans.toList h_e_local) := by
  unfold probOf
  have h_pmf : (pe.continuationFrom history h_term).init e_local.init = 1 := by
    change (PMF.pure (history.endState h_term)) e_local.init = 1
    rw [h_init, PMF.pure_apply]
    simp
  rw [h_pmf, one_mul, h_init]
  exact probOfRemaining_continuationFrom pe history h_term _

/-- `continuationFrom`'s `probOf` is zero when the local prefix's init
doesn't match `history.endState`: the `init` factor is `0`. -/
theorem probOf_continuationFrom_zero_of_init_ne
    (pe : PMFProbabilisticExecution sys) (history : AlterSeq State Label)
    (h_term : history.trans.Terminates) (e_local : AlterSeq State Label)
    (h_e_local : e_local.trans.Terminates)
    (h_init_ne : e_local.init ≠ history.endState h_term) :
    (pe.continuationFrom history h_term).probOf e_local h_e_local = 0 := by
  unfold probOf
  have h_pmf : (pe.continuationFrom history h_term).init e_local.init = 0 := by
    change (PMF.pure (history.endState h_term)) e_local.init = 0
    rw [PMF.pure_apply]
    simp [h_init_ne.symm, Ne.symm]
  rw [h_pmf]
  ring

/-- **Factorization of `probOf` over the first transition** for the
PMF execution. -/
theorem probOf_cons (pe : PMFProbabilisticExecution sys)
    (s₀ : State) (l₀ : Label) (s₁ : State) (e_rest_trans : Seq (Label × State))
    (h_term_full : (Seq.cons (l₀, s₁) e_rest_trans).Terminates) :
    pe.probOf ⟨s₀, Seq.cons (l₀, s₁) e_rest_trans⟩ h_term_full =
      pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
      (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
            : (Seq.cons (l₀, s₁) Seq.nil).Terminates)).probOf
        ⟨s₁, e_rest_trans⟩ (Stream'.Seq.terminates_tail_of_cons h_term_full) := by
  have h_hist_term : (Seq.cons (l₀, s₁) Seq.nil : Seq (Label × State)).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  have h_e_rest_term : e_rest_trans.Terminates :=
    Stream'.Seq.terminates_tail_of_cons h_term_full
  have h_find : Nat.find h_hist_term = 1 := by
    apply le_antisymm
    · exact Nat.find_le (show (Seq.cons (l₀, s₁) Seq.nil).TerminatedAt 1 from rfl)
    · rw [Nat.one_le_iff_ne_zero]
      intro h_zero
      exact Stream'.Seq.cons_not_terminatedAt_zero
        (h_zero ▸ Nat.find_spec h_hist_term)
  have h_endState :
      ({ init := s₀, trans := Seq.cons (l₀, s₁) Seq.nil
        : AlterSeq State Label }).endState h_hist_term = s₁ := by
    have h_eq := AlterSeq.stateAt_find_eq_endState
      ({ init := s₀, trans := Seq.cons (l₀, s₁) Seq.nil
        : AlterSeq State Label }) h_hist_term
    rw [h_find] at h_eq
    exact (Option.some.inj h_eq).symm
  have h_lhs : pe.probOf ⟨s₀, Seq.cons (l₀, s₁) e_rest_trans⟩ h_term_full =
      pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
      pe.probOfRemaining ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
        (e_rest_trans.toList h_e_rest_term) := by
    unfold probOf
    rw [Stream'.Seq.toList_cons, probOfRemaining_cons]
    rw [show (⟨s₀, Seq.nil⟩ : AlterSeq State Label).trans.append
      (Seq.cons (l₀, s₁) Seq.nil) = Seq.cons (l₀, s₁) Seq.nil from
      Stream'.Seq.nil_append _]
    ring
  rw [h_lhs]
  rw [probOf_continuationFrom pe ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ h_hist_term
    ⟨s₁, e_rest_trans⟩ h_e_rest_term h_endState.symm]

end PMFProbabilisticExecution

/-- Trace probability for `PMFProbabilisticExecution`: sum of `probOf` over
finite tight executions whose trace equals `τ`. -/
noncomputable def LabelledSystem.traceProbPMF
    {State Label : Type} (ls : LabelledSystem State Label)
    (pe : PMFProbabilisticExecution ls.toSystem) (τ : Seq Label) : ENNReal :=
  ∑' e : {e : AlterSeq State Label //
      e.trans.Terminates ∧ ls.trace e = τ ∧ ls.IsTight e},
    pe.probOf e.1 e.2.1

/-- The `traceProbPMF` of a `continuationFrom`-execution restricts to the
sub-subtype where `e.init = history.endState`, mirroring
`traceProb_continuationFrom_init_restrict`. -/
theorem LabelledSystem.traceProbPMF_continuationFrom_init_restrict
    {State Label : Type} (ls : LabelledSystem State Label)
    (pe : PMFProbabilisticExecution ls.toSystem)
    (history : AlterSeq State Label) (h_term : history.trans.Terminates)
    (τ : Seq Label) :
    LabelledSystem.traceProbPMF ls (pe.continuationFrom history h_term) τ =
      ∑' (e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ ls.trace e = τ ∧ ls.IsTight e ∧
          e.init = history.endState h_term}),
        (pe.continuationFrom history h_term).probOf e.1 e.2.1 := by
  classical
  unfold LabelledSystem.traceProbPMF
  set A := {e : AlterSeq State Label //
    e.trans.Terminates ∧ ls.trace e = τ ∧ ls.IsTight e} with hA_def
  set p : A → Prop := fun a => a.1.init = history.endState h_term with hp_def
  rw [show
      (∑' (a : A), (pe.continuationFrom history h_term).probOf a.1 a.2.1) =
      ∑' (x : {a : A // p a} ⊕ {a : A // ¬ p a}),
        (pe.continuationFrom history h_term).probOf
          ((Equiv.sumCompl p) x).1 ((Equiv.sumCompl p) x).2.1 from
    ((Equiv.sumCompl p).tsum_eq _).symm]
  rw [tsum_sum_type]
  have h_zero : (∑' (a : {a : A // ¬ p a}),
      (pe.continuationFrom history h_term).probOf
        ((Equiv.sumCompl p) (Sum.inr a)).1
        ((Equiv.sumCompl p) (Sum.inr a)).2.1) = 0 := by
    apply ENNReal.tsum_eq_zero.mpr
    rintro ⟨⟨e, h_term', h_trace', h_tight'⟩, h_ne⟩
    exact PMFProbabilisticExecution.probOf_continuationFrom_zero_of_init_ne
      pe history h_term e h_term' h_ne
  rw [h_zero, add_zero]
  let e_B' : {a : A // p a} ≃ {e : AlterSeq State Label //
      e.trans.Terminates ∧ ls.trace e = τ ∧ ls.IsTight e ∧
      e.init = history.endState h_term} :=
    { toFun := fun ⟨⟨e, h_term', h_trace', h_tight'⟩, h_init'⟩ =>
        ⟨e, h_term', h_trace', h_tight', h_init'⟩
      invFun := fun ⟨e, h_term', h_trace', h_tight', h_init'⟩ =>
        ⟨⟨e, h_term', h_trace', h_tight'⟩, h_init'⟩
      left_inv := fun ⟨⟨_, _, _, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _, _⟩ => rfl }
  refine (tsum_congr (fun a => ?_)).trans
    (e_B'.tsum_eq (fun e => (pe.continuationFrom history h_term).probOf e.1 e.2.1))
  rcases a with ⟨⟨e, _, _, _⟩, _⟩
  rfl

/-- **First-step decomposition for `traceProbPMF`** — the parallel of
`traceProb_first_step`. Decomposes a cons-trace probability as a sum
over `(s₀, l₀, s₁)` of init mass × kernel × continuation traceProbPMF. -/
theorem LabelledSystem.traceProbPMF_first_step
    {State Label : Type} (ls : LabelledSystem State Label)
    (pe : PMFProbabilisticExecution ls.toSystem)
    (l : Label) (τ : Seq Label) :
    LabelledSystem.traceProbPMF ls pe (Seq.cons l τ) =
      ∑' (s₀ : State) (l₀ : Label) (s₁ : State),
        pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
        (ls.consumeLabel l₀ (Seq.cons l τ)).elim 0
          (fun τ' => LabelledSystem.traceProbPMF ls
            (pe.continuationFrom
              ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
              ⟨1, by
                change (Seq.cons (l₀, s₁) Seq.nil).get? 1 = none
                rw [Stream'.Seq.get?_cons_succ]
                exact Stream'.Seq.terminatedAt_nil⟩)
            τ') := by
  classical
  -- Step 1: reindex via TraceDecomp.equiv.
  change (∑' (e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ ls.trace e = Seq.cons l τ ∧ ls.IsTight e}),
        pe.probOf e.1 e.2.1) = _
  rw [show
      (∑' (e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ ls.trace e = Seq.cons l τ ∧ ls.IsTight e}),
        pe.probOf e.1 e.2.1)
      = ∑' (d : ls.TraceDecomp l τ),
          pe.probOf (LabelledSystem.TraceDecomp.toTight ls l τ d).1
            (LabelledSystem.TraceDecomp.toTight ls l τ d).2.1 from
    ((LabelledSystem.TraceDecomp.equiv ls l τ).symm.tsum_eq
      (fun e => pe.probOf e.1 e.2.1)).symm]
  -- Step 2: factor each summand via probOf_cons.
  rw [tsum_congr (fun d : ls.TraceDecomp l τ =>
    show pe.probOf (LabelledSystem.TraceDecomp.toTight ls l τ d).1
        (LabelledSystem.TraceDecomp.toTight ls l τ d).2.1 =
      pe.init d.1 * pe.kernel ⟨d.1, Seq.nil⟩ (d.2.1, d.2.2.1) *
        (pe.continuationFrom ⟨d.1, Seq.cons (d.2.1, d.2.2.1) Seq.nil⟩
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
        ⟨d.2.2.1, d.2.2.2.1.trans⟩
        (Stream'.Seq.terminates_tail_of_cons
          (LabelledSystem.TraceDecomp.toTight ls l τ d).2.1)
    from PMFProbabilisticExecution.probOf_cons pe d.1 d.2.1 d.2.2.1 d.2.2.2.1.trans _)]
  -- Step 3: apply traceProbPMF_continuationFrom_init_restrict inside consumeLabel.elim.
  have h_inner_restrict : ∀ (s₀ : State) (l₀ : Label) (s₁ : State),
      (ls.consumeLabel l₀ (Seq.cons l τ)).elim 0
        (fun τ' => LabelledSystem.traceProbPMF ls
          (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)) τ') =
      (ls.consumeLabel l₀ (Seq.cons l τ)).elim 0
        (fun τ' => ∑' (e_rest : {e_rest : AlterSeq State Label //
            e_rest.trans.Terminates ∧ ls.trace e_rest = τ' ∧ ls.IsTight e_rest ∧
            e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
              (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)}),
          (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
            e_rest.1 e_rest.2.1) := by
    intros s₀ l₀ s₁
    rcases Option.eq_none_or_eq_some (ls.consumeLabel l₀ (Seq.cons l τ))
      with h | ⟨τ', h⟩
    · rw [h]; rfl
    · rw [h, Option.elim_some, Option.elim_some]
      exact LabelledSystem.traceProbPMF_continuationFrom_init_restrict ls pe _ _ τ'
  rw [tsum_congr (fun s₀ => tsum_congr (fun l₀ => tsum_congr (fun s₁ => by
    rw [h_inner_restrict s₀ l₀ s₁])))]
  -- Step 4a: push init * kernel inside Option.elim and the inner tsum.
  have h_distrib : ∀ (s₀ : State) (l₀ : Label) (s₁ : State),
      pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
        (ls.consumeLabel l₀ (Seq.cons l τ)).elim 0
          (fun τ' => ∑' (e_rest : {e_rest : AlterSeq State Label //
              e_rest.trans.Terminates ∧ ls.trace e_rest = τ' ∧ ls.IsTight e_rest ∧
              e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
                (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)}),
            (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
              (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
              e_rest.1 e_rest.2.1) =
      (ls.consumeLabel l₀ (Seq.cons l τ)).elim 0
        (fun τ' => ∑' (e_rest : {e_rest : AlterSeq State Label //
            e_rest.trans.Terminates ∧ ls.trace e_rest = τ' ∧ ls.IsTight e_rest ∧
            e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
              (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)}),
          pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
          (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
            e_rest.1 e_rest.2.1) := by
    intros s₀ l₀ s₁
    rcases Option.eq_none_or_eq_some (ls.consumeLabel l₀ (Seq.cons l τ))
      with h | ⟨τ', h⟩
    · rw [h]; simp
    · rw [h]; simp only [Option.elim_some]
      rw [ENNReal.tsum_mul_left]
  rw [tsum_congr (fun s₀ => tsum_congr (fun l₀ => tsum_congr (fun s₁ =>
    h_distrib s₀ l₀ s₁)))]
  -- Step 4b: combine Option.elim + inner sum into a single inner sum with the
  -- constraint consumeLabel = some (trace e_rest).
  have h_combine : ∀ (s₀ : State) (l₀ : Label) (s₁ : State),
      (ls.consumeLabel l₀ (Seq.cons l τ)).elim 0
        (fun τ' => ∑' (e_rest : {e_rest : AlterSeq State Label //
            e_rest.trans.Terminates ∧ ls.trace e_rest = τ' ∧ ls.IsTight e_rest ∧
            e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
              (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)}),
          pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
          (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
            e_rest.1 e_rest.2.1) =
      ∑' (e_rest : {e_rest : AlterSeq State Label //
          e_rest.trans.Terminates ∧ ls.IsTight e_rest ∧
          e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) ∧
          ls.consumeLabel l₀ (Seq.cons l τ) = some (ls.trace e_rest)}),
        pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
        (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
          e_rest.1 e_rest.2.1 := by
    intros s₀ l₀ s₁
    rcases Option.eq_none_or_eq_some (ls.consumeLabel l₀ (Seq.cons l τ))
      with h_none | ⟨τ', h_some⟩
    · conv_lhs => rw [h_none, Option.elim_none]
      symm
      apply ENNReal.tsum_eq_zero.mpr
      rintro ⟨_, _, _, _, h_consume⟩
      rw [h_none] at h_consume
      exact absurd h_consume (by simp)
    · conv_lhs => rw [h_some]; rw [Option.elim_some]
      let e_inner : {e_rest : AlterSeq State Label //
          e_rest.trans.Terminates ∧ ls.trace e_rest = τ' ∧ ls.IsTight e_rest ∧
          e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)} ≃
          {e_rest : AlterSeq State Label //
          e_rest.trans.Terminates ∧ ls.IsTight e_rest ∧
          e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) ∧
          ls.consumeLabel l₀ (Seq.cons l τ) = some (ls.trace e_rest)} :=
        { toFun := fun ⟨e, h_term', h_trace', h_tight', h_init'⟩ =>
            ⟨e, h_term', h_tight', h_init', h_trace' ▸ h_some⟩
          invFun := fun ⟨e, h_term', h_tight', h_init', h_consume'⟩ =>
            ⟨e, h_term', by
              have : some τ' = some (ls.trace e) := h_some ▸ h_consume'
              exact (Option.some.inj this).symm,
             h_tight', h_init'⟩
          left_inv := fun ⟨_, _, _, _, _⟩ => rfl
          right_inv := fun ⟨_, _, _, _, _⟩ => rfl }
      let F : {e_rest : AlterSeq State Label //
          e_rest.trans.Terminates ∧ ls.IsTight e_rest ∧
          e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) ∧
          ls.consumeLabel l₀ (Seq.cons l τ) = some (ls.trace e_rest)} → ENNReal :=
        fun e_rest => pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
          (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
            e_rest.1 e_rest.2.1
      calc (∑' (c : {e_rest // e_rest.trans.Terminates ∧ ls.trace e_rest = τ' ∧
              ls.IsTight e_rest ∧ e_rest.init = _}),
            pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
            (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ _).probOf c.1 c.2.1)
          = ∑' c, F (e_inner c) := by
            apply tsum_congr
            rintro ⟨_, _, _, _, _⟩
            rfl
        _ = ∑' b, F b := e_inner.tsum_eq F
  rw [tsum_congr (fun s₀ => tsum_congr (fun l₀ => tsum_congr (fun s₁ =>
    h_combine s₀ l₀ s₁)))]
  -- Step 4c.1: substitute ⟨d.2.2.1, d.2.2.2.1.trans⟩ with d.2.2.2.1 (= e_rest).
  have h_summand_eq : ∀ d : ls.TraceDecomp l τ,
      pe.init d.1 * pe.kernel ⟨d.1, Seq.nil⟩ (d.2.1, d.2.2.1) *
        (pe.continuationFrom ⟨d.1, Seq.cons (d.2.1, d.2.2.1) Seq.nil⟩
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
          ⟨d.2.2.1, d.2.2.2.1.trans⟩
          (Stream'.Seq.terminates_tail_of_cons
            (LabelledSystem.TraceDecomp.toTight ls l τ d).2.1) =
      pe.init d.1 * pe.kernel ⟨d.1, Seq.nil⟩ (d.2.1, d.2.2.1) *
        (pe.continuationFrom ⟨d.1, Seq.cons (d.2.1, d.2.2.1) Seq.nil⟩
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
          d.2.2.2.1
          d.2.2.2.2.2.1 := by
    rintro ⟨s₀, l₀, s₁, ⟨e_rest, h_init, h_term, h_tight, h_consume⟩⟩
    rcases e_rest with ⟨init, trans⟩
    simp only at h_init
    subst h_init
    rfl
  rw [tsum_congr h_summand_eq]
  -- Step 4c.2: master Equiv between TraceDecomp l τ and the Σ-form.
  let e_master : ls.TraceDecomp l τ ≃
      Σ s₀ : State, Σ l₀ : Label, Σ s₁ : State,
        {e_rest : AlterSeq State Label //
          e_rest.trans.Terminates ∧ ls.IsTight e_rest ∧
          e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) ∧
          ls.consumeLabel l₀ (Seq.cons l τ) = some (ls.trace e_rest)} :=
    { toFun := fun ⟨s₀, l₀, s₁, e_rest, h_init, h_term, h_tight, h_consume⟩ =>
        ⟨s₀, l₀, s₁, ⟨e_rest, h_term, h_tight,
          h_init.trans (AlterSeq.endState_singleton_cons s₀ l₀ s₁).symm,
          h_consume⟩⟩
      invFun := fun ⟨s₀, l₀, s₁, e_rest, h_term, h_tight, h_init_endState, h_consume⟩ =>
        ⟨s₀, l₀, s₁, ⟨e_rest,
          h_init_endState.trans (AlterSeq.endState_singleton_cons s₀ l₀ s₁),
          h_term, h_tight, h_consume⟩⟩
      left_inv := fun ⟨_, _, _, ⟨_, _, _, _, _⟩⟩ => rfl
      right_inv := fun ⟨_, _, _, ⟨_, _, _, _, _⟩⟩ => rfl }
  let G : (Σ s₀ : State, Σ l₀ : Label, Σ s₁ : State,
      {e_rest : AlterSeq State Label //
        e_rest.trans.Terminates ∧ ls.IsTight e_rest ∧
        e_rest.init = (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) ∧
        ls.consumeLabel l₀ (Seq.cons l τ) = some (ls.trace e_rest)}) → ENNReal :=
    fun b => pe.init b.1 * pe.kernel ⟨b.1, Seq.nil⟩ (b.2.1, b.2.2.1) *
      (pe.continuationFrom ⟨b.1, Seq.cons (b.2.1, b.2.2.1) Seq.nil⟩
        (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
        b.2.2.2.1 b.2.2.2.2.1
  calc (∑' d : ls.TraceDecomp l τ,
          pe.init d.1 * pe.kernel ⟨d.1, Seq.nil⟩ (d.2.1, d.2.2.1) *
            (pe.continuationFrom ⟨d.1, Seq.cons (d.2.1, d.2.2.1) Seq.nil⟩
              (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)).probOf
              d.2.2.2.1 d.2.2.2.2.2.1)
      = ∑' d, G (e_master d) := by
        apply tsum_congr
        rintro ⟨_, _, _, ⟨_, _, _, _, _⟩⟩
        rfl
    _ = ∑' b, G b := e_master.tsum_eq G
    _ = _ := by
        rw [ENNReal.tsum_sigma']
        apply tsum_congr; intro s₀
        rw [ENNReal.tsum_sigma']
        apply tsum_congr; intro l₀
        rw [ENNReal.tsum_sigma']

/-- **`traceProbPMF` at nil equals 1**, mirroring `traceProb_nil_eq_one`.
The tight finite executions with empty trace bijection with initial states
(via `e ↦ e.init`), and each contributes `pe.init e.init`. The sum is
`pe.init.tsum_coe = 1`. -/
theorem LabelledSystem.traceProbPMF_nil_eq_one
    {State Label : Type} (ls : LabelledSystem State Label)
    (pe : PMFProbabilisticExecution ls.toSystem) :
    LabelledSystem.traceProbPMF ls pe Seq.nil = 1 := by
  unfold LabelledSystem.traceProbPMF
  let e_equiv : {e : AlterSeq State Label //
      e.trans.Terminates ∧ ls.trace e = Seq.nil ∧ ls.IsTight e} ≃ State :=
    { toFun := fun e => e.1.init
      invFun := fun s =>
        ⟨⟨s, Seq.nil⟩,
          Stream'.Seq.terminates_nil,
          ls.trace_init s,
          Or.inl Stream'.Seq.terminatedAt_nil⟩
      left_inv := by
        rintro ⟨⟨init, trans⟩, hTerm, hTrace, hTight⟩
        have h_trans_nil : trans = Seq.nil :=
          trans_nil_of_tight_trace_nil ls ⟨init, trans⟩ hTrace hTight
        subst h_trans_nil
        rfl
      right_inv := fun _ => rfl }
  have h_probOf : ∀ (a : {e : AlterSeq State Label //
      e.trans.Terminates ∧ ls.trace e = Seq.nil ∧ ls.IsTight e}),
      pe.probOf a.1 a.2.1 = pe.init a.1.init := by
    rintro ⟨⟨init, trans⟩, hTerm, hTrace, hTight⟩
    have h_trans_nil : trans = Seq.nil :=
      trans_nil_of_tight_trace_nil ls ⟨init, trans⟩ hTrace hTight
    subst h_trans_nil
    unfold PMFProbabilisticExecution.probOf
    change pe.init init * pe.probOfRemaining ⟨init, Seq.nil⟩
        ((Seq.nil : Seq (Label × State)).toList hTerm) = pe.init init
    have h_toList : (Seq.nil : Seq (Label × State)).toList hTerm = [] :=
      Stream'.Seq.toList_nil
    rw [h_toList]
    unfold PMFProbabilisticExecution.probOfRemaining
    simp
  rw [tsum_congr h_probOf]
  rw [show
      (∑' a : {e : AlterSeq State Label //
          e.trans.Terminates ∧ ls.trace e = Seq.nil ∧ ls.IsTight e},
        pe.init a.1.init) = ∑' s, pe.init s from e_equiv.tsum_eq pe.init]
  exact pe.init.tsum_coe

/-! ### Trace inclusion via probabilistic forward simulation (v4)

This section constructs an abstract probabilistic execution `pe_A` such
that, for every trace τ, `sys_C.traceProb pe_C τ = sys_A^w.traceProbPMF pe_A τ`.

The construction uses:
* `sys_A^w` — the weak-step closure of `sys_A`.
* `MatchingState` — a trajectory-relative record carrying a concrete
  prefix `e_C` plus the chain of abstract distributions sampled along
  the trajectory, with an `R`-invariant at the last (s_C, μ_A) pair.
* `MatchingStateKernel` — an unnormalised ENNReal-valued posterior over
  matching states, indexed by the abstract prefix.
* `Joint` — the joint space of (concrete, abstract) trajectories used to
  bridge `sys_C.traceProb` to `sys_A^w.traceProbPMF` via per-step
  γ-marginal identities. -/

namespace ProbabilisticForwardSimulation

variable {State_C State_A Label : Type}
variable {sys_C : LabelledSystem State_C Label} {sys_A : LabelledSystem State_A Label}
variable {R : State_C → PMF State_A → Prop}

/-! #### PMFRel decomposition and per-step γ-marginal identities -/

private structure PMFRelDecomp {α β : Type} (R : α → β → Prop)
    (μ : PMF α) (ν : PMF β) where
  γ : PMF (α × β)
  h_fst : PMF.map Prod.fst γ = μ
  h_snd : PMF.map Prod.snd γ = ν
  h_R : ∀ p ∈ γ.support, R p.1 p.2

/-- Extract `PMFRelDecomp` from a `PMFRel` witness. -/
private noncomputable def PMFRel.decomp {α β : Type} {R : α → β → Prop}
    {μ : PMF α} {ν : PMF β} (h : PMFRel R μ ν) :
    PMFRelDecomp R μ ν :=
  let h_spec := h.choose_spec
  { γ := h.choose
    h_fst := h_spec.1
    h_snd := h_spec.2.1
    h_R := h_spec.2.2 }

/-- **D3 marginal extraction (α-side)**: γ's first marginal applied at `a`
sums to μ(a). The standard "joint → marginal" identity made explicit. -/
private lemma PMFRelDecomp.fst_apply_eq_tsum
    {α β : Type} {R : α → β → Prop} {μ : PMF α} {ν : PMF β}
    (decomp : PMFRelDecomp R μ ν) (a : α) :
    μ a = ∑' b, decomp.γ (a, b) := by
  classical
  have h_μ : μ a = (PMF.map Prod.fst decomp.γ) a := by rw [decomp.h_fst]
  rw [h_μ, PMF.map_apply, ENNReal.tsum_prod']
  rw [show (∑' (a' : α) (b : β), (if a = a' then decomp.γ (a', b) else 0))
        = (∑' (b : β) (a' : α), (if a = a' then decomp.γ (a', b) else 0))
        from ENNReal.tsum_comm]
  refine tsum_congr (fun b => ?_)
  rw [tsum_eq_single a (fun a' h_ne => by
    simp only [if_neg (Ne.symm h_ne)])]
  simp

/-- **D3 marginal extraction (β-side)**: γ's second marginal applied at `b`
sums to ν(b). -/
private lemma PMFRelDecomp.snd_apply_eq_tsum
    {α β : Type} {R : α → β → Prop} {μ : PMF α} {ν : PMF β}
    (decomp : PMFRelDecomp R μ ν) (b : β) :
    ν b = ∑' a, decomp.γ (a, b) := by
  classical
  have h_ν : ν b = (PMF.map Prod.snd decomp.γ) b := by rw [decomp.h_snd]
  rw [h_ν, PMF.map_apply, ENNReal.tsum_prod']
  refine tsum_congr (fun a => ?_)
  rw [tsum_eq_single b (fun b' h_ne => by
    simp only [if_neg (Ne.symm h_ne)])]
  simp

/-- Total mass on `γ`'s support equals 1. (Trivial — γ is a PMF — but
useful as a named handle.) -/
private lemma PMFRelDecomp.γ_tsum_eq_one
    {α β : Type} {R : α → β → Prop} {μ : PMF α} {ν : PMF β}
    (decomp : PMFRelDecomp R μ ν) :
    ∑' p, decomp.γ p = 1 :=
  decomp.γ.tsum_coe

/-- **D3 per-step mass marginal (concrete side)**: for each concrete
sample `s_C'`, summing the joint γ-mass over all `(μ_A_next, s_A_final)`
outcomes gives `μ_C(s_C')`. The mass-conservation version of γ's first
marginal.

(General: works for both internal and external `l_C`; the proof only
needs `PMFRel γ`, not the internal/external classification — `ω =
sim.stepWitness h_R h_step` is the same in both cases.) -/
private lemma per_step_mass_marginal_concrete
    {sys_C : LabelledSystem State_C Label} {sys_A : LabelledSystem State_A Label}
    {R : State_C → PMF State_A → Prop}
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    {s_C : State_C} {μ_A : PMF State_A} (h_R : R s_C μ_A)
    {l : Label} {μ_C : PMF State_C} (h_step : sys_C.step s_C l μ_C)
    (s_C' : State_C) :
    ∑' (s_A_final : State_A) (μ_A_next : PMF State_A),
      (PMFRel.decomp (sim.stepWitness_pmfRel h_R h_step)).γ (s_C', μ_A_next) *
      μ_A_next s_A_final
    = μ_C s_C' := by
  set decomp := PMFRel.decomp (sim.stepWitness_pmfRel h_R h_step) with h_decomp_def
  rw [ENNReal.tsum_comm]
  rw [show (∑' (μ_A_next : PMF State_A) (s_A_final : State_A),
          decomp.γ (s_C', μ_A_next) * μ_A_next s_A_final)
        = ∑' μ_A_next : PMF State_A,
            decomp.γ (s_C', μ_A_next) *
            (∑' s_A_final : State_A, μ_A_next s_A_final) from by
      refine tsum_congr (fun μ_A_next => ?_)
      rw [ENNReal.tsum_mul_left]]
  simp_rw [PMF.tsum_coe, mul_one]
  exact (decomp.fst_apply_eq_tsum s_C').symm

/-- **D3 per-step mass marginal (abstract side)**: for each abstract end
state `s_A_final`, summing the joint γ-mass over all `(s_C', μ_A_next)`
outcomes gives `(sim.stepWitness h_R h_step).bind id` at `s_A_final` —
i.e., the abstract block's end-state mass.

This is the dual of `per_step_mass_marginal_concrete` and captures γ's
second marginal in mass-conservation form: the block's abstract end-state
distribution is the sum over all concrete-side states of γ-mediated
contributions.

(General: works for both internal and external `l_C`. For internal, by
`σ_internal_run_eq`, `(stepWitness).bind id = μ_A.bind σ_int.run`. For
external, the same identity holds via the σ_pre + hyper + σ_post chain.) -/
private lemma per_step_mass_marginal_abstract
    {sys_C : LabelledSystem State_C Label} {sys_A : LabelledSystem State_A Label}
    {R : State_C → PMF State_A → Prop}
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    {s_C : State_C} {μ_A : PMF State_A} (h_R : R s_C μ_A)
    {l : Label} {μ_C : PMF State_C} (h_step : sys_C.step s_C l μ_C)
    (s_A_final : State_A) :
    ∑' (s_C' : State_C) (μ_A_next : PMF State_A),
      (PMFRel.decomp (sim.stepWitness_pmfRel h_R h_step)).γ (s_C', μ_A_next) *
      μ_A_next s_A_final
    = ((sim.stepWitness h_R h_step).bind id) s_A_final := by
  set decomp := PMFRel.decomp (sim.stepWitness_pmfRel h_R h_step) with h_decomp_def
  rw [ENNReal.tsum_comm]
  -- ∑' μ_A_next, ∑' s_C', γ(s_C', μ_A_next) * μ_A_next(s_A_final)
  rw [show (∑' (μ_A_next : PMF State_A) (s_C' : State_C),
          decomp.γ (s_C', μ_A_next) * μ_A_next s_A_final)
        = ∑' μ_A_next : PMF State_A,
            (sim.stepWitness h_R h_step) μ_A_next * μ_A_next s_A_final from by
      refine tsum_congr (fun μ_A_next => ?_)
      rw [ENNReal.tsum_mul_right]
      congr 1
      exact (decomp.snd_apply_eq_tsum μ_A_next).symm]
  -- ∑' μ_A_next, ω(μ_A_next) * μ_A_next(s_A_final) = (ω.bind id)(s_A_final).
  rw [PMF.bind_apply]
  rfl

/-- **D3 per-step mass equation, external case**: identical to the internal
case at the algebraic level since `ω = sim.stepWitness h_R h_step` is
shared. The internal/external distinction only affects *how* the abstract
block's mass is realized (σ_int.run vs σ_pre + hyper + σ_post), not its
total mass at each `s_A_final`. -/
private lemma per_step_mass_marginal_concrete_external
    {sys_C : LabelledSystem State_C Label} {sys_A : LabelledSystem State_A Label}
    {R : State_C → PMF State_A → Prop}
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    {s_C : State_C} {μ_A : PMF State_A} (h_R : R s_C μ_A)
    {l : Label} {μ_C : PMF State_C} (h_step : sys_C.step s_C l μ_C)
    (_h_ext : ¬ sys_C.internal l) (s_C' : State_C) :
    ∑' (s_A_final : State_A) (μ_A_next : PMF State_A),
      (PMFRel.decomp (sim.stepWitness_pmfRel h_R h_step)).γ (s_C', μ_A_next) *
      μ_A_next s_A_final
    = μ_C s_C' :=
  per_step_mass_marginal_concrete sim h_R h_step s_C'


/-! #### `sys_A^w`: weak-step closure of `sys_A` (§2) -/

/-- **Weak-step closure**: a `LabelledSystem` whose strong-step relation
admits any μ reachable from `s` via a weak step from *some* surrounding
distribution `μ_A` with `s ∈ μ_A.support`. (Plan §2 specifies
`weakStep (PMF.pure s) l μ`; we generalise to "weakStep from any
μ_A containing s" so that sim's PMF-level witness directly supplies a
valid step, without needing a per-state refinement of weakStep.)

This permissiveness does not affect traceProb identities downstream:
the validity field is purely structural correctness of pe_A's scheduler.
The shared internal predicate makes `traceProbPMF` on `sys_A^w`
structurally identical to one on `sys_A`. -/
def weakClosure (sys_A : LabelledSystem State_A Label) :
    LabelledSystem State_A Label where
  init := sys_A.init
  step s l μ := ∃ μ_A : PMF State_A, s ∈ μ_A.support ∧ weakStep sys_A μ_A l μ
  internal := sys_A.internal

/-- Notation `sys ^w` for `weakClosure sys`. -/
scoped notation sys "^w" => weakClosure sys

/-! #### `MatchingState`: trajectory-relative matching record (§3.1) -/

/-- A matching state pairs a concrete prefix `e_C` with the chain of
abstract distributions `μ_A_chain` sampled along the same trajectory,
plus an `R`-invariant linking the last concrete state to the last
abstract distribution. -/
structure MatchingState
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (_h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init) where
  /-- The concrete prefix walked so far. -/
  e_C : AlterSeq State_C Label
  /-- Termination proof for the concrete prefix. -/
  e_C_term : e_C.trans.Terminates
  /-- The sequence of abstract distributions sampled along this
  trajectory: `μ_A_chain[k]` is the `μ_A_next` from which `s_A_k` was
  sampled at step k. -/
  μ_A_chain : List (PMF State_A)
  /-- Trajectory-relative `R`-invariant. When `μ_A_chain` is nonempty,
  asserts `R (e_C.endState e_C_term) (μ_A_chain.getLast _)`. The
  empty case is handled by `h_init_R` (passed through the structure
  parameters), so no obligation is needed here. -/
  h_R : ∀ h_nonempty : μ_A_chain ≠ [],
        R (e_C.endState e_C_term) (μ_A_chain.getLast h_nonempty)

namespace MatchingState

variable {sim : ProbabilisticForwardSimulation sys_C sys_A R}
variable {pe_C : ProbabilisticExecution sys_C.toSystem}
variable {μ_A_init : PMF State_A}
variable {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}

/-- `advance_pe_C_step`: advance a matching state by one pe_C step.
The advance applies uniformly regardless of label class (internal /
external). -/
noncomputable def advance_pe_C_step
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (l_C : Label) (s_C' : State_C) (μ_A_next : PMF State_A)
    (h_R_next : R s_C' μ_A_next) :
    MatchingState sim pe_C μ_A_init h_init_R where
  e_C := ⟨m.e_C.init, m.e_C.trans.append (Seq.cons (l_C, s_C') Seq.nil)⟩
  e_C_term := ⟨Nat.find m.e_C_term + 1,
    Stream'.Seq.terminatedAt_append_find m.e_C_term
      (show (Seq.cons (l_C, s_C') Seq.nil).TerminatedAt 1 from rfl)⟩
  μ_A_chain := m.μ_A_chain ++ [μ_A_next]
  h_R := by
    intro _h_ne
    -- `endState` of `e_C.append (cons (l_C, s_C') nil)` equals `s_C'`,
    -- by `AlterSeq.endState_append_singleton`.
    rw [AlterSeq.endState_append_singleton m.e_C m.e_C_term l_C s_C',
        List.getLast_append_singleton]
    exact h_R_next

end MatchingState

namespace MatchingState

variable {sim : ProbabilisticForwardSimulation sys_C sys_A R}
variable {pe_C : ProbabilisticExecution sys_C.toSystem}
variable {μ_A_init : PMF State_A}
variable {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}

/-- The "current" abstract distribution associated with a matching state:
either the last entry of `μ_A_chain`, or `μ_A_init` if the chain is empty.
This is the distribution from which the *next* abstract state would be
sampled along this trajectory. -/
noncomputable def current_μ_A
    (m : MatchingState sim pe_C μ_A_init h_init_R) : PMF State_A :=
  if h : m.μ_A_chain = [] then μ_A_init
  else m.μ_A_chain.getLast h

/-- The "current" concrete state associated with a matching state: the
end-state of `e_C`. The full result type is `State_C`. -/
noncomputable def current_s_C
    (m : MatchingState sim pe_C μ_A_init h_init_R) : State_C :=
  m.e_C.endState m.e_C_term

/-- A matching state has a "valid" `R`-witness if either:
* its `μ_A_chain` is non-empty (so the struct's `h_R` field applies), OR
* `μ_A_chain = []` and `e_C.trans = Seq.nil` and `e_C.init ∈ pe_C.init.support`
  (so `h_init_R` applies, with `e_C.endState = e_C.init`).

`fromAbstractPrefix` only places positive mass on matching states with
this property, so all proofs work within this fragment. -/
def has_valid_R
    (m : MatchingState sim pe_C μ_A_init h_init_R) : Prop :=
  m.μ_A_chain ≠ [] ∨
    (m.e_C.trans = Seq.nil ∧ m.e_C.init ∈ pe_C.init.support)

/-- For `m` with `has_valid_R`, extract the trajectory's R-witness
`R (m.current_s_C) (m.current_μ_A)`. -/
noncomputable def current_R
    {m : MatchingState sim pe_C μ_A_init h_init_R}
    (h_valid : m.has_valid_R) :
    R m.current_s_C m.current_μ_A := by
  unfold current_s_C current_μ_A
  classical
  rcases h_valid with h_nonempty | ⟨h_trans_nil, h_init_supp⟩
  · -- Non-empty chain case: use m.h_R.
    rw [dif_neg h_nonempty]
    exact m.h_R h_nonempty
  · -- Empty-chain case: μ_A_chain = [] (from h_init_R applicability),
    -- but `m.has_valid_R` only states e_C.trans = nil ∧ e_C.init ∈ support.
    -- However for the `current_μ_A` calc we need μ_A_chain = []. The
    -- has_valid_R definition's left disjunct (`m.μ_A_chain ≠ []`) was ruled
    -- out by being in the right disjunct only iff μ_A_chain = [].
    -- Actually has_valid_R right disjunct doesn't force μ_A_chain = [].
    -- We need an additional case-split.
    by_cases h_chain : m.μ_A_chain = []
    · rw [dif_pos h_chain]
      -- Now: R (m.e_C.endState m.e_C_term) μ_A_init.
      -- e_C.endState when trans = nil equals e_C.init.
      have h_endState : m.e_C.endState m.e_C_term = m.e_C.init := by
        have h_find : Nat.find m.e_C_term = 0 := by
          apply Nat.eq_zero_of_le_zero
          apply Nat.find_le
          rw [h_trans_nil]
          exact Stream'.Seq.terminatedAt_nil
        have h_stateAt : m.e_C.stateAt (Nat.find m.e_C_term) = some m.e_C.init := by
          rw [h_find]; rfl
        have h_endState_some :=
          AlterSeq.stateAt_find_eq_endState m.e_C m.e_C_term
        rw [h_stateAt] at h_endState_some
        exact (Option.some.inj h_endState_some).symm
      rw [h_endState]
      exact h_init_R m.e_C.init h_init_supp
    · -- m.μ_A_chain ≠ []: fall back to the first disjunct.
      rw [dif_neg h_chain]
      exact m.h_R h_chain

end MatchingState

/-! #### Step-witness extraction from `pe_C`'s scheduler validity -/

/-- Given a prefix `e_C` of `pe_C` with a `Terminates` witness, the
distribution `d` returned by `pe_C.scheduler.next e_C`, and a support
membership `(l, μ_C) ∈ d.support`, the scheduler's `valid` field
provides the corresponding step witness
`sys_C.step (e_C.endState e_C_term) l μ_C`. -/
theorem pe_C_step_witness
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (e_C : AlterSeq State_C Label) (e_C_term : e_C.trans.Terminates)
    (d : PMF (Label × PMF State_C))
    (h_d_eq : pe_C.scheduler.next e_C = some d)
    (l : Label) (μ_C : PMF State_C) (h_supp : (l, μ_C) ∈ d.support) :
    sys_C.toSystem.step (e_C.endState e_C_term) l μ_C :=
  pe_C.scheduler.valid e_C (Nat.find e_C_term) (e_C.endState e_C_term)
    (Nat.find_spec e_C_term) (AlterSeq.stateAt_find_eq_endState e_C e_C_term)
    d h_d_eq l μ_C h_supp

/-! #### `MatchingStateKernel` and `fromAbstractPrefix` (§3.2)

`MatchingStateKernel` is the unnormalised posterior over matching states
given an abstract prefix. `fromAbstractPrefix` defines this kernel
inductively on `history_A`'s transitions: the base case (empty `trans`)
places mass `μ_A_init(s_A_init) · pe_C.init(s_C_init)` on each initial
matching state whose `e_C.init = s_C_init`. The step case integrates
against a Bayesian step-weight (§3.2 step case formula). -/

/-- The matching-state kernel: an ENNReal-valued (unnormalised) measure
over matching states, indexed by an abstract prefix `history_A` together
with a `Terminates` witness. -/
abbrev MatchingStateKernel
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init) : Type :=
  (history_A : AlterSeq State_A Label) → history_A.trans.Terminates →
    MatchingState sim pe_C μ_A_init h_init_R → ENNReal

/-- The per-step Bayesian update factor (§3.2 step case): when
`pe_C.scheduler.next m_prev.e_C = some d`, sums over `(μ_C, s_C', μ_A_next)`
in γ's support of `d(l_k, μ_C) · γ(s_C', μ_A_next) · μ_A_next(s_A_k)` with
indicators forcing `m_new` to be `m_prev` advanced by `(l_k, s_C', μ_A_next)`.
When `pe_C.scheduler.next m_prev.e_C = none` or `m_prev` lacks a valid R,
returns 0. -/
noncomputable def step_weight
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (m_prev m_new : MatchingState sim pe_C μ_A_init h_init_R)
    (l_k : Label) (s_A_k : State_A) : ENNReal :=
  open Classical in
  if h_valid : m_prev.has_valid_R then
    match h_next : pe_C.scheduler.next m_prev.e_C with
    | none => 0
    | some d =>
        ∑' (μ_C : PMF State_C),
          d (l_k, μ_C) * (
            if h_supp : (l_k, μ_C) ∈ d.support then
              ∑' (s_C' : State_C) (μ_A_next : PMF State_A),
                (PMFRel.decomp (sim.stepWitness_pmfRel (m_prev.current_R h_valid)
                    (pe_C_step_witness pe_C m_prev.e_C m_prev.e_C_term d h_next l_k μ_C h_supp))
                ).γ (s_C', μ_A_next) * μ_A_next s_A_k *
                (if m_new.e_C = ⟨m_prev.e_C.init,
                    m_prev.e_C.trans.append (Seq.cons (l_k, s_C') Seq.nil)⟩ ∧
                  m_new.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next] then 1 else 0)
            else 0)
  else 0

/-- The base value of `fromAbstractPrefix` at the empty-trans prefix:
`μ_A_init(s_A_init) · pe_C.init(m.e_C.init)`, gated by indicators that
`m.e_C.trans = Seq.nil`, `m.μ_A_chain = []`, and `m.e_C.init ∈ pe_C.init.support`.
The `μ_A_init` factor matches the codebase's `probOf` convention
(multiplied by the initial mass at the start of pe_A.probOf). -/
noncomputable def fromAbstractPrefix_base
    (_sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (_h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (s_A_init : State_A)
    (m : MatchingState _sim pe_C μ_A_init _h_init_R) : ENNReal :=
  open Classical in
  if m.e_C.trans = Seq.nil ∧ m.μ_A_chain = [] ∧ m.e_C.init ∈ pe_C.init.support
  then μ_A_init s_A_init * pe_C.init m.e_C.init
  else 0

/-- **List-based recursion** for `fromAbstractPrefix`. Parameters:
* `s_A_init`: the head of `history_A` (`history_A.init`);
* `rev_trans`: the transitions of `history_A` in REVERSE order — i.e.,
  the most recent step is the HEAD;
* `m_new`: the matching state to evaluate at.

Recursion:
* `[]` (empty history): yields `fromAbstractPrefix_base`.
* `(l, s_A) :: rest` (last step is `(l, s_A)`, earlier prefix is reversed `rest`):
  `∑' m_prev, fromAbstractPrefix_list rest m_prev * step_weight m_prev m_new l s_A`. -/
noncomputable def fromAbstractPrefix_list
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (s_A_init : State_A) :
    List (Label × State_A) →
      MatchingState sim pe_C μ_A_init h_init_R → ENNReal
  | List.nil =>
      fun m => fromAbstractPrefix_base sim pe_C μ_A_init h_init_R s_A_init m
  | List.cons head rest =>
      fun m_new =>
        ∑' m_prev,
          fromAbstractPrefix_list sim pe_C μ_A_init h_init_R s_A_init rest m_prev *
          step_weight sim pe_C μ_A_init h_init_R m_prev m_new head.1 head.2

/-- The unnormalised posterior `fromAbstractPrefix history_A h_term m`:
defined as `fromAbstractPrefix_list` applied to `history_A.init` and
the reversed transitions of `history_A`. -/
noncomputable def fromAbstractPrefix
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init) :
    MatchingStateKernel sim pe_C μ_A_init h_init_R :=
  fun history_A h_term =>
    fromAbstractPrefix_list sim pe_C μ_A_init h_init_R history_A.init
      (history_A.trans.toList h_term).reverse

/-! #### `blockEmission_general` and `pe_A_emission_distribution` (§2) -/

/-- `blockEmission_general m d h_d_eq h_valid`: the per-matching-state
emission PMF, given that pe_C has not halted at `m.e_C` (i.e., scheduler
returned `some d`) and `m` has a valid R-witness. Per plan §2's
formula: sample `(l_C, μ_C)` from `d`; flatten γ to obtain an abstract
state distribution `γ.bind (fun (_, μ_A_next) => μ_A_next)`; sample
`s_A` from it; emit `(l_C, PMF.pure s_A)` (Dirac on the sampled
abstract state). -/
noncomputable def blockEmission_general
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (d : PMF (Label × PMF State_C))
    (h_d_eq : pe_C.scheduler.next m.e_C = some d)
    (h_valid : m.has_valid_R) :
    PMF (Label × PMF State_A) :=
  d.bind (fun (lμ : Label × PMF State_C) =>
    open Classical in
    if h_supp : (lμ.1, lμ.2) ∈ d.support then
      let h_step := pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq lμ.1 lμ.2
                      (by simpa using h_supp)
      let γ := (PMFRel.decomp (sim.stepWitness_pmfRel (m.current_R h_valid) h_step)).γ
      -- Sample s_A from γ.bind (fun (_, μ_A_next) => μ_A_next); emit Dirac on s_A.
      (γ.bind (fun p => p.2)).map (fun s_A => (lμ.1, PMF.pure s_A))
    else
      -- Outside support (mass 0 anyway): pick any deterministic value.
      PMF.pure (lμ.1, PMF.pure sys_A.init))

/-- **Per-matching-state emission**: the `PMF (Option (Label × PMF State_A))`
that pe_A would emit if we *knew* the matching state were exactly `m`.

* If `m` has valid R and `pe_C.scheduler.next m.e_C = some d`:
  emit `(blockEmission_general m d _ _).map some` — sample a block step.
* Otherwise (m lacks valid R, or pe_C has halted at m.e_C):
  emit `PMF.pure none` (halt). -/
noncomputable def pe_A_emit_at_state
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R) :
    PMF (Option (Label × PMF State_A)) :=
  open Classical in
  if h_valid : m.has_valid_R then
    match h_next : pe_C.scheduler.next m.e_C with
    | none => PMF.pure none
    | some d => (blockEmission_general m d h_next h_valid).map some
  else PMF.pure none

/-- The `PMF (Option (Label × PMF State_A))` emitted by pe_A's scheduler
at `history_A`. Aggregates over the matching-state posterior:
* Compute the unnormalised matching-state measure `m_kernel = fromAbstractPrefix`.
* If its total mass is positive and finite, normalise to get a PMF over
  matching states, then `bind` with `pe_A_emit_at_state`.
* Otherwise (zero or infinite total mass, or non-terminating history_A):
  fall back to `PMF.pure none`. -/
noncomputable def pe_A_emission_distribution
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (history_A : AlterSeq State_A Label) :
    PMF (Option (Label × PMF State_A)) :=
  open Classical in
  if h_term : history_A.trans.Terminates then
    let m_kernel := fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A h_term
    if h0 : (∑' m, m_kernel m) ≠ 0 then
      if hFin : (∑' m, m_kernel m) ≠ ⊤ then
        (PMF.normalize m_kernel h0 hFin).bind pe_A_emit_at_state
      else PMF.pure none
    else PMF.pure none
  else PMF.pure none

/-! #### `pe_A` as a `PMFProbabilisticExecution sys_A^w` -/

/-- The abstract probabilistic execution `pe_A` constructed from the
simulation data, operating over `sys_A^w` (the weak-step closure). -/
noncomputable def pe_A_of_simulation
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init) :
    PMFProbabilisticExecution (sys_A^w).toSystem where
  init := μ_A_init
  scheduler :=
    { next := pe_A_emission_distribution sim pe_C μ_A_init h_init_R
      valid := by sorry }

/-! #### Mass-conservation invariant on `fromAbstractPrefix` (§3.2) -/

/-- **Mass-conservation invariant**: the total mass of the matching-state
posterior at `history_A` equals `pe_A.probOf history_A`.

This invariant is proved by induction on `history_A.trans.toList`-length,
interleaved with `m_dist_posterior_predictive` (§9.3) — at step k+1, this
invariant follows from m_dist_posterior_predictive at step k, and
m_dist_posterior_predictive at step k+1 uses this invariant at step k. -/
theorem fromAbstractPrefix_mass_conservation
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (history_A : AlterSeq State_A Label) (h_term : history_A.trans.Terminates) :
    (∑' m, fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A h_term m) =
      (pe_A_of_simulation sim pe_C μ_A_init h_init_R).probOf
        history_A h_term :=
  sorry

/-! #### Joint kernel, joint mass, joint marginals (§5, §8)

The joint kernel is the per-step mass at `(l, s_C, s_A)` given a
matching state `m`:
  `joint_kernel m l s_C s_A
    := ∑' (μ_C, μ_A_next), d_m(l, μ_C) · γ_{m,(l,μ_C)}(s_C, μ_A_next) · μ_A_next(s_A)`
where `d_m = pe_C.scheduler.next m.e_C` (some `d_m` when pe_C has not
halted), and `γ_{m, (l, μ_C)}` is the joint distribution from sim's witness
at `m`'s R-coupling.

`joint_mass(e_C, e_A) := pe_C.init(e_C.init) · μ_A_init(e_A.init) ·
∏_k joint_kernel(m_k, l_k, s_C_k, s_A_k)`, where `m_k` is the matching
state at step k (advanced from `m_0` by the prior trajectory). -/

/-- The per-step joint kernel, parameterised by the matching state `m`.
Returns 0 when `m` lacks an R-witness, or `pe_C.scheduler.next m.e_C = none`
(pe_C has halted at this prefix), or `(l, μ_C) ∉ d.support`. -/
noncomputable def joint_kernel
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (l : Label) (s_C : State_C) (s_A : State_A) : ENNReal :=
  open Classical in
  if h_valid : m.has_valid_R then
    match h_next : pe_C.scheduler.next m.e_C with
    | none => 0
    | some d =>
        ∑' (μ_C : PMF State_C),
          d (l, μ_C) * (
            if h_supp : (l, μ_C) ∈ d.support then
              ∑' (μ_A_next : PMF State_A),
                (PMFRel.decomp (sim.stepWitness_pmfRel (m.current_R h_valid)
                    (pe_C_step_witness pe_C m.e_C m.e_C_term d h_next l μ_C h_supp))
                ).γ (s_C, μ_A_next) * μ_A_next s_A
            else 0)
  else 0

/-- **Per-step joint marginal over `s_A` (§5)**: summing `joint_kernel`
over the abstract end-state recovers `pe_C`'s per-step kernel. Requires
`m.has_valid_R` so the R-witness for sim's stepWitness exists. -/
theorem joint_kernel_marginal_s_A
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (h_valid : m.has_valid_R)
    (l : Label) (s_C : State_C) :
    (∑' s_A, joint_kernel m l s_C s_A) =
      pe_C.kernel m.e_C (l, s_C) :=
  -- Proof outline (~50-80 lines): under h_valid, unfold both sides;
  -- when pe_C.scheduler.next m.e_C = none, both are 0; otherwise
  -- swap ∑' s_A and ∑' μ_C, apply per_step_mass_marginal_concrete
  -- to compute ∑' (s_A) (μ_A_next), γ(s_C, μ_A_next) * μ_A_next s_A
  -- = μ_C s_C; then identify the result with pe_C.kernel via
  -- the bind/map expansion.
  sorry

/-- **`per_state_kernel m l s_A`**: the matching-state-conditional pe_A
emission kernel at `m`, marginalising the joint γ over the next concrete
state. Equals the joint kernel's `s_C`-marginal. Definition deferred to
match `joint_kernel`'s concretization. -/
noncomputable def per_state_kernel
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (l : Label) (s_A : State_A) : ENNReal :=
  ∑' s_C, joint_kernel m l s_C s_A

/-- **Per-step joint marginal over `s_C` (§5)**: by definition,
`per_state_kernel m l s_A = ∑' s_C, joint_kernel m l s_C s_A`. -/
theorem joint_kernel_marginal_s_C
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (l : Label) (s_A : State_A) :
    (∑' s_C, joint_kernel m l s_C s_A) =
      per_state_kernel m l s_A :=
  rfl

/-! #### `m_dist_posterior_predictive` (§9.3 — the central work item)

The heart of the proof. Links pe_A's `m_kernel`-aggregated kernel at
`history_A_{k+1}` to the joint kernel's abstract marginal at step k,
yielding `pe_A.probOf history_A_{k+1}`. Proved by induction on
`history_A.trans` length, interleaved with mass conservation. -/

/-- **`m_dist_posterior_predictive` (§9.3, unnormalised form)**: the
matching-state-aggregated `per_state_kernel` value at step k equals
`pe_A.probOf` at the extended history. -/
theorem m_dist_posterior_predictive
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (history_A_k : AlterSeq State_A Label) (h_term_k : history_A_k.trans.Terminates)
    (l : Label) (s_A : State_A) :
    (∑' m, fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A_k h_term_k m *
      per_state_kernel m l s_A) =
    (pe_A_of_simulation sim pe_C μ_A_init h_init_R).probOf
      ⟨history_A_k.init, history_A_k.trans.append (Seq.cons (l, s_A) Seq.nil)⟩
      ⟨Nat.find h_term_k + 1,
        Stream'.Seq.terminatedAt_append_find h_term_k
          (show (Seq.cons (l, s_A) Seq.nil).TerminatedAt 1 from rfl)⟩ :=
  sorry

/-! #### Joint-space marginals (§9.4, §9.5)

Once `joint_kernel` and `joint_mass` are defined, the two marginal
identities bridge `pe_C.probOf` and `pe_A.probOf` to a shared joint mass
quantity, giving the trace coupling by tsum bijection. -/

/-- **Joint mass**: `joint_mass e_C e_A` is the total probability of a
joint (concrete, abstract) trajectory whose concrete part is `e_C` and
abstract part is `e_A`, integrated over the γ-sampled abstract
distributions along the path. Defined as
  `pe_C.init e_C.init * μ_A_init e_A.init * ∏_k joint_kernel(m_k, l_k, s_C_k, s_A_k)`
where `m_k` is the matching state at step k (a γ-positive integration
over prior `μ_A_chain` choices implicit in `joint_kernel`'s inner sum).

The concrete construction recurses on the joint trajectory's transitions
list, accumulating `joint_kernel` factors and threading matching-state
advances. -/
noncomputable def joint_mass
    (_sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (_pe_C : ProbabilisticExecution sys_C.toSystem)
    (_μ_A_init : PMF State_A)
    (_h_init_R : ∀ s_C ∈ _pe_C.init.support, R s_C _μ_A_init)
    (_e_C : AlterSeq State_C Label) (_e_C_term : _e_C.trans.Terminates)
    (_e_A : AlterSeq State_A Label) (_e_A_term : _e_A.trans.Terminates) : ENNReal :=
  sorry

/-- **§9.4**: marginalising the joint over `e_A`'s state samples
recovers `pe_C.probOf e_C`. Proven by composing per-step
`joint_kernel_marginal_s_A` across the trajectory. -/
theorem joint_marginalises_to_pe_C
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (e_C : AlterSeq State_C Label) (e_C_term : e_C.trans.Terminates)
    (init_A : State_A) :
    -- Summing joint_mass over (e_A : AlterSeq) with |e_A.trans| = |e_C.trans|
    -- and labels matching step-by-step yields pe_C.probOf e_C.
    -- The summation domain: matching e_A's with init_A and proper labels.
    (∑' (e_A : {e_A : AlterSeq State_A Label //
                ∃ h_term : e_A.trans.Terminates,
                  e_A.init = init_A ∧
                  (e_A.trans.toList h_term).length = (e_C.trans.toList e_C_term).length ∧
                  ∀ k h₁ h₂, ((e_A.trans.toList h_term).get ⟨k, h₁⟩).1 =
                             ((e_C.trans.toList e_C_term).get ⟨k, h₂⟩).1}),
        joint_mass sim pe_C μ_A_init h_init_R e_C e_C_term e_A.1 e_A.2.choose) =
      pe_C.probOf e_C e_C_term :=
  sorry

/-- **§9.5**: marginalising the joint over `e_C`'s state samples
recovers `pe_A.probOf e_A`. Proven by induction on `e_A.trans` length,
using `m_dist_posterior_predictive` at each step. -/
theorem joint_marginalises_to_pe_A
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (e_A : AlterSeq State_A Label) (e_A_term : e_A.trans.Terminates) :
    (∑' (e_C : {e_C : AlterSeq State_C Label //
                ∃ h_term : e_C.trans.Terminates,
                  e_C.init ∈ pe_C.init.support ∧
                  (e_C.trans.toList h_term).length = (e_A.trans.toList e_A_term).length ∧
                  ∀ k h₁ h₂, ((e_C.trans.toList h_term).get ⟨k, h₁⟩).1 =
                             ((e_A.trans.toList e_A_term).get ⟨k, h₂⟩).1}),
        joint_mass sim pe_C μ_A_init h_init_R e_C.1 e_C.2.choose e_A e_A_term) =
      (pe_A_of_simulation sim pe_C μ_A_init h_init_R).probOf e_A e_A_term :=
  sorry

/-! #### Top-level trace inclusion theorem (§1) -/

/-- **Trace inclusion (v4)**: for every probabilistic execution `pe_C` of
`sys_C` and every initial abstract distribution `μ_A_init` `R`-related
pointwise to `pe_C`'s initial states, there is an abstract probabilistic
execution `pe_A` of `sys_A^w` matching `pe_C`'s trace probability at
every trace τ.

**Proof structure (per §8)**:
1. Unfold both sides as tsums over tight finite executions.
2. Define the joint space `Joint(τ)` and joint_mass.
3. Apply `joint_marginalises_to_pe_C`: sum over e_A reproduces pe_C.probOf(e_C).
4. Apply `joint_marginalises_to_pe_A`: sum over e_C reproduces pe_A.probOf(e_A).
5. Compose: both sides equal ∑' Joint(τ) joint_mass. -/
theorem traceInclusion
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init) :
    ∃ pe_A : PMFProbabilisticExecution (sys_A^w).toSystem,
      ∀ τ : Seq Label,
        sys_C.traceProb pe_C τ = (sys_A^w).traceProbPMF pe_A τ :=
  ⟨pe_A_of_simulation sim pe_C μ_A_init h_init_R, by sorry⟩

end ProbabilisticForwardSimulation

end PLTS
