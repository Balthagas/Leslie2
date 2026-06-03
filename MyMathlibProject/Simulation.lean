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

/-- **Seq-splitting helper**: any terminating `Seq` whose `toList` is
non-empty can be expressed as `previous.append (cons last nil)` for some
terminating `previous` and last element `last`. Used for induction on
`AlterSeq` length: lets us peel off the most recent transition.

The construction takes `previous := ofList (toList.dropLast)` and `last :=
toList.getLast h_nonempty`; correctness follows from `dropLast ++ [getLast]
= toList`, `ofList_append`, and `ofList_toList`. -/
theorem exists_split_last
    {α : Type} (s : Seq α) (h_term : s.Terminates)
    (h_nonempty : s.toList h_term ≠ []) :
    ∃ (previous : Seq α) (last : α) (h_prev : previous.Terminates),
      s = previous.append (Seq.cons last Seq.nil) ∧
      previous.toList h_prev = (s.toList h_term).dropLast ∧
      last = (s.toList h_term).getLast h_nonempty := by
  let toL := s.toList h_term
  let lst := toL.getLast h_nonempty
  let prevList := toL.dropLast
  let previous : Seq α := Stream'.Seq.ofList prevList
  have h_prev : previous.Terminates := Stream'.Seq.terminates_ofList prevList
  have h_split : toL = prevList ++ [lst] :=
    (List.dropLast_append_getLast h_nonempty).symm
  refine ⟨previous, lst, h_prev, ?_, ?_, rfl⟩
  · -- s = previous.append (cons lst nil)
    -- s = ofList (toList s h_term) = ofList (prevList ++ [lst])
    --   = (ofList prevList).append (ofList [lst])
    --   = previous.append (cons lst (ofList []))
    --   = previous.append (cons lst nil)
    have h_s_eq : s = Stream'.Seq.ofList toL := (Stream'.Seq.ofList_toList s h_term).symm
    rw [h_s_eq, h_split, Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons,
        Stream'.Seq.ofList_nil]
  · -- previous.toList h_prev = prevList = dropLast (toL).
    exact Stream'.Seq.toList_ofList prevList

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

/-- Auxiliary: `foldl (cons-extend)` over `xs` from an initial Seq `init`
gives `init.append (Seq.ofList xs)`. Used by `probOf_append_singleton`. -/
private theorem foldl_seq_app_eq_ofList (xs : List (Label × State)) (init : Seq (Label × State)) :
    xs.foldl (fun acc hd => acc.append (Seq.cons hd Seq.nil)) init =
    init.append (Stream'.Seq.ofList xs) := by
  induction xs generalizing init with
  | nil =>
    simp [Stream'.Seq.ofList_nil, Stream'.Seq.append_nil]
  | cons hd rest ih =>
    change List.foldl _ (init.append (Seq.cons hd Seq.nil)) rest = _
    rw [ih, Stream'.Seq.ofList_cons, Stream'.Seq.append_assoc]
    congr 1
    show (Seq.cons hd Seq.nil).append (Stream'.Seq.ofList rest) =
      Seq.cons hd (Stream'.Seq.ofList rest)
    rw [Stream'.Seq.cons_append, Stream'.Seq.nil_append]

/-- **End-step factorisation for `probOfRemaining`** (plan v4.1 §9.3 sub-lemma C):
appending a transition `last` at the end multiplies by `pe.kernel`
at the prefix accumulated after walking through `xs`. -/
theorem probOfRemaining_append_singleton (pe : PMFProbabilisticExecution sys)
    (pre : AlterSeq State Label) (xs : List (Label × State)) (last : Label × State) :
    pe.probOfRemaining pre (xs ++ [last]) =
      pe.probOfRemaining pre xs *
        pe.kernel ⟨pre.init,
          xs.foldl (fun acc hd => acc.append (Seq.cons hd Seq.nil)) pre.trans⟩ last := by
  induction xs generalizing pre with
  | nil =>
    -- xs = []: LHS = probOfRemaining pre [last]. RHS = probOfRemaining pre [] * pe.kernel pre last.
    -- probOfRemaining pre [] = 1 (foldl on []).
    -- probOfRemaining pre [last] = pe.kernel pre last (foldl on [last] step).
    -- xs.foldl on [] reduces to pre.trans, so ⟨pre.init, pre.trans⟩ = pre.
    simp only [List.nil_append, List.foldl]
    rw [probOfRemaining_cons]
    unfold probOfRemaining
    simp only [List.foldl]
    rcases pre with ⟨init, trans⟩
    change pe.kernel ⟨init, trans⟩ last * 1 = 1 * pe.kernel ⟨init, trans⟩ last
    ring
  | cons hd rest ih =>
    -- xs = hd :: rest. (hd :: rest) ++ [last] = hd :: (rest ++ [last]).
    -- LHS: probOfRemaining pre (hd :: (rest ++ [last]))
    --   = pe.kernel pre hd * probOfRemaining ⟨pre.init, pre.trans.append (cons hd nil)⟩
    --     (rest ++ [last])
    --       (by probOfRemaining_cons)
    --   = pe.kernel pre hd * (probOfRemaining ⟨pre.init, pre.trans.append (cons hd nil)⟩ rest *
    --       pe.kernel ⟨pre.init, walked-from-(cons hd nil)⟩ last)
    --       (by IH on rest)
    -- RHS: probOfRemaining pre (hd :: rest) * pe.kernel ⟨pre.init, walked-from-(hd::rest)⟩ last
    --   = (pe.kernel pre hd * probOfRemaining ⟨pre.init, ...⟩ rest) * pe.kernel ⟨...⟩ last
    --       (by probOfRemaining_cons)
    -- Equal by associativity and noting walking from (cons hd nil) for rest =
    -- walking from (hd :: rest) original.
    show pe.probOfRemaining pre ((hd :: rest) ++ [last]) = _
    rw [show ((hd :: rest) ++ [last] : List _) = hd :: (rest ++ [last]) from rfl,
        probOfRemaining_cons, probOfRemaining_cons]
    rw [ih ⟨pre.init, pre.trans.append (Seq.cons hd Seq.nil)⟩]
    -- After rw [ih]: pe.kernel pre hd * (probOfRem ... rest
    --                                 * pe.kernel ⟨_, foldl ... extended rest⟩ last).
    -- After probOfRemaining_cons on RHS: (pe.kernel pre hd * probOfRem ... rest)
    --                                    * pe.kernel ⟨_, foldl ... pre (hd :: rest)⟩ last.
    -- Need: foldl ... extended rest = foldl ... pre.trans (hd :: rest),
    -- which is definitional via List.foldl.
    simp only [List.foldl, mul_assoc]

/-- **End-step factorisation for `pe.probOf`** (plan v4.1 §9.3 sub-lemma C):
appending a transition `last` at the end of `history` multiplies `pe.probOf`
by `pe.kernel history last`. -/
theorem probOf_append_singleton (pe : PMFProbabilisticExecution sys)
    (init : State) (trans : Seq (Label × State)) (h_term : trans.Terminates)
    (last : Label × State) :
    pe.probOf ⟨init, trans.append (Seq.cons last Seq.nil)⟩
        ⟨Nat.find h_term + 1, Stream'.Seq.terminatedAt_append_find h_term
          (show (Seq.cons last Seq.nil).TerminatedAt 1 from rfl)⟩ =
      pe.probOf ⟨init, trans⟩ h_term *
        pe.kernel ⟨init, trans⟩ last := by
  unfold PMFProbabilisticExecution.probOf
  -- (trans.append (cons last nil)).toList = trans.toList h_term ++ [last]
  have h_toList : (trans.append (Seq.cons last Seq.nil)).toList
      ⟨Nat.find h_term + 1, Stream'.Seq.terminatedAt_append_find h_term
        (show (Seq.cons last Seq.nil).TerminatedAt 1 from rfl)⟩ =
      trans.toList h_term ++ (Seq.cons last Seq.nil).toList
        ⟨1, show (Seq.cons last Seq.nil).TerminatedAt 1 from rfl⟩ :=
    Stream'.Seq.toList_append trans (Seq.cons last Seq.nil) h_term _ _
  have h_singleton_toList : (Seq.cons last Seq.nil).toList
      ⟨1, show (Seq.cons last Seq.nil).TerminatedAt 1 from rfl⟩ = [last] := by
    rw [Stream'.Seq.toList_cons]
    simp [Stream'.Seq.toList_nil]
  rw [h_toList, h_singleton_toList]
  rw [probOfRemaining_append_singleton]
  -- Now: pe.init init * (probOfRemaining ⟨init, nil⟩ (trans.toList h_term) *
  --        pe.kernel ⟨init, foldl ... Seq.nil (trans.toList h_term)⟩ last)
  --    = pe.init init * probOfRemaining ⟨init, nil⟩ (trans.toList h_term)
  --                   * pe.kernel ⟨init, trans⟩ last
  -- The foldl form simplifies via foldl_seq_append_eq_ofList + ofList_toList:
  -- foldl ... Seq.nil (trans.toList h_term) = Seq.nil.append (Seq.ofList (trans.toList h_term))
  --   = Seq.ofList (trans.toList h_term)  [by nil_append]
  --   = trans  [by ofList_toList]
  rw [foldl_seq_app_eq_ofList, Stream'.Seq.nil_append, Stream'.Seq.ofList_toList]
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
admits any `μ` appearing in the support of a PMF (PMF State_A) witness
`ω` whose aggregated bind is reached by a weak step from a containing
distribution `μ_A`. This matches what sim's `stepWitness` provides:
`weakStep μ_A l (ω.bind id)` with `μ ∈ ω.support`.

Plan §2's `weakStep (PMF.pure s) l μ` is strictly stronger (Dirac
source). The relaxed form here is provable from sim and preserves
the trace probability identities (the validity field is structural
correctness of pe_A's scheduler; trace probabilities depend on the
kernel via the scheduler, not on the precise weakClosure relation). -/
def weakClosure (sys_A : LabelledSystem State_A Label) :
    LabelledSystem State_A Label where
  init := sys_A.init
  step s l μ := ∃ (μ_A : PMF State_A) (ω : PMF (PMF State_A)),
    s ∈ μ_A.support ∧ μ ∈ ω.support ∧
    (weakTau sys_A μ_A (ω.bind id) ∨ weakStep sys_A μ_A l (ω.bind id))
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
end-state of `e_C`. Defined as `abbrev` so it reduces definitionally
(needed for `sim.stepWitness` typeclass-unification at use sites). -/
noncomputable abbrev current_s_C
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

/-- **MatchingState extensionality (data-only)**: two matching states with
equal `e_C` and `μ_A_chain` fields are equal. The `e_C_term` and `h_R` fields
are Prop, hence definitionally equal by Lean 4's proof irrelevance once the
data fields align. -/
private theorem MatchingState.ext_of_data
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    {m1 m2 : MatchingState sim pe_C μ_A_init h_init_R}
    (h_e_C : m1.e_C = m2.e_C) (h_chain : m1.μ_A_chain = m2.μ_A_chain) :
    m1 = m2 := by
  cases m1 with
  | mk e_C1 term1 chain1 hR1 =>
    cases m2 with
    | mk e_C2 term2 chain2 hR2 =>
      simp only at h_e_C h_chain
      subst h_e_C
      subst h_chain
      rfl

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

/-- **`step_weight_at_d`** — d-explicit form of `step_weight` (mirrors the
`joint_kernel_at_d` / `per_state_kernel_at_d` split). Taking `d` and the
equation `h_d_eq : pe_C.scheduler.next m_prev.e_C = some d` as explicit
arguments avoids the dependent-match pattern that would otherwise live
inside `step_weight`. -/
noncomputable def step_weight_at_d
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (m_prev m_new : MatchingState sim pe_C μ_A_init h_init_R)
    (d : PMF (Label × PMF State_C))
    (h_d_eq : pe_C.scheduler.next m_prev.e_C = some d)
    (h_valid : m_prev.has_valid_R)
    (l_k : Label) (s_A_k : State_A) : ENNReal :=
  ∑' (μ_C : PMF State_C),
    d (l_k, μ_C) * (
      open Classical in
      if h_supp : (l_k, μ_C) ∈ d.support then
        ∑' (s_C' : State_C) (μ_A_next : PMF State_A),
          (PMFRel.decomp (sim.stepWitness_pmfRel (m_prev.current_R h_valid)
              (pe_C_step_witness pe_C m_prev.e_C m_prev.e_C_term d h_d_eq l_k μ_C h_supp))
          ).γ (s_C', μ_A_next) * μ_A_next s_A_k *
          (if m_new.e_C = ⟨m_prev.e_C.init,
              m_prev.e_C.trans.append (Seq.cons (l_k, s_C') Seq.nil)⟩ ∧
            m_new.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next] then 1 else 0)
      else 0)

/-- The per-step Bayesian update factor (§3.2 step case): when
`pe_C.scheduler.next m_prev.e_C = some d`, sums over `(μ_C, s_C', μ_A_next)`
in γ's support of `d(l_k, μ_C) · γ(s_C', μ_A_next) · μ_A_next(s_A_k)` with
indicators forcing `m_new` to be `m_prev` advanced by `(l_k, s_C', μ_A_next)`.
When `pe_C.scheduler.next m_prev.e_C = none` or `m_prev` lacks a valid R,
returns 0.

Thin wrapper over `step_weight_at_d` (parallels `joint_kernel`'s wrapper
over `joint_kernel_at_d`). The `isSome`/`get` pattern avoids dependent
matches on `Option`, keeping downstream proofs tractable. -/
noncomputable def step_weight
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (m_prev m_new : MatchingState sim pe_C μ_A_init h_init_R)
    (l_k : Label) (s_A_k : State_A) : ENNReal :=
  open Classical in
  if h_valid : m_prev.has_valid_R then
    if h_some : (pe_C.scheduler.next m_prev.e_C).isSome then
      step_weight_at_d sim pe_C μ_A_init h_init_R m_prev m_new
        ((pe_C.scheduler.next m_prev.e_C).get h_some)
        (Option.eq_some_of_isSome h_some) h_valid l_k s_A_k
    else 0
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
emission PMF, given that pe_C has not halted at `m.e_C` and `m` has a
valid R-witness. Sample `(l_C, μ_C)` from `d`; sample `μ_A_next` from
sim's `ω` (the PMF (PMF State_A) witnessing the abstract weak step);
emit `(l_C, μ_A_next)`.

Note: this deviates from plan §2's Dirac formula in favour of emitting
the full sim-witnessed `μ_A_next`. Reason: pe_A's `valid` field requires
`sys_A^w.step s l μ` for each emitted `(l, μ)`; sim's witness gives a
weakStep at the PMF level (between PMFs, not Diracs). Emitting general
PMFs lets the validity proof go through directly. -/
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
      let ω := sim.stepWitness (m.current_R h_valid) h_step
      ω.map (fun μ_A_next => (lμ.1, μ_A_next))
    else
      -- Outside support (mass 0 anyway): pick any deterministic value.
      PMF.pure (lμ.1, PMF.pure sys_A.init))

/-- **Flat form for `blockEmission_general (l, μ)`**: avoids the nested
let-bindings of `blockEmission_general` by expressing the value at a
specific `(l, μ)` as a single tsum over `μ_C` (with `l' = l` selected). -/
private theorem blockEmission_general_apply_eq
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (d : PMF (Label × PMF State_C))
    (h_d_eq : pe_C.scheduler.next m.e_C = some d)
    (h_valid : m.has_valid_R)
    (l : Label) (μ : PMF State_A) :
    blockEmission_general m d h_d_eq h_valid (l, μ) =
    ∑' μ_C : PMF State_C, d (l, μ_C) *
      (open Classical in
       if h_supp : (l, μ_C) ∈ d.support then
        sim.stepWitness (m.current_R h_valid)
          (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq l μ_C h_supp) μ
      else 0) := by
  classical
  unfold blockEmission_general
  rw [PMF.bind_apply]
  rw [ENNReal.tsum_prod']
  -- Show l' ≠ l contributes 0; then for l' = l reduce.
  rw [tsum_eq_single l (fun l' h_ne_l => ?_)]
  swap
  · -- l' ≠ l: ∑' μ_C, d (l', μ_C) * (branch (l', μ_C)) (l, μ) = 0
    apply ENNReal.tsum_eq_zero.mpr
    intro μ_C
    by_cases h_supp : (l', μ_C) ∈ d.support
    · simp only [dif_pos h_supp]
      -- (ω.map (l', ·)) (l, μ) = ∑' a, if (l, μ) = (l', a) then ω a else 0 = 0 (l ≠ l').
      rw [PMF.map_apply]
      -- Show the product is 0 by showing the right factor (inner sum) is 0.
      apply mul_eq_zero_of_ne_zero_imp_eq_zero
      intro _
      apply ENNReal.tsum_eq_zero.mpr
      intro a
      have h_pair_ne : (l, μ) ≠ (l', a) :=
        fun h_eq => h_ne_l (Prod.mk.inj h_eq).1.symm
      rw [if_neg h_pair_ne]
    · simp only [dif_neg h_supp]
      have h_d_zero : d (l', μ_C) = 0 := by
        rw [PMF.mem_support_iff] at h_supp; push Not at h_supp; exact h_supp
      rw [h_d_zero, zero_mul]
  -- l' = l case.
  refine tsum_congr (fun μ_C => ?_)
  by_cases h_supp : (l, μ_C) ∈ d.support
  · simp only [dif_pos h_supp]
    congr 1
    -- (ω.map (l, ·)) (l, μ) = ω μ
    rw [PMF.map_apply]
    rw [tsum_eq_single μ (fun a h_ne_a => by
      have : (l, μ) ≠ (l, a) := fun h => h_ne_a (Prod.mk.inj h).2.symm
      simp [this])]
    simp
  · simp only [dif_neg h_supp]
    -- d (l, μ_C) = 0
    have h_d_zero : d (l, μ_C) = 0 := by
      rw [PMF.mem_support_iff] at h_supp; push Not at h_supp; exact h_supp
    rw [h_d_zero, zero_mul, zero_mul]

/-- **Per-matching-state emission**: the `PMF (Option (Label × PMF State_A))`
that pe_A would emit if we *knew* the matching state were exactly `m`.

* If `m` has valid R and `pe_C.scheduler.next m.e_C = some d`:
  emit `(blockEmission_general m d _ _).map some` — sample a block step.
* Otherwise (m lacks valid R, or pe_C has halted at m.e_C):
  emit `PMF.pure none` (halt).

Implemented via `Option.isSome` + `Option.get` (avoids match-with-binder;
makes the support extraction proof go through). -/
noncomputable def pe_A_emit_at_state
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R) :
    PMF (Option (Label × PMF State_A)) :=
  open Classical in
  if h_valid : m.has_valid_R then
    if h_some : (pe_C.scheduler.next m.e_C).isSome then
      (blockEmission_general m ((pe_C.scheduler.next m.e_C).get h_some)
        (Option.eq_some_of_isSome h_some) h_valid).map some
    else PMF.pure none
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

/-- **Structural decomposition of step_weight's support**: when
`step_weight m_prev m_new l s_A ≠ 0`, there exists a `μ_A_next` such that
`m_new.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next]` and `μ_A_next s_A ≠ 0`.
This captures the constraint imposed by the canonical-extension indicator
inside `step_weight_at_d`. -/
private lemma step_weight_pos_implies_structure
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (m_prev m_new : MatchingState sim pe_C μ_A_init h_init_R)
    (l : Label) (s_A : State_A)
    (h : step_weight sim pe_C μ_A_init h_init_R m_prev m_new l s_A ≠ 0) :
    ∃ μ_A_next : PMF State_A,
      m_new.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next] ∧
      μ_A_next s_A ≠ 0 := by
  classical
  unfold step_weight at h
  by_cases h_valid : m_prev.has_valid_R
  · rw [dif_pos h_valid] at h
    by_cases h_some : (pe_C.scheduler.next m_prev.e_C).isSome
    · rw [dif_pos h_some] at h
      unfold step_weight_at_d at h
      -- h : ∑' μ_C, d(l, μ_C) * (if h_supp then ∑' s_C' μ_A_next, γ * ... * [ind] else 0) ≠ 0
      rw [ne_eq, ENNReal.tsum_eq_zero] at h
      push Not at h
      obtain ⟨μ_C, h_μ_C⟩ := h
      -- d(l, μ_C) ≠ 0 AND the if-branch ≠ 0
      have h_d_ne : ((pe_C.scheduler.next m_prev.e_C).get h_some) (l, μ_C) ≠ 0 := by
        intro h_d_zero
        apply h_μ_C
        rw [h_d_zero, zero_mul]
      have h_inner_ne :
          (open Classical in
           if h_supp : (l, μ_C) ∈ ((pe_C.scheduler.next m_prev.e_C).get h_some).support then
             ∑' (s_C' : State_C) (μ_A_next : PMF State_A),
               (PMFRel.decomp (sim.stepWitness_pmfRel (m_prev.current_R h_valid)
                   (pe_C_step_witness pe_C m_prev.e_C m_prev.e_C_term _
                     (Option.eq_some_of_isSome h_some) l μ_C h_supp))
               ).γ (s_C', μ_A_next) * μ_A_next s_A *
               (if m_new.e_C = ⟨m_prev.e_C.init,
                   m_prev.e_C.trans.append (Seq.cons (l, s_C') Seq.nil)⟩ ∧
                 m_new.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next] then 1 else 0)
           else 0) ≠ 0 := by
        intro h_inner_zero
        apply h_μ_C
        rw [h_inner_zero, mul_zero]
      -- Extract h_supp.
      by_cases h_supp : (l, μ_C) ∈ ((pe_C.scheduler.next m_prev.e_C).get h_some).support
      · rw [dif_pos h_supp] at h_inner_ne
        -- Inner sum ≠ 0: ∃ s_C', μ_A_next with γ * μ_A_next.s_A * [ind] ≠ 0
        rw [ne_eq, ENNReal.tsum_eq_zero] at h_inner_ne
        push Not at h_inner_ne
        obtain ⟨s_C', h_sC⟩ := h_inner_ne
        rw [ne_eq, ENNReal.tsum_eq_zero] at h_sC
        push Not at h_sC
        obtain ⟨μ_A_next, h_term⟩ := h_sC
        -- h_term : γ(s_C', μ_A_next) * μ_A_next s_A * [ind] ≠ 0
        -- All factors ≠ 0.
        refine ⟨μ_A_next, ?_, ?_⟩
        · -- m_new.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next]
          by_contra h_chain_ne
          apply h_term
          have h_ind_zero :
              (if m_new.e_C = ⟨m_prev.e_C.init,
                   m_prev.e_C.trans.append (Seq.cons (l, s_C') Seq.nil)⟩ ∧
                 m_new.μ_A_chain = m_prev.μ_A_chain ++
                 [μ_A_next] then (1 : ENNReal) else 0) = 0 := by
            rw [if_neg]; intro ⟨_, h2⟩; exact h_chain_ne h2
          rw [h_ind_zero, mul_zero]
        · -- μ_A_next s_A ≠ 0
          by_contra h_μ_A_zero
          apply h_term
          rw [h_μ_A_zero]
          ring
      · rw [dif_neg h_supp] at h_inner_ne
        exact absurd rfl h_inner_ne
    · rw [dif_neg h_some] at h
      exact absurd rfl h
  · rw [dif_neg h_valid] at h
    exact absurd rfl h

/-- **Structural invariant on fromAbstractPrefix's support**: for each
matching state `m` in `fromAbstractPrefix history_A`'s positive-mass
support, `m.current_μ_A.support` contains the endstate of `history_A`.

This holds because `step_weight` places positive mass only on
`m_new.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next]` with the constraint
`μ_A_next s_A_k > 0` (i.e., `s_A_k ∈ μ_A_next.support`) implicit in the
nontrivial γ contribution.

Proof structure: case-split on `(history_A.trans.toList h_term).reverse`.
* Empty case ⟹ history_A.trans = nil. fromAbstractPrefix_base ≠ 0 gives
  μ_A_chain = [] and μ_A_init(s_A_init) > 0. current_μ_A = μ_A_init,
  endState = init = s_A_init.
* Cons (head :: tail) ⟹ ∃ m_prev with positive prefix-mass and
  step_weight ≠ 0. step_weight_pos_implies_structure gives μ_A_next with
  m.μ_A_chain ending in μ_A_next and μ_A_next(head.2) ≠ 0. current_μ_A =
  μ_A_next; endState = head.2 via endState_append_singleton. -/
theorem current_μ_A_support_contains_history_A_endState
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (history_A : AlterSeq State_A Label) (h_term : history_A.trans.Terminates)
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (h_mass : fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A h_term m ≠ 0) :
    history_A.endState h_term ∈ m.current_μ_A.support := by
  classical
  unfold fromAbstractPrefix at h_mass
  -- h_mass : fromAbstractPrefix_list ... history_A.init (toList.reverse) m ≠ 0
  rcases h_rev_eq : (history_A.trans.toList h_term).reverse with _ | ⟨head, tail⟩
  · -- nil case: toList.reverse = [], so toList = [], so trans = nil.
    have h_toList_nil : history_A.trans.toList h_term = [] :=
      List.reverse_eq_nil_iff.mp h_rev_eq
    have h_trans_length : history_A.trans.length h_term = 0 := by
      rw [← Stream'.Seq.length_toList, h_toList_nil]; rfl
    have h_trans_nil : history_A.trans = Seq.nil :=
      Stream'.Seq.length_eq_zero.mp h_trans_length
    -- Unfold fromAbstractPrefix_list at nil; h_mass becomes fromAbstractPrefix_base ≠ 0.
    rw [h_rev_eq] at h_mass
    unfold fromAbstractPrefix_list fromAbstractPrefix_base at h_mass
    by_cases h_cond :
        m.e_C.trans = Seq.nil ∧ m.μ_A_chain = [] ∧ m.e_C.init ∈ pe_C.init.support
    · rw [if_pos h_cond] at h_mass
      have h_init_ne_zero : μ_A_init history_A.init ≠ 0 := by
        intro h_zero
        apply h_mass
        rw [h_zero, zero_mul]
      have h_μ_chain_nil : m.μ_A_chain = [] := h_cond.2.1
      unfold MatchingState.current_μ_A
      rw [dif_pos h_μ_chain_nil]
      -- Goal: history_A.endState h_term ∈ μ_A_init.support
      have h_endState_eq_init : history_A.endState h_term = history_A.init := by
        have h_find : Nat.find h_term = 0 := by
          apply Nat.eq_zero_of_le_zero
          apply Nat.find_le
          rw [h_trans_nil]
          exact Stream'.Seq.terminatedAt_nil
        have h_stateAt : history_A.stateAt (Nat.find h_term) = some history_A.init := by
          rw [h_find]; rfl
        have h_endState_some := AlterSeq.stateAt_find_eq_endState history_A h_term
        rw [h_stateAt] at h_endState_some
        exact (Option.some.inj h_endState_some).symm
      rw [h_endState_eq_init, PMF.mem_support_iff]
      exact h_init_ne_zero
    · rw [if_neg h_cond] at h_mass
      exact absurd rfl h_mass
  · -- cons case: rev_list = head :: tail. head is the LAST transition of history_A.
    rw [h_rev_eq] at h_mass
    unfold fromAbstractPrefix_list at h_mass
    -- h_mass : ∑' m_prev, fromAbstractPrefix_list ... tail m_prev * step_weight ... ≠ 0
    rw [ne_eq, ENNReal.tsum_eq_zero] at h_mass
    push Not at h_mass
    obtain ⟨m_prev, h_prod⟩ := h_mass
    have h_step :
        step_weight sim pe_C μ_A_init h_init_R m_prev m head.1 head.2 ≠ 0 := by
      intro h_step_zero
      apply h_prod
      rw [h_step_zero, mul_zero]
    obtain ⟨μ_A_next, h_chain_eq, h_supp_s_A⟩ :=
      step_weight_pos_implies_structure sim pe_C μ_A_init h_init_R m_prev m head.1 head.2 h_step
    -- m.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next]
    -- current_μ_A m = μ_A_next.
    have h_chain_ne_nil : m.μ_A_chain ≠ [] := by
      rw [h_chain_eq]; exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    have h_current_eq : m.current_μ_A = μ_A_next := by
      unfold MatchingState.current_μ_A
      simp only [h_chain_eq,
        dif_neg (List.append_ne_nil_of_right_ne_nil m_prev.μ_A_chain
          (List.cons_ne_nil μ_A_next [])),
        List.getLast_append_singleton]
    -- Show history_A.trans = (ofList tail.reverse).append (cons head nil) via h_rev_eq.
    have h_toList_eq : history_A.trans.toList h_term = tail.reverse ++ [head] := by
      have h1 : (history_A.trans.toList h_term).reverse.reverse = (head :: tail).reverse := by
        rw [h_rev_eq]
      rw [List.reverse_reverse] at h1
      simpa using h1
    have h_trans_eq :
        history_A.trans = (Stream'.Seq.ofList tail.reverse).append (Seq.cons head Seq.nil) := by
      conv_lhs => rw [← Stream'.Seq.ofList_toList history_A.trans h_term, h_toList_eq]
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have h_prev_term_aux : (Stream'.Seq.ofList tail.reverse).Terminates :=
      Stream'.Seq.terminates_ofList _
    -- Reconstruct history_A as ⟨init, (ofList tail.reverse).append (cons head nil)⟩.
    have h_ha_struct : history_A =
        (⟨history_A.init, (Stream'.Seq.ofList tail.reverse).append (Seq.cons head Seq.nil)⟩
          : AlterSeq State_A Label) := by
      cases history_A with
      | mk init trans =>
        simp only [AlterSeq.mk.injEq, true_and]
        exact h_trans_eq
    have h_endState_eq : history_A.endState h_term = head.2 := by
      -- Hand-craft via a strong-typed auxiliary equation.
      have h_aux : ∀ (e : AlterSeq State_A Label) (h : e.trans.Terminates),
          e.trans = (Stream'.Seq.ofList tail.reverse).append (Seq.cons head Seq.nil) →
          e.endState h = head.2 := by
        intro e h h_trans
        -- Cases on e to expose its components; subst on h_trans.
        cases e with
        | mk init_e trans_e =>
          subst h_trans
          have h_target := AlterSeq.endState_append_singleton
            (⟨init_e, Stream'.Seq.ofList tail.reverse⟩ : AlterSeq State_A Label)
            h_prev_term_aux head.1 head.2
          exact h_target
      exact h_aux history_A h_term h_trans_eq
    rw [h_endState_eq, h_current_eq, PMF.mem_support_iff]
    exact h_supp_s_A

/-- Step 1 of validity: unwind `pe_A_emission_distribution`'s support
membership to extract a matching state `m` with positive mass under
`fromAbstractPrefix`, and `some (l, μ) ∈ (pe_A_emit_at_state m).support`. -/
private theorem pe_A_emission_support_extract
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (e : AlterSeq State_A Label) (l : Label) (μ : PMF State_A)
    (h_supp : some (l, μ) ∈
      (pe_A_emission_distribution sim pe_C μ_A_init h_init_R e).support) :
    ∃ (h_term : e.trans.Terminates) (m : MatchingState sim pe_C μ_A_init h_init_R),
      fromAbstractPrefix sim pe_C μ_A_init h_init_R e h_term m ≠ 0 ∧
      some (l, μ) ∈ (pe_A_emit_at_state m).support := by
  classical
  unfold pe_A_emission_distribution at h_supp
  by_cases h_term : e.trans.Terminates
  swap
  · exfalso
    rw [dif_neg h_term] at h_supp
    rw [PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at h_supp
    exact h_supp rfl
  rw [dif_pos h_term] at h_supp
  by_cases h0 : (∑' m, fromAbstractPrefix sim pe_C μ_A_init h_init_R e h_term m) ≠ 0
  swap
  · exfalso
    rw [dif_neg h0] at h_supp
    rw [PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at h_supp
    exact h_supp rfl
  rw [dif_pos h0] at h_supp
  by_cases hFin : (∑' m, fromAbstractPrefix sim pe_C μ_A_init h_init_R e h_term m) ≠ ⊤
  swap
  · exfalso
    rw [dif_neg hFin] at h_supp
    rw [PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at h_supp
    exact h_supp rfl
  rw [dif_pos hFin] at h_supp
  rw [PMF.mem_support_iff, PMF.bind_apply] at h_supp
  -- h_supp : (∑' m, normalize ... m * pe_A_emit_at_state m (some (l, μ))) ≠ 0
  have h_exists : ∃ m, (PMF.normalize _ h0 hFin) m *
      (pe_A_emit_at_state m) (some (l, μ)) ≠ 0 := by
    by_contra h_all
    push Not at h_all
    exact h_supp (ENNReal.tsum_eq_zero.mpr h_all)
  obtain ⟨m, h_m_ne⟩ := h_exists
  rw [ne_eq, mul_eq_zero, not_or] at h_m_ne
  obtain ⟨h_norm_ne, h_emit_ne⟩ := h_m_ne
  refine ⟨h_term, m, ?_, ?_⟩
  · rw [PMF.normalize_apply] at h_norm_ne
    exact left_ne_zero_of_mul h_norm_ne
  · rw [PMF.mem_support_iff]; exact h_emit_ne

/-- Step 2 of validity: from `some (l, μ) ∈ (pe_A_emit_at_state m).support`,
extract `m.has_valid_R`, `pe_C.scheduler.next m.e_C = some d`, and
`(l, μ) ∈ (blockEmission_general m d _ _).support`. -/
private theorem pe_A_emit_at_state_extract
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (l : Label) (μ : PMF State_A)
    (h_emit_supp : some (l, μ) ∈ (pe_A_emit_at_state m).support) :
    ∃ (h_valid : m.has_valid_R) (d : PMF (Label × PMF State_C))
      (h_d_eq : pe_C.scheduler.next m.e_C = some d),
      (l, μ) ∈ (blockEmission_general m d h_d_eq h_valid).support := by
  classical
  unfold pe_A_emit_at_state at h_emit_supp
  rw [PMF.mem_support_iff] at h_emit_supp
  by_cases h_valid : m.has_valid_R
  swap
  · exfalso
    rw [dif_neg h_valid] at h_emit_supp
    rw [PMF.pure_apply_of_ne _ _ (by simp)] at h_emit_supp
    exact h_emit_supp rfl
  rw [dif_pos h_valid] at h_emit_supp
  -- Case on (pe_C.scheduler.next m.e_C).isSome.
  by_cases h_some : (pe_C.scheduler.next m.e_C).isSome
  swap
  · exfalso
    rw [dif_neg h_some] at h_emit_supp
    rw [PMF.pure_apply_of_ne _ _ (by simp)] at h_emit_supp
    exact h_emit_supp rfl
  rw [dif_pos h_some] at h_emit_supp
  -- Extract d := (pe_C.scheduler.next m.e_C).get h_some.
  set d := (pe_C.scheduler.next m.e_C).get h_some with h_d_def
  refine ⟨h_valid, d, Option.eq_some_of_isSome h_some, ?_⟩
  rw [PMF.mem_support_iff]
  intro h_block
  apply h_emit_supp
  rw [PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  by_cases h_eq : some (l, μ) = some x
  · rw [if_pos h_eq]
    have hx : x = (l, μ) := (Option.some.inj h_eq).symm
    rw [hx, h_block]
  · rw [if_neg h_eq]

/-- Step 3 of validity: from `(l, μ) ∈ blockEmission_general m d h_d_eq h_valid`'s
support, extract `(l, μ) = (l_C, μ_A_next)` for some `(l_C, μ_C) ∈ d.support`
and `μ_A_next ∈ ω.support` (where `ω := sim.stepWitness ...`). -/
private theorem blockEmission_general_extract
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (d : PMF (Label × PMF State_C))
    (h_d_eq : pe_C.scheduler.next m.e_C = some d)
    (h_valid : m.has_valid_R)
    (l : Label) (μ : PMF State_A)
    (h_supp : (l, μ) ∈ (blockEmission_general m d h_d_eq h_valid).support) :
    ∃ (μ_C : PMF State_C) (h_μ_C_supp : (l, μ_C) ∈ d.support),
      μ ∈ (sim.stepWitness (m.current_R h_valid)
        (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq l μ_C
          h_μ_C_supp)).support := by
  classical
  unfold blockEmission_general at h_supp
  rw [PMF.mem_support_bind_iff] at h_supp
  obtain ⟨⟨l_C, μ_C⟩, h_d_supp, h_inner⟩ := h_supp
  -- h_inner : (l, μ) ∈ ((if h_supp_lμ : (l_C, μ_C) ∈ d.support then
  --                        ω.map (fun μ_A_next => (l_C, μ_A_next))
  --                      else PMF.pure ...).support)
  -- Since h_d_supp : (l_C, μ_C) ∈ d.support, the if is true.
  rw [dif_pos h_d_supp] at h_inner
  rw [PMF.mem_support_map_iff] at h_inner
  obtain ⟨μ_A_next, h_ω_supp, h_eq⟩ := h_inner
  -- h_eq : (l_C, μ_A_next) = (l, μ)
  have h_l : l_C = l := (Prod.mk.inj h_eq).1
  have h_μ : μ_A_next = μ := (Prod.mk.inj h_eq).2
  subst h_l; subst h_μ
  exact ⟨μ_C, h_d_supp, h_ω_supp⟩

/-- Step 4 of validity: connect history_A's endstate (at any TerminatedAt
position) to the canonical `Nat.find h_term` endstate. -/
private theorem stateAt_eq_endState_at_terminator
    (e : AlterSeq State_A Label) (h_term : e.trans.Terminates)
    (n : ℕ) (s : State_A)
    (h_term_n : e.trans.TerminatedAt n) (h_stateAt_n : e.stateAt n = some s) :
    e.endState h_term = s := by
  -- For any n with TerminatedAt n, n ≥ Nat.find h_term. We need to show
  -- e.stateAt n = e.stateAt (Nat.find h_term) for n ≥ Nat.find h_term.
  have h_endState_eq := AlterSeq.stateAt_find_eq_endState e h_term
  -- For n ≥ Nat.find h_term, e.stateAt n = e.stateAt (Nat.find h_term).
  -- This is because the trans is terminated at Nat.find h_term, so any later
  -- get? returns none, and stateAt n = (trans.get? (n-1)).map snd or e.init.
  have h_n_ge : n ≥ Nat.find h_term := Nat.find_le h_term_n
  -- If n = 0, then Nat.find h_term = 0 too (since 0 ≤ Nat.find ≤ 0).
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · subst hn0
    have h_find_zero : Nat.find h_term = 0 := Nat.eq_zero_of_le_zero h_n_ge
    rw [h_find_zero] at h_endState_eq
    have h_stateAt_def : e.stateAt 0 = some e.init := rfl
    rw [h_stateAt_def] at h_stateAt_n h_endState_eq
    have h_s_eq_init : s = e.init := (Option.some.inj h_stateAt_n).symm
    have h_endState_init : e.endState h_term = e.init :=
      (Option.some.inj h_endState_eq).symm
    rw [h_endState_init, h_s_eq_init]
  · -- n ≥ 1. e.stateAt n = (e.trans.get? (n-1)).map snd.
    -- Case on Nat.find h_term.
    rcases Nat.eq_zero_or_pos (Nat.find h_term) with hf0 | hf_pos
    · -- Nat.find = 0 means trans = nil (TerminatedAt 0). So e.trans.get? (n-1) = none.
      -- Then stateAt n = none, contradicting h_stateAt_n.
      exfalso
      have h_term_0 : e.trans.TerminatedAt 0 := hf0 ▸ Nat.find_spec h_term
      have h_get_none : e.trans.get? (n - 1) = none :=
        Stream'.Seq.terminated_stable e.trans (Nat.zero_le _) h_term_0
      have h_stateAt_def : e.stateAt n = (e.trans.get? (n - 1)).map Prod.snd := by
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn_pos.ne'
        rw [hj]; rfl
      rw [h_get_none] at h_stateAt_def
      simp only [Option.map_none] at h_stateAt_def
      rw [h_stateAt_def] at h_stateAt_n
      simp at h_stateAt_n
    · -- Nat.find h_term > 0 and n ≥ Nat.find h_term.
      by_cases h_eq_find : n = Nat.find h_term
      · rw [← h_eq_find] at h_endState_eq
        rw [h_stateAt_n] at h_endState_eq
        exact (Option.some.inj h_endState_eq).symm
      · -- n > Nat.find h_term: e.trans.get? (n - 1) = none.
        have h_gt : n > Nat.find h_term := lt_of_le_of_ne h_n_ge (Ne.symm h_eq_find)
        have h_n1_ge : n - 1 ≥ Nat.find h_term := by omega
        have h_get_none := Stream'.Seq.terminated_stable e.trans h_n1_ge (Nat.find_spec h_term)
        have h_stateAt_def : e.stateAt n = (e.trans.get? (n - 1)).map Prod.snd := by
          obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn_pos.ne'
          rw [hj]; rfl
        rw [h_get_none] at h_stateAt_def
        simp only [Option.map_none] at h_stateAt_def
        rw [h_stateAt_def] at h_stateAt_n
        exact absurd h_stateAt_n (by simp)

/-- The abstract probabilistic execution `pe_A` constructed from the
simulation data, operating over `sys_A^w` (the weak-step closure).

The `valid` proof composes the four extraction theorems above with sim's
`stepWitness_weakTau` (internal label case) or `stepWitness_weakStep`
(external label case). The s ∈ m.current_μ_A.support requirement is
discharged by `current_μ_A_support_contains_history_A_endState`. -/
noncomputable def pe_A_of_simulation
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init) :
    PMFProbabilisticExecution (sys_A^w).toSystem where
  init := μ_A_init
  scheduler :=
    { next := pe_A_emission_distribution sim pe_C μ_A_init h_init_R
      valid := by
        intro e n s h_term_n h_stateAt_n l μ h_supp
        -- Convert `some (l, μ) ∈ ... .support` form.
        rw [show some (l, μ) ∈ _ ↔ _ from Iff.rfl] at h_supp
        -- Step 1: extract h_term, m, h_mass, h_emit.
        obtain ⟨h_term, m, h_mass, h_emit⟩ :=
          pe_A_emission_support_extract sim pe_C μ_A_init h_init_R e l μ h_supp
        -- Step 2: extract h_valid, d, h_d_eq, h_block.
        obtain ⟨h_valid, d, h_d_eq, h_block⟩ :=
          pe_A_emit_at_state_extract m l μ h_emit
        -- Step 3: extract μ_C, h_μC_supp, h_ω_supp.
        obtain ⟨μ_C, h_μC_supp, h_ω_supp⟩ :=
          blockEmission_general_extract m d h_d_eq h_valid l μ h_block
        -- Build the sys_A^w.step witness.
        refine ⟨m.current_μ_A, sim.stepWitness (m.current_R h_valid) _, ?_, h_ω_supp, ?_⟩
        · -- s ∈ m.current_μ_A.support.
          have h_endState_s : e.endState h_term = s :=
            stateAt_eq_endState_at_terminator e h_term n s h_term_n h_stateAt_n
          rw [← h_endState_s]
          exact current_μ_A_support_contains_history_A_endState sim pe_C μ_A_init h_init_R
            e h_term m h_mass
        · -- weakTau ∨ weakStep. Case-split on sys_C.internal l.
          rcases Classical.em (sys_C.internal l) with h_int | h_ext
          · exact Or.inl (sim.stepWitness_weakTau (m.current_R h_valid) _ h_int)
          · exact Or.inr (sim.stepWitness_weakStep (m.current_R h_valid) _ h_ext) }

/-! #### Mass-conservation helper (base case)

The full mass-conservation invariant on `fromAbstractPrefix` requires both
`step_weight_marginal_eq_per_state_kernel` and `m_dist_posterior_predictive_with_mass`
(defined further below). The helper for the base case is independent and
lives here. -/

/-- **Base-case mass conservation**: the total mass of `fromAbstractPrefix_base`
over all matching states equals `μ_A_init s_A_init`. Proof via re-indexing
the sum by `m.e_C.init` using `tsum_eq_tsum_of_ne_zero_bij`: the bijection
maps each `s_C` in `pe_C.init`'s support to the canonical initial matching
state `⟨⟨s_C, Seq.nil⟩, terminates_nil, [], vacuous_h_R⟩`. -/
private lemma fromAbstractPrefix_base_tsum_eq
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (s_A_init : State_A) :
    (∑' m : MatchingState sim pe_C μ_A_init h_init_R,
        fromAbstractPrefix_base sim pe_C μ_A_init h_init_R s_A_init m) =
      μ_A_init s_A_init := by
  classical
  have h_reindex :
      (∑' m : MatchingState sim pe_C μ_A_init h_init_R,
          fromAbstractPrefix_base sim pe_C μ_A_init h_init_R s_A_init m) =
      ∑' s_C : State_C, μ_A_init s_A_init * pe_C.init s_C := by
    refine tsum_eq_tsum_of_ne_zero_bij
      (fun (p : {s_C : State_C // μ_A_init s_A_init * pe_C.init s_C ≠ 0}) =>
        (⟨⟨p.val, Seq.nil⟩, Stream'.Seq.terminates_nil, [], fun h_ne => absurd rfl h_ne⟩
         : MatchingState sim pe_C μ_A_init h_init_R)) ?_ ?_ ?_
    · -- Injectivity: i ⟨s_C₁, _⟩ = i ⟨s_C₂, _⟩ → s_C₁ = s_C₂.
      rintro ⟨s_C₁, _⟩ ⟨s_C₂, _⟩ h_eq
      have h_init_eq : s_C₁ = s_C₂ := by
        have := congr_arg
          (fun m : MatchingState sim pe_C μ_A_init h_init_R => m.e_C.init) h_eq
        exact this
      exact Subtype.ext h_init_eq
    · -- support f ⊆ range i: any m with fromAbstractPrefix_base m ≠ 0 has the canonical form.
      intro m h_m_supp
      rw [Function.mem_support] at h_m_supp
      unfold fromAbstractPrefix_base at h_m_supp
      by_cases h_cond :
          m.e_C.trans = Seq.nil ∧ m.μ_A_chain = [] ∧ m.e_C.init ∈ pe_C.init.support
      · rw [if_pos h_cond] at h_m_supp
        refine ⟨⟨m.e_C.init, h_m_supp⟩, ?_⟩
        apply MatchingState.ext_of_data
        · -- e_C: ⟨m.e_C.init, Seq.nil⟩ = m.e_C
          change (⟨m.e_C.init, Seq.nil⟩ : AlterSeq State_C Label) = m.e_C
          conv_rhs => rw [show m.e_C = ⟨m.e_C.init, m.e_C.trans⟩ from rfl, h_cond.1]
        · -- μ_A_chain: [] = m.μ_A_chain
          exact h_cond.2.1.symm
      · rw [if_neg h_cond] at h_m_supp
        exact absurd rfl h_m_supp
    · -- f(i x) = g x.
      rintro ⟨s_C, h_nonzero⟩
      change fromAbstractPrefix_base sim pe_C μ_A_init h_init_R s_A_init
           ⟨⟨s_C, Seq.nil⟩, Stream'.Seq.terminates_nil, [], fun h_ne => absurd rfl h_ne⟩ =
           μ_A_init s_A_init * pe_C.init s_C
      unfold fromAbstractPrefix_base
      have h_s_C_in_supp : s_C ∈ pe_C.init.support := by
        rw [PMF.mem_support_iff]
        intro h_zero
        apply h_nonzero
        simp only [mul_eq_zero]
        right
        exact h_zero
      rw [if_pos ⟨rfl, rfl, h_s_C_in_supp⟩]
  rw [h_reindex, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]


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

/-- **`joint_kernel_at_d`** — inner form of `joint_kernel` parameterised
by `d` and `h_d_eq` (plan v4.1, §5). This is the closed-form expression
that lives inside `joint_kernel`'s `dif_pos h_valid`/`dif_pos h_some`
branch, lifted to a top-level definition. Taking `d` as an explicit
argument allows proofs that bridge with `blockEmission_general` (also
d-explicit) to operate on a common form without dependent-rewrite
hazards on `(Option).get`. -/
noncomputable def joint_kernel_at_d
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (d : PMF (Label × PMF State_C))
    (h_d_eq : pe_C.scheduler.next m.e_C = some d)
    (h_valid : m.has_valid_R)
    (l : Label) (s_C : State_C) (s_A : State_A) : ENNReal :=
  ∑' (μ_C : PMF State_C),
    d (l, μ_C) * (
      open Classical in
      if h_supp : (l, μ_C) ∈ d.support then
        ∑' (μ_A_next : PMF State_A),
          (PMFRel.decomp (sim.stepWitness_pmfRel (m.current_R h_valid)
              (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq l μ_C h_supp))
          ).γ (s_C, μ_A_next) * μ_A_next s_A
      else 0)

/-- The per-step joint kernel, parameterised by the matching state `m`.
Returns 0 when `m` lacks an R-witness, or `pe_C.scheduler.next m.e_C = none`
(pe_C has halted at this prefix), or `(l, μ_C) ∉ d.support`. Implemented
as a thin wrapper over `joint_kernel_at_d`. -/
noncomputable def joint_kernel
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (l : Label) (s_C : State_C) (s_A : State_A) : ENNReal :=
  open Classical in
  if h_valid : m.has_valid_R then
    if h_some : (pe_C.scheduler.next m.e_C).isSome then
      joint_kernel_at_d m ((pe_C.scheduler.next m.e_C).get h_some)
        (Option.eq_some_of_isSome h_some) h_valid l s_C s_A
    else 0
  else 0

/-- **Bridge lemma** (plan v4.1, §5): `joint_kernel` equals
`joint_kernel_at_d` when supplied with the matching `d` and `h_d_eq`.

Proof strategy: introduce a generic `aux` function parameterised over
the Option-value `o` and an equation `pe_C.scheduler.next m.e_C = o`,
prove the equation holds when `o = some d`, then specialise. -/
private theorem joint_kernel_eq_at_d
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (d : PMF (Label × PMF State_C))
    (h_d_eq : pe_C.scheduler.next m.e_C = some d)
    (h_valid : m.has_valid_R)
    (l : Label) (s_C : State_C) (s_A : State_A) :
    joint_kernel m l s_C s_A = joint_kernel_at_d m d h_d_eq h_valid l s_C s_A := by
  classical
  unfold joint_kernel
  rw [dif_pos h_valid]
  have h_some : (pe_C.scheduler.next m.e_C).isSome = true := by rw [h_d_eq]; rfl
  rw [dif_pos h_some]
  -- Goal: joint_kernel_at_d m ((pe_C.scheduler.next m.e_C).get h_some)
  --                          (Option.eq_some_of_isSome h_some) h_valid l s_C s_A
  --     = joint_kernel_at_d m d h_d_eq h_valid l s_C s_A
  -- Use Eq.recOn on h_d_eq.symm to transport h_d_eq's d into position.
  -- Concretely: from h_d_eq : pe_C.scheduler.next m.e_C = some d, we know that
  -- both sides are joint_kernel_at_d m d' (proof of pe_C... = some d') h_valid ...
  -- with d' = d, and any two such proofs are equal by Subsingleton.
  have h_d_get : (pe_C.scheduler.next m.e_C).get h_some = d := by
    have h_pair : pe_C.scheduler.next m.e_C = some ((pe_C.scheduler.next m.e_C).get h_some) :=
      Option.eq_some_of_isSome h_some
    -- Avoid `rw [h_d_eq] at h_pair` (dependent rewrite). Compose equations directly:
    have h_eq_some : some d = some ((pe_C.scheduler.next m.e_C).get h_some) :=
      h_d_eq.symm.trans h_pair
    exact (Option.some.inj h_eq_some).symm
  -- Rewrite the goal via h_d_get. The dependent eq_some_of_isSome term's
  -- expected type `pe_C... = some ((pe_C...).get h_some)` becomes
  -- `pe_C... = some d` after rewriting — matching h_d_eq's type.
  -- By proof irrelevance, the two `pe_C... = some d` proofs are equal.
  subst h_d_get
  -- After subst (h_d_get viewing d as the variable to replace by .get h_some):
  -- d has been replaced by (pe_C.scheduler.next m.e_C).get h_some.
  -- h_d_eq's type becomes pe_C... = some ((pe_C...).get h_some) = the eq_some_of_isSome.
  -- By proof irrelevance, the two joint_kernel_at_d's are equal.
  rfl

-- per_state_kernel_at_d and per_state_kernel_eq_at_d are placed
-- after the existing per_state_kernel definition below.

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
      pe_C.kernel m.e_C (l, s_C) := by
  classical
  unfold joint_kernel ProbabilisticExecution.kernel
  simp only [dif_pos h_valid]
  by_cases h_some : (pe_C.scheduler.next m.e_C).isSome
  swap
  · -- Scheduler returns none: both sides are 0.
    simp only [dif_neg h_some, tsum_zero]
    rcases Option.eq_none_or_eq_some (pe_C.scheduler.next m.e_C) with h_none | ⟨d, h_some_eq⟩
    · rw [h_none]; rfl
    · exfalso; rw [h_some_eq] at h_some; exact h_some rfl
  simp only [dif_pos h_some]
  -- Get d from the some-witness.
  set d := (pe_C.scheduler.next m.e_C).get h_some with h_d_def
  have h_d_eq : pe_C.scheduler.next m.e_C = some d := Option.eq_some_of_isSome h_some
  -- Rewrite the RHS using h_d_eq + Option.elim_some.
  conv_rhs => rw [h_d_eq, Option.elim_some]
  -- Unfold joint_kernel_at_d to get the tsum form.
  unfold joint_kernel_at_d
  -- LHS: ∑' s_A, ∑' μ_C, d(l,μ_C)
  -- * (if h_supp then ∑' μ_A_next, γ(s_C,μ_A_next)
  -- * μ_A_next s_A else 0)
  -- Swap tsums.
  rw [ENNReal.tsum_comm]
  -- Now: ∑' μ_C, ∑' s_A, d(l,μ_C) * (...)
  -- Factor d(l, μ_C) out of the inner sum and combine the if.
  have h_inner : ∀ μ_C : PMF State_C,
      (∑' s_A : State_A, d (l, μ_C) * (
        if h_supp : (l, μ_C) ∈ d.support then
          ∑' (μ_A_next : PMF State_A),
            (PMFRel.decomp (sim.stepWitness_pmfRel (m.current_R h_valid)
                (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq l μ_C h_supp))
            ).γ (s_C, μ_A_next) * μ_A_next s_A
        else 0)) =
      d (l, μ_C) * μ_C s_C := by
    intro μ_C
    rw [ENNReal.tsum_mul_left]
    by_cases h_supp : (l, μ_C) ∈ d.support
    · simp only [dif_pos h_supp]
      -- After tsum_mul_left and dif_pos, goal is
      --   d(l, μ_C) * ∑' s_A μ_A_next, γ(s_C, μ_A_next) * μ_A_next s_A = d(l, μ_C) * μ_C s_C
      -- Use per_step_mass_marginal_concrete and congr.
      have h_step := pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq l μ_C h_supp
      have h_marg := per_step_mass_marginal_concrete sim (m.current_R h_valid) h_step s_C
      rw [h_marg]
    · -- ¬ (l, μ_C) ∈ d.support: d(l, μ_C) = 0.
      simp only [dif_neg h_supp, tsum_zero, mul_zero]
      have h_d_zero : d (l, μ_C) = 0 := by
        rw [PMF.mem_support_iff] at h_supp
        push Not at h_supp
        exact h_supp
      rw [h_d_zero, zero_mul]
  -- Apply h_inner.
  rw [tsum_congr h_inner]
  -- RHS: (d.bind (fun lμ => PMF.map (lμ.1, ·) lμ.2)) (l, s_C)
  rw [PMF.bind_apply]
  -- = ∑' lμ, d lμ * (PMF.map (lμ.1, ·) lμ.2) (l, s_C)
  -- Need to show ∑' μ_C, d(l, μ_C) * μ_C s_C = ∑' lμ, d lμ * (PMF.map (lμ.1, ·) lμ.2) (l, s_C)
  -- RHS unfolds to ∑' (l', μ_C), d(l', μ_C) * if l = l' then μ_C s_C else 0.
  rw [ENNReal.tsum_prod']
  -- ∑' l', ∑' μ_C, d (l', μ_C) * (PMF.map (l', ·) μ_C) (l, s_C)
  have h_inner_map : ∀ (l' : Label) (μ_C : PMF State_C),
      (PMF.map (fun s => (l', s)) μ_C) (l, s_C) =
      (if l = l' then μ_C s_C else 0) := by
    intro l' μ_C
    rw [PMF.map_apply]
    by_cases h_l : l = l'
    · subst h_l
      rw [if_pos rfl]
      rw [tsum_eq_single s_C (fun s h_ne => by simp [Prod.mk.injEq, Ne.symm h_ne])]
      simp
    · rw [if_neg h_l]
      apply ENNReal.tsum_eq_zero.mpr
      intro s
      have : (l, s_C) ≠ (l', s) := fun h => h_l (Prod.mk.inj h).1
      simp [this]
  simp_rw [h_inner_map]
  -- ∑' l', ∑' μ_C, d (l', μ_C) * (if l = l' then μ_C s_C else 0)
  rw [tsum_eq_single l (fun l' h_ne => ?_)]
  · -- l' = l case.
    apply tsum_congr
    intro μ_C
    rw [if_pos rfl]
  · -- l' ≠ l: inner is 0.
    apply ENNReal.tsum_eq_zero.mpr
    intro μ_C
    rw [if_neg (Ne.symm h_ne), mul_zero]

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

/-- **`per_state_kernel_at_d`** — d-explicit form of `per_state_kernel`.
The s_C-marginal of `joint_kernel_at_d`. -/
noncomputable def per_state_kernel_at_d
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (d : PMF (Label × PMF State_C))
    (h_d_eq : pe_C.scheduler.next m.e_C = some d)
    (h_valid : m.has_valid_R)
    (l : Label) (s_A : State_A) : ENNReal :=
  ∑' s_C, joint_kernel_at_d m d h_d_eq h_valid l s_C s_A

/-- **Corollary**: `per_state_kernel` equals its d-explicit form under
the matching hypotheses. (Follows from `joint_kernel_eq_at_d` applied
under the s_C-tsum.) -/
private theorem per_state_kernel_eq_at_d
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (d : PMF (Label × PMF State_C))
    (h_d_eq : pe_C.scheduler.next m.e_C = some d)
    (h_valid : m.has_valid_R)
    (l : Label) (s_A : State_A) :
    per_state_kernel m l s_A = per_state_kernel_at_d m d h_d_eq h_valid l s_A := by
  unfold per_state_kernel per_state_kernel_at_d
  exact tsum_congr fun s_C => joint_kernel_eq_at_d m d h_d_eq h_valid l s_C s_A

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

/-- **Indicator-collapse sub-lemma**: for `(s_C', μ_A_next)` such that
`R s_C' μ_A_next` holds, summing the canonical-extension indicator over all
matching states yields `1`. The witness is `advance_pe_C_step m_prev l s_C'
μ_A_next h_R`; uniqueness up to definitional proof irrelevance for
`MatchingState`'s `e_C_term` / `h_R` Prop fields collapses the sum. -/
private theorem matchingState_indicator_sum_eq_one
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m_prev : MatchingState sim pe_C μ_A_init h_init_R)
    (l : Label) (s_C' : State_C) (μ_A_next : PMF State_A)
    (h_R : R s_C' μ_A_next) :
    (∑' m_new : MatchingState sim pe_C μ_A_init h_init_R,
      (open Classical in
       if m_new.e_C = ⟨m_prev.e_C.init,
            m_prev.e_C.trans.append (Seq.cons (l, s_C') Seq.nil)⟩ ∧
          m_new.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next] then (1 : ENNReal) else 0)) =
      1 := by
  classical
  let canonical : MatchingState sim pe_C μ_A_init h_init_R :=
    MatchingState.advance_pe_C_step m_prev l s_C' μ_A_next h_R
  have h_canonical_e_C :
      canonical.e_C = ⟨m_prev.e_C.init,
        m_prev.e_C.trans.append (Seq.cons (l, s_C') Seq.nil)⟩ := rfl
  have h_canonical_chain :
      canonical.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next] := rfl
  rw [tsum_eq_single canonical]
  · -- value at canonical: indicator is 1.
    rw [if_pos ⟨h_canonical_e_C, h_canonical_chain⟩]
  · -- ∀ m_new ≠ canonical, indicator m_new = 0.
    intro m_new h_ne
    by_cases h_cond :
        m_new.e_C = ⟨m_prev.e_C.init,
          m_prev.e_C.trans.append (Seq.cons (l, s_C') Seq.nil)⟩ ∧
        m_new.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next]
    · -- Conditions match: by ext, m_new = canonical, contradicting h_ne.
      exfalso
      apply h_ne
      exact MatchingState.ext_of_data
        (h_cond.1.trans h_canonical_e_C.symm)
        (h_cond.2.trans h_canonical_chain.symm)
    · rw [if_neg h_cond]

/-- **Auxiliary lemma (§3.2)**: summing `step_weight m_prev m_new l s_A` over
the new matching state `m_new` recovers `per_state_kernel m_prev l s_A`.

Proof structure:
* **Degenerate cases** (¬h_valid, scheduler.next = none): both sides equal 0.
* **Main case** (h_valid, scheduler.next = some d):
  - Use Fubini (`ENNReal.tsum_comm`) to swap `∑' m_new` with the inner
    `∑' (μ_C, s_C', μ_A_next)`.
  - For each `(s_C', μ_A_next)`, collapse `∑' m_new, [m_new.e_C = X ∧
    m_new.μ_A_chain = Y]` to the indicator of `R s_C' μ_A_next` via
    `matchingState_indicator_sum_eq_one`.
  - Absorb the `R` indicator into γ's support (γ > 0 ⟹ R via R_on_support).
  - Bridge to `per_state_kernel_at_d` via `per_state_kernel_eq_at_d`.

Plan v4.1 §3.2 step-case definition is precisely this identity. -/
private theorem step_weight_marginal_eq_per_state_kernel
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (m_prev : MatchingState sim pe_C μ_A_init h_init_R)
    (l : Label) (s_A : State_A) :
    (∑' m_new, step_weight sim pe_C μ_A_init h_init_R m_prev m_new l s_A) =
      per_state_kernel m_prev l s_A := by
  classical
  by_cases h_valid : m_prev.has_valid_R
  · by_cases h_some : (pe_C.scheduler.next m_prev.e_C).isSome
    · -- Main case: h_valid and scheduler.next = some d.
      set d : PMF (Label × PMF State_C) := (pe_C.scheduler.next m_prev.e_C).get h_some with hd_def
      have h_d_eq : pe_C.scheduler.next m_prev.e_C = some d :=
        Option.eq_some_of_isSome h_some
      -- Convert LHS via step_weight unfold.
      have h_LHS_eq : ∀ m_new : MatchingState sim pe_C μ_A_init h_init_R,
          step_weight sim pe_C μ_A_init h_init_R m_prev m_new l s_A =
          step_weight_at_d sim pe_C μ_A_init h_init_R m_prev m_new d h_d_eq h_valid l s_A := by
        intro m_new
        unfold step_weight
        rw [dif_pos h_valid, dif_pos h_some]
      simp_rw [h_LHS_eq]
      -- Convert RHS to per_state_kernel_at_d.
      rw [per_state_kernel_eq_at_d m_prev d h_d_eq h_valid]
      -- Set the decomp once per μ_C (γ in scope).
      -- Show both sides equal a common intermediate form:
      --   ∑' μ_C, d(l, μ_C) * (if h_supp then ∑' (s_C, μ_A_next), γ(s_C, μ_A_next) * μ_A_next s_A
      --                                  else 0)
      set common : ENNReal := ∑' μ_C : PMF State_C, d (l, μ_C) *
        (open Classical in
         if h_supp : (l, μ_C) ∈ d.support then
           ∑' (p : State_C × PMF State_A),
             (PMFRel.decomp (sim.stepWitness_pmfRel (m_prev.current_R h_valid)
                 (pe_C_step_witness pe_C m_prev.e_C m_prev.e_C_term d h_d_eq l μ_C h_supp))
             ).γ (p.1, p.2) * p.2 s_A
         else 0) with hcommon_def
      have h_LHS : (∑' m_new : MatchingState sim pe_C μ_A_init h_init_R,
          step_weight_at_d sim pe_C μ_A_init h_init_R m_prev m_new d h_d_eq h_valid l s_A) =
          common := by
        unfold step_weight_at_d
        -- LHS: ∑' m_new, ∑' μ_C, d(l,μ_C) * (if h_supp then INNER(m_new, μ_C) else 0)
        --      where INNER(m_new, μ_C) = ∑' (s_C', μ_A_next), γ * μ_A_next.s_A * [ind(m_new)]
        rw [ENNReal.tsum_comm]
        rw [hcommon_def]
        refine tsum_congr (fun μ_C => ?_)
        -- Inner: ∑' m_new, d * (if h_supp then ∑' (s_C', μ_A_next), γ * μ_A_next.s_A
        --                                                             * [ind] else 0)
        rw [ENNReal.tsum_mul_left]
        congr 1
        by_cases h_supp : (l, μ_C) ∈ d.support
        · simp only [dif_pos h_supp]
          -- ∑' m_new, ∑' (s_C', μ_A_next), γ * μ_A_next.s_A * [ind]
          -- Swap m_new with (s_C', μ_A_next) (double tsum_comm).
          rw [show (∑' (m_new : MatchingState sim pe_C μ_A_init h_init_R)
                      (s_C' : State_C) (μ_A_next : PMF State_A),
                (PMFRel.decomp (sim.stepWitness_pmfRel (m_prev.current_R h_valid)
                    (pe_C_step_witness pe_C m_prev.e_C m_prev.e_C_term d h_d_eq l μ_C h_supp))
                ).γ (s_C', μ_A_next) * μ_A_next s_A *
                (if m_new.e_C = ⟨m_prev.e_C.init,
                    m_prev.e_C.trans.append (Seq.cons (l, s_C') Seq.nil)⟩ ∧
                  m_new.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next] then 1 else 0)) =
              ∑' (s_C' : State_C) (μ_A_next : PMF State_A)
                  (m_new : MatchingState sim pe_C μ_A_init h_init_R),
                (PMFRel.decomp (sim.stepWitness_pmfRel (m_prev.current_R h_valid)
                    (pe_C_step_witness pe_C m_prev.e_C m_prev.e_C_term d h_d_eq l μ_C h_supp))
                ).γ (s_C', μ_A_next) * μ_A_next s_A *
                (if m_new.e_C = ⟨m_prev.e_C.init,
                    m_prev.e_C.trans.append (Seq.cons (l, s_C') Seq.nil)⟩ ∧
                  m_new.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next] then 1 else 0)
            from by rw [ENNReal.tsum_comm]; refine tsum_congr (fun s_C' => ?_);
                    rw [ENNReal.tsum_comm]]
          -- Convert RHS: ∑' p → ∑' s_C' ∑' μ_A_next.
          rw [ENNReal.tsum_prod' (f := fun p =>
            (PMFRel.decomp (sim.stepWitness_pmfRel (m_prev.current_R h_valid)
                (pe_C_step_witness pe_C m_prev.e_C m_prev.e_C_term d h_d_eq l μ_C h_supp))
            ).γ (p.1, p.2) * p.2 s_A)]
          -- LHS: ∑' (s_C', μ_A_next, m_new), γ * μ_A_next s_A * [ind(m_new)]
          -- RHS: ∑' (s_C', μ_A_next), γ * μ_A_next s_A
          -- For each (s_C', μ_A_next): factor γ * μ_A_next s_A out of m_new-sum,
          -- then absorb via R_on_support + matchingState_indicator_sum_eq_one.
          refine tsum_congr (fun s_C' => ?_)
          refine tsum_congr (fun μ_A_next => ?_)
          -- Goal: ∑' m_new, γ * μ_A_next s_A * [ind(m_new)] = γ * μ_A_next s_A.
          rw [ENNReal.tsum_mul_left]
          -- Goal: γ * μ_A_next s_A * ∑' m_new, [ind] = γ * μ_A_next s_A (RHS uncurries to .2 s_A).
          -- Set γ_val for case-split.
          set γ_val : ENNReal :=
            (PMFRel.decomp (sim.stepWitness_pmfRel (m_prev.current_R h_valid)
                (pe_C_step_witness pe_C m_prev.e_C m_prev.e_C_term d h_d_eq l μ_C h_supp))
            ).γ (s_C', μ_A_next) with hγ_def
          by_cases h_γ : γ_val = 0
          · -- γ_val = 0: both sides reduce to 0 via zero_mul.
            simp [h_γ]
          · -- γ_val > 0: R s_C' μ_A_next holds; indicator sum = 1.
            have h_R : R s_C' μ_A_next := by
              have h_supp_γ : (s_C', μ_A_next) ∈
                  (PMFRel.decomp (sim.stepWitness_pmfRel (m_prev.current_R h_valid)
                      (pe_C_step_witness pe_C m_prev.e_C m_prev.e_C_term d h_d_eq l μ_C h_supp))
                  ).γ.support := by
                rw [PMF.mem_support_iff]; exact h_γ
              exact (PMFRel.decomp (sim.stepWitness_pmfRel (m_prev.current_R h_valid)
                  (pe_C_step_witness pe_C m_prev.e_C m_prev.e_C_term d h_d_eq l μ_C h_supp))
                ).h_R (s_C', μ_A_next) h_supp_γ
            rw [matchingState_indicator_sum_eq_one m_prev l s_C' μ_A_next h_R, mul_one]
        · simp only [dif_neg h_supp]
          rw [tsum_zero]
      have h_RHS : per_state_kernel_at_d m_prev d h_d_eq h_valid l s_A = common := by
        unfold per_state_kernel_at_d joint_kernel_at_d
        -- RHS: ∑' s_C, ∑' μ_C, d * (if h_supp then ∑' μ_A_next, γ(s_C, μ_A_next)
        --                        * μ_A_next.s_A else 0)
        rw [ENNReal.tsum_comm]
        rw [hcommon_def]
        refine tsum_congr (fun μ_C => ?_)
        rw [ENNReal.tsum_mul_left]
        congr 1
        by_cases h_supp : (l, μ_C) ∈ d.support
        · simp only [dif_pos h_supp]
          -- ∑' s_C, ∑' μ_A_next, γ(s_C, μ_A_next) * μ_A_next.s_A
          -- = ∑' p : State_C × PMF State_A, γ(p.1, p.2) * p.2 s_A
          rw [ENNReal.tsum_prod' (f := fun p =>
            (PMFRel.decomp (sim.stepWitness_pmfRel (m_prev.current_R h_valid)
                (pe_C_step_witness pe_C m_prev.e_C m_prev.e_C_term d h_d_eq l μ_C h_supp))
            ).γ (p.1, p.2) * p.2 s_A)]
        · simp only [dif_neg h_supp]
          rw [tsum_zero]
      exact h_LHS.trans h_RHS.symm
    · -- None branch: step_weight = 0 and per_state_kernel = 0.
      have h_each : ∀ m_new : MatchingState sim pe_C μ_A_init h_init_R,
          step_weight sim pe_C μ_A_init h_init_R m_prev m_new l s_A = 0 := by
        intro m_new
        unfold step_weight
        rw [dif_pos h_valid, dif_neg h_some]
      simp_rw [h_each]
      rw [tsum_zero]
      unfold per_state_kernel joint_kernel
      symm
      apply ENNReal.tsum_eq_zero.mpr
      intro s_C
      simp [dif_pos h_valid, dif_neg h_some]
  · -- ¬h_valid: step_weight = 0 and per_state_kernel = 0.
    have h_each : ∀ m_new : MatchingState sim pe_C μ_A_init h_init_R,
        step_weight sim pe_C μ_A_init h_init_R m_prev m_new l s_A = 0 := by
      intro m_new
      unfold step_weight
      rw [dif_neg h_valid]
    simp_rw [h_each]
    rw [tsum_zero]
    unfold per_state_kernel joint_kernel
    symm
    apply ENNReal.tsum_eq_zero.mpr
    intro s_C
    simp [dif_neg h_valid]

/-! #### `m_dist_posterior_predictive` (§9.3 — the central work item)

The heart of the proof. Links pe_A's `m_kernel`-aggregated kernel at
`history_A_{k+1}` to the joint kernel's abstract marginal at step k,
yielding `pe_A.probOf history_A_{k+1}`. Proved by induction on
`history_A.trans` length, interleaved with mass conservation. -/

/-- **D-explicit form** of `blockEmission_general_emission_marginal`:
∑' μ, blockEmission * μ s_A = per_state_kernel_at_d. Both sides use the
external `d` and `h_d_eq`, sidestepping the bridge lemma. -/
private theorem blockEmission_general_emission_marginal_at_d
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (d : PMF (Label × PMF State_C))
    (h_d_eq : pe_C.scheduler.next m.e_C = some d)
    (h_valid : m.has_valid_R)
    (l : Label) (s_A : State_A) :
    (∑' μ : PMF State_A,
      blockEmission_general m d h_d_eq h_valid (l, μ) * μ s_A) =
    per_state_kernel_at_d m d h_d_eq h_valid l s_A := by
  classical
  -- Define the common intermediate form `mid`.
  set mid : ENNReal := ∑' μ_C : PMF State_C, d (l, μ_C) *
    (open Classical in
     if h_supp : (l, μ_C) ∈ d.support then
       ((sim.stepWitness (m.current_R h_valid)
         (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq l μ_C h_supp)).bind id) s_A
     else 0) with hmid_def
  -- LHS = mid (5-step reduction).
  have h_LHS_eq_mid : (∑' μ : PMF State_A,
      blockEmission_general m d h_d_eq h_valid (l, μ) * μ s_A) = mid := by
    -- Step 1: rewrite blockEmission_general via the helper.
    have h1 : (∑' μ : PMF State_A,
        blockEmission_general m d h_d_eq h_valid (l, μ) * μ s_A) =
        ∑' μ : PMF State_A,
          (∑' μ_C : PMF State_C, d (l, μ_C) *
            (open Classical in
             if h_supp : (l, μ_C) ∈ d.support then
               sim.stepWitness (m.current_R h_valid)
                 (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq l μ_C h_supp) μ
             else 0)) * μ s_A := by
      apply tsum_congr; intro μ
      rw [blockEmission_general_apply_eq]
    rw [h1]
    -- Step 2: distribute μ s_A into the inner sum.
    have h2 : (∑' μ : PMF State_A,
        (∑' μ_C : PMF State_C, d (l, μ_C) *
          (open Classical in
           if h_supp : (l, μ_C) ∈ d.support then
             sim.stepWitness (m.current_R h_valid)
               (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq l μ_C h_supp) μ
           else 0)) * μ s_A) =
        ∑' μ : PMF State_A, ∑' μ_C : PMF State_C,
          d (l, μ_C) *
            (open Classical in
             if h_supp : (l, μ_C) ∈ d.support then
               sim.stepWitness (m.current_R h_valid)
                 (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq l μ_C h_supp) μ
             else 0) * μ s_A := by
      apply tsum_congr; intro μ
      rw [ENNReal.tsum_mul_right]
    rw [h2]
    -- Step 3: swap tsums.
    rw [ENNReal.tsum_comm]
    rw [hmid_def]
    -- Per μ_C: factor d and reduce inner.
    apply tsum_congr; intro μ_C
    -- Goal: ∑' μ, d * if-clause * μ s_A = d * (if h_supp then (ω.bind id) s_A else 0)
    -- Step 4: re-associate to put d at the front.
    have h4 : (∑' μ : PMF State_A, d (l, μ_C) *
          (open Classical in
           if h_supp : (l, μ_C) ∈ d.support then
             sim.stepWitness (m.current_R h_valid)
               (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq l μ_C h_supp) μ
           else 0) * μ s_A) =
        ∑' μ : PMF State_A, d (l, μ_C) *
          ((open Classical in
            if h_supp : (l, μ_C) ∈ d.support then
              sim.stepWitness (m.current_R h_valid)
                (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq l μ_C h_supp) μ
            else 0) * μ s_A) := by
      apply tsum_congr; intro μ; ring
    rw [h4]
    rw [ENNReal.tsum_mul_left]
    -- Step 5: inner reduction. d * ∑' μ, (if h_supp then ω μ else 0) * μ s_A
    --       = d * (if h_supp then (ω.bind id) s_A else 0)
    congr 1
    by_cases h_supp : (l, μ_C) ∈ d.support
    · simp only [dif_pos h_supp]
      -- ∑' μ, ω μ * μ s_A = (ω.bind id) s_A
      rw [PMF.bind_apply]; rfl
    · simp only [dif_neg h_supp]
      -- ∑' μ, 0 * μ s_A = 0
      simp
  -- RHS = mid (3-step reduction).
  have h_RHS_eq_mid : per_state_kernel_at_d m d h_d_eq h_valid l s_A = mid := by
    unfold per_state_kernel_at_d joint_kernel_at_d
    rw [ENNReal.tsum_comm]
    rw [hmid_def]
    apply tsum_congr
    intro μ_C
    rw [ENNReal.tsum_mul_left]
    congr 1
    by_cases h_supp : (l, μ_C) ∈ d.support
    · simp only [dif_pos h_supp]
      exact per_step_mass_marginal_abstract sim (m.current_R h_valid)
        (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq l μ_C h_supp) s_A
    · simp only [dif_neg h_supp]
      simp
  exact h_LHS_eq_mid.trans h_RHS_eq_mid.symm

/-- **§9.3 sub-lemma A** (`blockEmission_general_emission_marginal`):
`blockEmission_general`'s emission marginal at `(l, s_A)` equals
`per_state_kernel m l s_A`. Stated against `per_state_kernel` (the
canonical form); proven by combining the d-explicit form above with
`per_state_kernel_eq_at_d`. -/
private theorem blockEmission_general_emission_marginal
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (d : PMF (Label × PMF State_C))
    (h_d_eq : pe_C.scheduler.next m.e_C = some d)
    (h_valid : m.has_valid_R)
    (l : Label) (s_A : State_A) :
    (∑' μ : PMF State_A,
      blockEmission_general m d h_d_eq h_valid (l, μ) * μ s_A) =
    per_state_kernel m l s_A := by
  rw [per_state_kernel_eq_at_d m d h_d_eq h_valid l s_A]
  exact blockEmission_general_emission_marginal_at_d m d h_d_eq h_valid l s_A

/-- **Uniform per-matching-state emission marginal**: for any matching
state `m` (valid or not), the emission marginal of `pe_A_emit_at_state m`
at `(l, ·) * · s_A` equals `per_state_kernel m l s_A`. In the valid
case, this follows from `blockEmission_general_emission_marginal`; in
the invalid case, both sides are 0. -/
private theorem pe_A_emit_at_state_emission_marginal
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m : MatchingState sim pe_C μ_A_init h_init_R)
    (l : Label) (s_A : State_A) :
    (∑' μ : PMF State_A, pe_A_emit_at_state m (some (l, μ)) * μ s_A) =
    per_state_kernel m l s_A := by
  classical
  unfold pe_A_emit_at_state
  by_cases h_valid : m.has_valid_R
  · simp only [dif_pos h_valid]
    by_cases h_some : (pe_C.scheduler.next m.e_C).isSome = true
    · simp only [dif_pos h_some]
      -- pe_A_emit_at_state branch: (blockEmission_general ...).map some
      -- ((bem).map some) (some (l, μ)) = bem (l, μ) (by PMF.map_apply + tsum_eq_single)
      have h_map_apply : ∀ μ : PMF State_A,
          ((blockEmission_general m ((pe_C.scheduler.next m.e_C).get h_some)
            (Option.eq_some_of_isSome h_some) h_valid).map some) (some (l, μ)) =
          blockEmission_general m ((pe_C.scheduler.next m.e_C).get h_some)
            (Option.eq_some_of_isSome h_some) h_valid (l, μ) := by
        intro μ
        rw [PMF.map_apply]
        rw [tsum_eq_single (l, μ) (fun x h_ne => by
          have h_some_ne : some (l, μ) ≠ some x := fun h_eq => h_ne (Option.some.inj h_eq).symm
          simp [h_some_ne])]
        simp
      simp_rw [h_map_apply]
      -- Now: ∑' μ, blockEmission_general ... (l, μ) * μ s_A = per_state_kernel m l s_A
      exact blockEmission_general_emission_marginal m
        ((pe_C.scheduler.next m.e_C).get h_some)
        (Option.eq_some_of_isSome h_some) h_valid l s_A
    · -- ¬h_some: pe_A_emit_at_state = PMF.pure none.
      simp only [dif_neg h_some]
      -- ∑' μ, (PMF.pure none) (some (l, μ)) * μ s_A = 0
      have h_zero : ∀ μ : PMF State_A,
          (PMF.pure (none : Option (Label × PMF State_A))) (some (l, μ)) * μ s_A = 0 := by
        intro μ; rw [PMF.pure_apply_of_ne _ _ (by simp)]; ring
      simp_rw [h_zero]
      rw [tsum_zero]
      -- per_state_kernel m l s_A = 0 (joint_kernel = 0 when ¬h_some)
      unfold per_state_kernel joint_kernel
      symm
      apply ENNReal.tsum_eq_zero.mpr
      intro s_C
      simp [dif_pos h_valid, dif_neg h_some]
  · -- ¬h_valid: pe_A_emit_at_state = PMF.pure none.
    simp only [dif_neg h_valid]
    have h_zero : ∀ μ : PMF State_A,
        (PMF.pure (none : Option (Label × PMF State_A))) (some (l, μ)) * μ s_A = 0 := by
      intro μ; rw [PMF.pure_apply_of_ne _ _ (by simp)]; ring
    simp_rw [h_zero]
    rw [tsum_zero]
    -- per_state_kernel m l s_A = 0 (joint_kernel = 0 when ¬h_valid)
    unfold per_state_kernel joint_kernel
    symm
    apply ENNReal.tsum_eq_zero.mpr
    intro s_C
    simp [dif_neg h_valid]

/-- **§9.3 sub-lemma B** (`pe_A_kernel_via_m_kernel`, multiplicative form):
pe_A's per-step kernel at `history_A_k` multiplied by `Z` (the total
m_kernel mass) equals the m_kernel-aggregated `per_state_kernel`. No
division. Requires `Z ≠ 0` and `Z ≠ ⊤` (the latter implicit by mass
conservation, but needed as an explicit hypothesis here).

Plan v4.1 §9.3 sub-lemma B. -/
private theorem pe_A_kernel_via_m_kernel
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (history_A_k : AlterSeq State_A Label) (h_term_k : history_A_k.trans.Terminates)
    (l : Label) (s_A : State_A)
    (h_Z_ne_zero :
      (∑' m, fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A_k h_term_k m) ≠ 0)
    (h_Z_ne_top :
      (∑' m, fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A_k h_term_k m) ≠ ⊤) :
    (pe_A_of_simulation sim pe_C μ_A_init h_init_R).kernel history_A_k (l, s_A) *
      (∑' m, fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A_k h_term_k m) =
    ∑' m, fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A_k h_term_k m *
      per_state_kernel m l s_A := by
  classical
  -- Set abbreviations for readability.
  set m_kernel : MatchingState sim pe_C μ_A_init h_init_R → ENNReal :=
    fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A_k h_term_k with h_mk_def
  set Z := ∑' m, m_kernel m with hZ_def
  -- Unfold pe_A.kernel and project scheduler.next; goal is now in terms of
  -- pe_A_emission_distribution directly.
  change (∑' μ : PMF State_A,
      pe_A_emission_distribution sim pe_C μ_A_init h_init_R history_A_k (some (l, μ)) * μ s_A) *
      Z = _
  -- Unfold pe_A_emission_distribution and apply dif_pos's.
  unfold pe_A_emission_distribution
  rw [dif_pos h_term_k, dif_pos h_Z_ne_zero, dif_pos h_Z_ne_top]
  -- LHS: (∑' μ, ((PMF.normalize m_kernel _ _).bind pe_A_emit_at_state) (some (l, μ)) * μ s_A) * Z
  -- Rewrite the inner ∑' μ as a double sum over m and μ, swap, collapse.
  have h_inner :
      (∑' μ : PMF State_A,
        ((PMF.normalize m_kernel h_Z_ne_zero h_Z_ne_top).bind pe_A_emit_at_state)
          (some (l, μ)) * μ s_A) =
      Z⁻¹ * ∑' m : MatchingState sim pe_C μ_A_init h_init_R,
        m_kernel m * per_state_kernel m l s_A := by
    -- Expand the bind and normalize.
    have h_expand : ∀ μ : PMF State_A,
        ((PMF.normalize m_kernel h_Z_ne_zero h_Z_ne_top).bind pe_A_emit_at_state)
          (some (l, μ)) * μ s_A =
        ∑' m : MatchingState sim pe_C μ_A_init h_init_R,
          m_kernel m * Z⁻¹ * pe_A_emit_at_state m (some (l, μ)) * μ s_A := by
      intro μ
      have h_step :
          ((PMF.normalize m_kernel h_Z_ne_zero h_Z_ne_top).bind pe_A_emit_at_state)
            (some (l, μ)) =
          ∑' m : MatchingState sim pe_C μ_A_init h_init_R,
            m_kernel m * Z⁻¹ * pe_A_emit_at_state m (some (l, μ)) := by
        rw [PMF.bind_apply]
        refine tsum_congr (fun m => ?_)
        rw [PMF.normalize_apply, ← hZ_def]
      rw [h_step, ENNReal.tsum_mul_right]
    simp_rw [h_expand]
    -- Swap, factor (m_kernel m * Z⁻¹) out, apply helper.
    rw [ENNReal.tsum_comm]
    have h_per_m : ∀ m : MatchingState sim pe_C μ_A_init h_init_R,
        (∑' μ : PMF State_A,
          m_kernel m * Z⁻¹ * pe_A_emit_at_state m (some (l, μ)) * μ s_A) =
        Z⁻¹ * (m_kernel m * per_state_kernel m l s_A) := by
      intro m
      have hM : (∑' μ : PMF State_A,
          m_kernel m * Z⁻¹ * pe_A_emit_at_state m (some (l, μ)) * μ s_A) =
          m_kernel m * Z⁻¹ *
            (∑' μ : PMF State_A, pe_A_emit_at_state m (some (l, μ)) * μ s_A) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr (fun μ => ?_); ring
      rw [hM, pe_A_emit_at_state_emission_marginal]; ring
    rw [tsum_congr h_per_m]
    rw [ENNReal.tsum_mul_left]
  rw [h_inner]
  -- LHS: (Z⁻¹ * ∑' m, m_kernel m * per_state_kernel m l s_A) * Z = ∑' m, ...
  rw [mul_comm Z⁻¹ _, mul_assoc, ENNReal.inv_mul_cancel h_Z_ne_zero h_Z_ne_top, mul_one]

/-- **Auxiliary form** of `m_dist_posterior_predictive` that takes mass
conservation at step k as an explicit hypothesis. This is the variant used
by `fromAbstractPrefix_mass_conservation`'s step case, which supplies the
IH-derived `h_mass`; the global `m_dist_posterior_predictive` (below) is a
corollary that supplies `h_mass` via `fromAbstractPrefix_mass_conservation`.

Proof strategy: by `pe_A.probOf`'s cons factorisation,
  `pe_A.probOf history_A_{k+1} = pe_A.probOf history_A_k * pe_A.kernel history_A_k (l, s_A)`.
Then `pe_A.kernel` unfolds via the normalised m_kernel bind to give
  `pe_A.kernel = (1/Z) * ∑' m, m_kernel m * (emission marginal at m)`,
where `Z = ∑' m, m_kernel m`. The hypothesis `h_mass` gives
`Z = pe_A.probOf history_A_k`, so the product simplifies to
`∑' m, m_kernel m * per_state_kernel m l s_A` by sub-lemma B. -/
theorem m_dist_posterior_predictive_with_mass
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (history_A_k : AlterSeq State_A Label) (h_term_k : history_A_k.trans.Terminates)
    (l : Label) (s_A : State_A)
    (h_mass : (∑' m, fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A_k h_term_k m) =
      (pe_A_of_simulation sim pe_C μ_A_init h_init_R).probOf history_A_k h_term_k) :
    (∑' m, fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A_k h_term_k m *
      per_state_kernel m l s_A) =
    (pe_A_of_simulation sim pe_C μ_A_init h_init_R).probOf
      ⟨history_A_k.init, history_A_k.trans.append (Seq.cons (l, s_A) Seq.nil)⟩
      ⟨Nat.find h_term_k + 1,
        Stream'.Seq.terminatedAt_append_find h_term_k
          (show (Seq.cons (l, s_A) Seq.nil).TerminatedAt 1 from rfl)⟩ := by
  classical
  set pe_A := pe_A_of_simulation sim pe_C μ_A_init h_init_R with hpe_A_def
  set m_kernel : MatchingState sim pe_C μ_A_init h_init_R → ENNReal :=
    fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A_k h_term_k with hmk_def
  set Z := ∑' m, m_kernel m with hZ_def
  rw [PMFProbabilisticExecution.probOf_append_singleton pe_A history_A_k.init history_A_k.trans
        h_term_k (l, s_A)]
  by_cases h_Z_eq_zero : Z = 0
  · rw [← h_mass, h_Z_eq_zero, zero_mul]
    apply ENNReal.tsum_eq_zero.mpr; intro m
    have h_each : m_kernel m = 0 := ENNReal.tsum_eq_zero.mp h_Z_eq_zero m
    rw [h_each, zero_mul]
  · have h_Z_ne_top : Z ≠ ⊤ := by
      rw [h_mass]
      refine ne_of_lt
        (lt_of_le_of_lt (PMFProbabilisticExecution.probOf_le_init pe_A history_A_k h_term_k) ?_)
      exact lt_of_le_of_lt (PMF.coe_le_one _ _) ENNReal.one_lt_top
    have h_sub_B :
        pe_A.kernel history_A_k (l, s_A) * Z =
        ∑' m, m_kernel m * per_state_kernel m l s_A :=
      pe_A_kernel_via_m_kernel sim pe_C μ_A_init h_init_R history_A_k h_term_k l s_A
        h_Z_eq_zero h_Z_ne_top
    rw [← h_sub_B, ← h_mass, mul_comm]

/-! #### Mass-conservation invariant on `fromAbstractPrefix` (§3.2) -/

/-- **Mass-conservation invariant**: the total mass of the matching-state
posterior at `history_A` equals `pe_A.probOf history_A`.

Proof structure (strong induction on `(history_A.trans.toList h_term).length`):
* **Base case** (length 0): `trans = Seq.nil`. Sum of `fromAbstractPrefix_base`
  over `m` collapses via initial-state indicator (parallel to
  `matchingState_indicator_sum_eq_one`) to `μ_A_init(s_A_init) ·
  pe_C.init.tsum = μ_A_init(s_A_init) = pe_A.probOf(⟨s_A_init, Seq.nil⟩)`.
* **Step case** (length n+1): split `trans = previous_trans.append (cons last
  nil)`. Apply `fromAbstractPrefix_list`'s cons recursion to extract the
  outer `∑' m_prev, fromAbstractPrefix(previous) * step_weight(...)`. Swap
  sums; collapse the `m_new`-sum via `step_weight_marginal_eq_per_state_kernel`
  to `∑' m_prev, fromAbstractPrefix(previous) * per_state_kernel(...)`. Apply
  `m_dist_posterior_predictive_with_mass` with the IH-derived `h_mass` to
  identify with `pe_A.probOf(previous ++ [last])`. -/
theorem fromAbstractPrefix_mass_conservation
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (history_A : AlterSeq State_A Label) (h_term : history_A.trans.Terminates) :
    (∑' m, fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A h_term m) =
      (pe_A_of_simulation sim pe_C μ_A_init h_init_R).probOf
        history_A h_term := by
  -- Strong induction on the list-length of history_A's transitions.
  generalize h_len_eq : (history_A.trans.toList h_term).length = n
  induction n using Nat.strong_induction_on generalizing history_A h_term with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h_zero | h_pos
    · -- Base case: trans.toList = [], so trans = Seq.nil.
      have h_toList_nil : history_A.trans.toList h_term = [] := by
        apply List.length_eq_zero_iff.mp; rw [h_len_eq]; exact h_zero
      have h_trans_length : history_A.trans.length h_term = 0 := by
        rw [← Stream'.Seq.length_toList, h_toList_nil]; rfl
      have h_trans_nil : history_A.trans = Seq.nil :=
        Stream'.Seq.length_eq_zero.mp h_trans_length
      have h_LHS :
          (∑' m, fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A h_term m) =
          μ_A_init history_A.init := by
        have h_unfold : ∀ m,
            fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A h_term m =
            fromAbstractPrefix_base sim pe_C μ_A_init h_init_R history_A.init m := by
          intro m
          unfold fromAbstractPrefix
          rw [h_toList_nil]
          rfl
        simp_rw [h_unfold]
        exact fromAbstractPrefix_base_tsum_eq sim pe_C μ_A_init h_init_R history_A.init
      have h_RHS :
          (pe_A_of_simulation sim pe_C μ_A_init h_init_R).probOf history_A h_term =
          μ_A_init history_A.init := by
        unfold PMFProbabilisticExecution.probOf
        rw [h_toList_nil]
        unfold PMFProbabilisticExecution.probOfRemaining
        simp only [List.foldl, mul_one]
        rfl
      exact h_LHS.trans h_RHS.symm
    · -- Step case: trans non-empty. Split into previous ++ [last], apply
      -- step_weight_marginal_eq_per_state_kernel + m_dist_posterior_predictive_with_mass.
      have h_toList_ne : history_A.trans.toList h_term ≠ [] := by
        intro h_nil
        have : (history_A.trans.toList h_term).length = 0 := by rw [h_nil]; rfl
        rw [h_len_eq] at this
        omega
      obtain ⟨previous_trans, last, h_prev_term, h_trans_eq, h_prev_toList_eq, h_last_eq⟩ :=
        Stream'.Seq.exists_split_last history_A.trans h_term h_toList_ne
      let previous_history_A : AlterSeq State_A Label := ⟨history_A.init, previous_trans⟩
      have h_prev_term' : previous_history_A.trans.Terminates := h_prev_term
      have h_prev_len : (previous_history_A.trans.toList h_prev_term').length = n - 1 := by
        change (previous_trans.toList h_prev_term).length = n - 1
        rw [h_prev_toList_eq, List.length_dropLast, h_len_eq]
      have h_IH :
          (∑' m, fromAbstractPrefix sim pe_C μ_A_init h_init_R previous_history_A h_prev_term' m) =
          (pe_A_of_simulation sim pe_C μ_A_init h_init_R).probOf previous_history_A h_prev_term' :=
        ih (n - 1) (Nat.sub_lt h_pos Nat.zero_lt_one) previous_history_A h_prev_term' h_prev_len
      have h_toList_history_A : history_A.trans.toList h_term =
          previous_trans.toList h_prev_term ++ [last] := by
        rw [h_prev_toList_eq, h_last_eq]
        exact (List.dropLast_append_getLast h_toList_ne).symm
      have h_rev : (history_A.trans.toList h_term).reverse =
          last :: (previous_trans.toList h_prev_term).reverse := by
        rw [h_toList_history_A, List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, List.singleton_append]
      have h_recursion : ∀ m,
          fromAbstractPrefix sim pe_C μ_A_init h_init_R history_A h_term m =
          ∑' m_prev,
            fromAbstractPrefix sim pe_C μ_A_init h_init_R previous_history_A h_prev_term' m_prev *
            step_weight sim pe_C μ_A_init h_init_R m_prev m last.1 last.2 := by
        intro m
        unfold fromAbstractPrefix
        rw [h_rev]
        rfl
      simp_rw [h_recursion]
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left]
      simp_rw [step_weight_marginal_eq_per_state_kernel]
      rw [m_dist_posterior_predictive_with_mass sim pe_C μ_A_init h_init_R
        previous_history_A h_prev_term' last.1 last.2 h_IH]
      -- Lift via h_trans_eq to relate the reconstructed AlterSeq to history_A.
      have h_aux : ∀ (e : AlterSeq State_A Label) (h : e.trans.Terminates)
          (_h_trans_eq : e.trans = previous_trans.append (Seq.cons last Seq.nil)),
          (pe_A_of_simulation sim pe_C μ_A_init h_init_R).probOf
            ⟨e.init, previous_trans.append (Seq.cons (last.1, last.2) Seq.nil)⟩
            ⟨Nat.find h_prev_term + 1, Stream'.Seq.terminatedAt_append_find h_prev_term
              (show (Seq.cons (last.1, last.2) Seq.nil).TerminatedAt 1 from rfl)⟩ =
          (pe_A_of_simulation sim pe_C μ_A_init h_init_R).probOf e h := by
        intro e h h_trans
        cases e with
        | mk init_e trans_e =>
          subst h_trans
          rfl
      exact h_aux history_A h_term h_trans_eq

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
  m_dist_posterior_predictive_with_mass sim pe_C μ_A_init h_init_R history_A_k h_term_k l s_A
    (fromAbstractPrefix_mass_conservation sim pe_C μ_A_init h_init_R history_A_k h_term_k)

/-! #### Joint-space marginals (§9.4, §9.5)

Once `joint_kernel` and `joint_mass` are defined, the two marginal
identities bridge `pe_C.probOf` and `pe_A.probOf` to a shared joint mass
quantity, giving the trace coupling by tsum bijection. -/

/-- **Path-value helper for joint_mass** (v4.2 redesigned): given the
previous matching state `m_prev` and the remaining (concrete, abstract)
transitions, compute the product of `joint_kernel` factors. At each step,
integrate the γ-samples `(μ_C, μ_A_next)` explicitly with γ-weight; the
inner `m_next` sum is collapsed by a fully-constraining indicator that
ties `m_next.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next]`.

The recursion shape mirrors `step_weight_at_d` / `fromAbstractPrefix_list`:
both definitions thread the chain via the canonical extension determined
by the γ-sampled μ_A_next, so the §9.5.a re-indexing
(`joint_mass_path_eq_m_kernel_aggregate`) becomes a level-by-level
correspondence with fromAbstractPrefix.

Returns `0` when labels mismatch, when `m_prev` lacks a valid R-witness,
or when `pe_C.scheduler.next m_prev.e_C = none` (pe_C halted). -/
noncomputable def joint_mass_path
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (m_prev : MatchingState sim pe_C μ_A_init h_init_R) :
    List (Label × State_C) → List (Label × State_A) → ENNReal
  | List.nil, List.nil => 1
  | List.cons hC restC, List.cons hA restA =>
      open Classical in
      if hC.1 = hA.1 then
        if h_valid : m_prev.has_valid_R then
          if h_some : (pe_C.scheduler.next m_prev.e_C).isSome then
            ∑' (μ_C : PMF State_C),
              ((pe_C.scheduler.next m_prev.e_C).get h_some) (hA.1, μ_C) * (
                if h_supp : (hA.1, μ_C) ∈
                    ((pe_C.scheduler.next m_prev.e_C).get h_some).support then
                  ∑' (μ_A_next : PMF State_A),
                    (PMFRel.decomp (sim.stepWitness_pmfRel (m_prev.current_R h_valid)
                        (pe_C_step_witness pe_C m_prev.e_C m_prev.e_C_term _
                          (Option.eq_some_of_isSome h_some) hA.1 μ_C h_supp))
                    ).γ (hC.2, μ_A_next) * μ_A_next hA.2 *
                    ∑' (m_next : MatchingState sim pe_C μ_A_init h_init_R),
                      (if m_next.e_C = ⟨m_prev.e_C.init,
                            m_prev.e_C.trans.append (Seq.cons (hC.1, hC.2) Seq.nil)⟩ ∧
                          m_next.μ_A_chain = m_prev.μ_A_chain ++ [μ_A_next]
                        then 1 else 0) *
                      joint_mass_path m_next restC restA
                else 0)
          else 0
        else 0
      else 0
  | List.nil, List.cons _ _ => 0
  | List.cons _ _, List.nil => 0

/-- **Initial matching state** at a concrete initial state `s_C_init`
(in `pe_C.init.support`) with empty trans and empty `μ_A_chain`. Used as
the starting point for `joint_mass`. -/
noncomputable def initial_matching_state
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (s_C_init : State_C) :
    MatchingState sim pe_C μ_A_init h_init_R where
  e_C := ⟨s_C_init, Seq.nil⟩
  e_C_term := Stream'.Seq.terminates_nil
  μ_A_chain := []
  h_R := fun h_ne => absurd rfl h_ne

/-- **Joint mass** (v4.2): `joint_mass e_C e_A` is the total probability
of a joint (concrete, abstract) trajectory whose concrete part is `e_C`
and abstract part is `e_A`. Defined as
  `pe_C.init e_C.init * μ_A_init e_A.init * joint_mass_path(m_0, trans_C, trans_A)`
where `m_0` is the `initial_matching_state` at `e_C.init`, and
`joint_mass_path` (v4.2) integrates each step's γ-samples
`(μ_C_k, μ_A_next_k)` with γ-weight and threads the chain via the
canonical extension `m_k.μ_A_chain ++ [μ_A_next_k]`.

Plan §4 says
  `joint_mass(e_C, e_A) := pe_C.init(e_C.init) · μ_A_init(e_A.init) ·
                          ∏_{k} joint_kernel(m_k, l_k, s_C_k, s_A_k)`
with `m_k` determined by the trajectory. v4.2's `joint_mass_path`
recursion realises this product as a γ-weighted nested integration; the
`∏_k joint_kernel(m_k, ...)` factorisation is recovered as the *output*
of the §9.4 telescope (γ-second-marginal collapse over `s_A`), not
syntactically present in the recursion. See plan §4 / §9.4 for the
correspondence. -/
noncomputable def joint_mass
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (e_C : AlterSeq State_C Label) (e_C_term : e_C.trans.Terminates)
    (e_A : AlterSeq State_A Label) (e_A_term : e_A.trans.Terminates) : ENNReal :=
  pe_C.init e_C.init * μ_A_init e_A.init *
  joint_mass_path (initial_matching_state sim pe_C μ_A_init h_init_R e_C.init)
    (e_C.trans.toList e_C_term) (e_A.trans.toList e_A_term)

/-! #### `tightExecsA_characterisation` (§9.2)

The plan §9.2 characterises `TightExecsA(τ)` as the set of `e_A`'s whose
trans-list has external sub-sequence equal to `τ` (and which ends with
an external label or are empty). This is the structural enumeration
used by §9.5's induction on `n = |e_A.trans|`.

For a Lean-mechanical induction on `n`, the key operations are:
* **Last-step decomposition**: for tight `e_A` with non-empty trans,
  write `e_A.trans = trans'.append (cons (l_last, s_last) nil)` with
  `l_last` external (= the last entry of τ).
* **Truncation**: for `e_A` with `trans = trans'.append (cons _ nil)`,
  let `e_A' = ⟨e_A.init, trans'⟩` (the truncation). This `e_A'` has
  trace `τ'` (= τ with last entry removed), but is not necessarily
  tight (its last label may be internal).

The induction in §9.5 uses these operations to relate `pe_A.probOf e_A`
to `pe_A.probOf e_A'`; tightness is recovered at the boundary via the
last-external-label condition. -/

/-- **Truncation to a given list of transitions**: convert a list of
(Label × State) back to an AlterSeq. Useful for the induction over
trans's length in §9.5. -/
noncomputable def fromList (init : State_A) (l : List (Label × State_A)) :
    AlterSeq State_A Label :=
  ⟨init, Stream'.Seq.ofList l⟩

/-- **Tight execution has external last label** (§9.2): a tight
execution with non-empty trans has a position `n` such that `get? n` is
an external label and `TerminatedAt (n+1)`. -/
theorem tightExec_has_external_last
    (ls : LabelledSystem State_A Label) (e : AlterSeq State_A Label)
    (h_tight : ls.IsTight e) (h_nonempty : e.trans ≠ Seq.nil) :
    ∃ (n : ℕ) (l_last : Label) (s_last : State_A),
      e.trans.get? n = some (l_last, s_last) ∧
      e.trans.TerminatedAt (n + 1) ∧
      ¬ ls.internal l_last := by
  rcases h_tight with h_term_0 | ⟨n, l, s, h_get, h_term, h_ext⟩
  · -- TerminatedAt 0: then e.trans = nil. Contradiction.
    exfalso
    apply h_nonempty
    exact Stream'.Seq.terminatedAt_zero_iff.mp h_term_0
  · exact ⟨n, l, s, h_get, h_term, h_ext⟩

/-- **Tightness extension by an external transition**: if `e_A` has any
finite trans and we append a transition with an external label, the
result is tight. -/
theorem isTight_append_external
    (ls : LabelledSystem State_A Label) (e : AlterSeq State_A Label)
    (h_term : e.trans.Terminates) (l : Label) (s : State_A)
    (h_ext : ¬ ls.internal l) :
    ls.IsTight ⟨e.init, e.trans.append (Seq.cons (l, s) Seq.nil)⟩ := by
  -- IsTight: TerminatedAt 0 (trans empty) OR ∃ external label at position n
  -- with TerminatedAt (n+1). Use the second disjunct with n = Nat.find h_term.
  right
  refine ⟨Nat.find h_term, l, s, ?_, ?_, h_ext⟩
  · -- get? at Nat.find h_term gives the appended (l, s).
    change (e.trans.append (Seq.cons (l, s) Seq.nil)).get? (Nat.find h_term) = some (l, s)
    have := Stream'.Seq.get?_append_find h_term (Seq.cons (l, s) Seq.nil) 0
    rw [Nat.add_zero] at this
    rw [this]
    rfl
  · -- TerminatedAt (Nat.find h_term + 1) by terminatedAt_append_find.
    change (e.trans.append (Seq.cons (l, s) Seq.nil)).TerminatedAt (Nat.find h_term + 1)
    exact Stream'.Seq.terminatedAt_append_find h_term
      (show (Seq.cons (l, s) Seq.nil).TerminatedAt 1 from rfl)

/-- **`tightExecsA_characterisation` — empty-trans case**: tight + trace nil
iff trans empty. (Provided by the existing `trans_nil_of_tight_trace_nil`
and the reverse direction is trivial.) -/
theorem tightExecsA_trans_nil_iff
    (ls : LabelledSystem State_A Label) (e : AlterSeq State_A Label) :
    (ls.trace e = Seq.nil ∧ ls.IsTight e) ↔ e.trans = Seq.nil := by
  refine ⟨fun ⟨h_trace, h_tight⟩ => ?_, fun h_nil => ?_⟩
  · exact trans_nil_of_tight_trace_nil ls e h_trace h_tight
  · refine ⟨?_, ?_⟩
    · rw [show e = ⟨e.init, e.trans⟩ from rfl, h_nil]
      exact ls.trace_init e.init
    · left
      rw [h_nil]; exact Stream'.Seq.terminatedAt_nil

/-- **`tightExecsA_characterisation` (§9.2 — useful form)**: a tight
finite execution `e_A` either has empty trans (and τ = nil) or has a
last position with an external label matching the trace's last entry.

In its full plan-§9.2 form, the bijection between `TightExecsA(τ)` and
list-based structural data uses Fin n → Bool/Label/State_A. We provide
the practical decomposition needed for §9.5's induction via the
structural lemmas `tightExec_has_external_last` (extracts the last
external position) and `isTight_append_external` (constructs tight
executions by appending an external transition). -/
theorem tightExecsA_characterisation
    (ls : LabelledSystem State_A Label) (e : AlterSeq State_A Label)
    (h_term : e.trans.Terminates) (h_tight : ls.IsTight e) :
    e.trans = Seq.nil ∨
    ∃ (n : ℕ) (l_last : Label) (s_last : State_A),
      e.trans.get? n = some (l_last, s_last) ∧
      e.trans.TerminatedAt (n + 1) ∧
      ¬ ls.internal l_last := by
  rcases h_tight with h_t0 | h_n
  · left; exact Stream'.Seq.terminatedAt_zero_iff.mp h_t0
  · right; exact h_n

/-- **Build the matching abstract trans-list**: given a concrete trans-list
and a list of abstract states of matching length, zip the labels from the
former with the states from the latter. Used to re-parameterise the
s_A-marginal of joint_mass_path. -/
private def buildToListA (toList_C : List (Label × State_C))
    (s_A_list : List State_A) : List (Label × State_A) :=
  List.zipWith (fun p s_A => (p.1, s_A)) toList_C s_A_list

/-- **Cons-equiv for length-restricted lists**: `α × {l // l.length = n} ≃
{l // l.length = n+1}` via `(a, t) ↦ a :: t`. Used to re-index the
s_A_list-sum in `joint_mass_path_marginal_s_A_aux`'s step case. -/
private noncomputable def consSubtypeEquiv {α : Type} (n : ℕ) :
    α × {l : List α // l.length = n} ≃ {l : List α // l.length = n + 1} :=
  Equiv.ofBijective
    (fun p => ⟨p.1 :: p.2.1, by simp [p.2.2]⟩) <| by
      refine ⟨?_, ?_⟩
      · -- Injective
        rintro ⟨a, ⟨la, ha⟩⟩ ⟨b, ⟨lb, hb⟩⟩ h_eq
        have h := Subtype.ext_iff.mp h_eq
        simp only [List.cons.injEq] at h
        obtain ⟨h_head, h_tail⟩ := h
        cases h_head
        congr 1
        exact Subtype.ext h_tail
      · -- Surjective
        rintro ⟨l, h_len⟩
        cases l with
        | nil => simp at h_len
        | cons a t =>
          refine ⟨(a, ⟨t, ?_⟩), ?_⟩
          · simpa using h_len
          · rfl

/-- **List-level s_A-marginal of joint_mass_path** (§9.4 auxiliary):
summing `joint_mass_path m toList_C (buildToListA toList_C s_A_list)` over
all `s_A_list` of length `toList_C.length` equals
`pe_C.probOfRemaining m.e_C toList_C`, for matching states `m` with a
valid R-witness. The proof is by induction on `toList_C`; the step case
uses the s_A-marginal of `μ_A_next.s_A = 1`, the m_1 indicator collapse
(via `MatchingState.ext_of_data`), the γ-first-marginal
(`PMFRelDecomp.fst_apply_eq_tsum`), and `probOfRemaining_cons`.

The `has_valid_R` hypothesis is required: at non-valid `m`,
`joint_mass_path m _ _ = 0` regardless of toList_C, but
`pe_C.probOfRemaining m.e_C toList_C` may be nonzero. The recursive
applications in the step case have `h_valid` automatic because the
canonical extension's μ_A_chain is non-empty (the `Or.inl` disjunct
of `has_valid_R`). -/
private lemma joint_mass_path_marginal_s_A_aux
    {sim : ProbabilisticForwardSimulation sys_C sys_A R}
    {pe_C : ProbabilisticExecution sys_C.toSystem}
    {μ_A_init : PMF State_A}
    {h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init}
    (toList_C : List (Label × State_C)) :
    ∀ (m : MatchingState sim pe_C μ_A_init h_init_R),
      m.has_valid_R →
      (∑' (s_A_list : {l : List State_A // l.length = toList_C.length}),
          joint_mass_path m toList_C (buildToListA toList_C s_A_list.1)) =
      pe_C.probOfRemaining m.e_C toList_C := by
  classical
  induction toList_C with
  | nil =>
    intro m _h_valid
    -- The subtype `{l : List State_A // l.length = ([] : List _).length}` reduces to
    -- `{l // l.length = 0}` which has the unique element `[]`.
    show (∑' (s_A_list : {l : List State_A // l.length = ([] : List (Label × State_C)).length}),
        joint_mass_path m [] (buildToListA [] s_A_list.1)) =
        pe_C.probOfRemaining m.e_C []
    simp only [List.length_nil]
    rw [tsum_eq_single (⟨[], rfl⟩ : {l : List State_A // l.length = 0})]
    · change joint_mass_path m [] (buildToListA [] []) = pe_C.probOfRemaining m.e_C []
      unfold buildToListA
      simp only [List.zipWith_nil_left]
      rfl
    · rintro ⟨l, hl⟩ h_ne
      exfalso
      apply h_ne
      have : l = [] := List.length_eq_zero_iff.mp hl
      exact Subtype.ext this
  | cons hd rest ih =>
    intro m h_valid
    classical
    -- Apply probOfRemaining_cons on the RHS: pe_C.probOfRemaining m.e_C (hd :: rest)
    --   = pe_C.kernel m.e_C hd * pe_C.probOfRemaining (m.e_C extended by hd) rest.
    rw [ProbabilisticExecution.probOfRemaining_cons]
    -- Case-split on whether pe_C's scheduler is active at m.e_C.
    by_cases h_some : (pe_C.scheduler.next m.e_C).isSome
    swap
    · -- ¬h_some: pe_C halted, both sides are 0.
      -- LHS: joint_mass_path = 0 (cons branch returns 0 under ¬h_some).
      -- RHS: pe_C.kernel m.e_C hd = 0 (kernel uses scheduler.next).
      have h_LHS : (∑' (s_A_list : {l : List State_A // l.length = (hd :: rest).length}),
          joint_mass_path m (hd :: rest) (buildToListA (hd :: rest) s_A_list.1)) = 0 := by
        apply ENNReal.tsum_eq_zero.mpr
        rintro ⟨s_A_list, h_len⟩
        -- s_A_list has length rest.length + 1 ≥ 1, so it's a cons.
        cases s_A_list with
        | nil => simp at h_len
        | cons s_A rest_s_A_list =>
          change joint_mass_path m (hd :: rest)
            (buildToListA (hd :: rest) (s_A :: rest_s_A_list)) = 0
          unfold buildToListA
          rw [List.zipWith_cons_cons]
          show joint_mass_path m (hd :: rest) ((hd.1, s_A) ::
            List.zipWith (fun p s_A => (p.1, s_A)) rest rest_s_A_list) = 0
          unfold joint_mass_path
          simp only [dif_neg h_some, dif_pos h_valid, if_pos]
      rw [h_LHS]
      -- RHS: pe_C.kernel m.e_C hd = 0.
      have h_kernel : pe_C.kernel m.e_C hd = 0 := by
        unfold ProbabilisticExecution.kernel
        rcases h_eq : pe_C.scheduler.next m.e_C with _ | d
        · simp
        · exfalso; rw [h_eq] at h_some; simp at h_some
      rw [h_kernel, zero_mul]
    -- h_some: main case. Set up d and h_d_eq.
    set d : PMF (Label × PMF State_C) := (pe_C.scheduler.next m.e_C).get h_some with hd_def
    have h_d_eq : pe_C.scheduler.next m.e_C = some d := Option.eq_some_of_isSome h_some
    -- Step 1: re-index the s_A_list sum to State_A × {l // l.length = rest.length}.
    rw [show (∑' (s_A_list : {l : List State_A // l.length = (hd :: rest).length}),
              joint_mass_path m (hd :: rest) (buildToListA (hd :: rest) s_A_list.1)) =
            ∑' (p : State_A × {l : List State_A // l.length = rest.length}),
              joint_mass_path m (hd :: rest)
                (buildToListA (hd :: rest) (consSubtypeEquiv rest.length p).1) from
        (Equiv.tsum_eq (consSubtypeEquiv rest.length) _).symm]
    -- The (consSubtypeEquiv n p).1 = p.1 :: p.2.1, so buildToListA gives (hd.1, p.1) :: ...
    simp only [consSubtypeEquiv, Equiv.ofBijective, Equiv.coe_fn_mk]
    -- After Equiv simp, the sum body has explicit s_A :: rest_s_A_list form. The remaining
    -- substitution + integration manipulation is documented in the inline comments.
    -- Step 2: split the product tsum into s_A then rest_s_A_list.
    rw [ENNReal.tsum_prod']
    -- Step 3: unfold buildToListA on cons-cons.
    simp only [buildToListA, List.zipWith_cons_cons]
    -- Step 4: unfold joint_mass_path's outer cons-cons branch.
    have h_body : ∀ (s_A : State_A) (rest_s_A_list : List State_A),
        joint_mass_path m (hd :: rest)
          ((hd.1, s_A) :: List.zipWith (fun p s_A => (p.1, s_A)) rest rest_s_A_list) =
        ∑' (μ_C : PMF State_C), d (hd.1, μ_C) * (
          if h_supp : (hd.1, μ_C) ∈ d.support then
            ∑' (μ_A_next : PMF State_A),
              (PMFRel.decomp (sim.stepWitness_pmfRel (m.current_R h_valid)
                  (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq hd.1 μ_C h_supp))
              ).γ (hd.2, μ_A_next) * μ_A_next s_A *
              ∑' (m_next : MatchingState sim pe_C μ_A_init h_init_R),
                (if m_next.e_C = ⟨m.e_C.init,
                      m.e_C.trans.append (Seq.cons (hd.1, hd.2) Seq.nil)⟩ ∧
                    m_next.μ_A_chain = m.μ_A_chain ++ [μ_A_next]
                  then 1 else 0) *
                joint_mass_path m_next rest
                  (List.zipWith (fun p s_A => (p.1, s_A)) rest rest_s_A_list)
          else 0) := by
      intro s_A rest_s_A_list
      -- The cons-cons branch of joint_mass_path unfolds to the if/dif tree;
      -- under labels-match (rfl), h_valid, h_some, it equals the integration expr.
      change (open Classical in
        if (hd.1, hd.2).1 = (hd.1, s_A).1 then
          if h_valid : m.has_valid_R then
            if h_some : (pe_C.scheduler.next m.e_C).isSome then
              ∑' (μ_C : PMF State_C),
                ((pe_C.scheduler.next m.e_C).get h_some) ((hd.1, s_A).1, μ_C) *
                (if h_supp : ((hd.1, s_A).1, μ_C) ∈
                      ((pe_C.scheduler.next m.e_C).get h_some).support then
                   ∑' (μ_A_next : PMF State_A),
                     (PMFRel.decomp (sim.stepWitness_pmfRel (m.current_R h_valid)
                         (pe_C_step_witness pe_C m.e_C m.e_C_term _
                           (Option.eq_some_of_isSome h_some) (hd.1, s_A).1 μ_C h_supp))
                     ).γ ((hd.1, hd.2).2, μ_A_next) * μ_A_next (hd.1, s_A).2 *
                     ∑' (m_next : MatchingState sim pe_C μ_A_init h_init_R),
                       (if m_next.e_C = ⟨m.e_C.init,
                             m.e_C.trans.append (Seq.cons ((hd.1, hd.2).1, (hd.1, hd.2).2) Seq.nil)⟩ ∧
                           m_next.μ_A_chain = m.μ_A_chain ++ [μ_A_next]
                         then 1 else 0) *
                       joint_mass_path m_next rest
                         (List.zipWith (fun p s_A => (p.1, s_A)) rest rest_s_A_list)
                 else 0)
            else 0
          else 0
        else 0) = _
      rw [if_pos rfl, dif_pos h_valid, dif_pos h_some]
    simp_rw [h_body]
    -- Goal (LHS): ∑' a, ∑' b, ∑' μ_C, d (hd.1, μ_C) * F(a, b, μ_C).
    -- Plan: show LHS = ∑' μ_C, d (hd.1, μ_C) * (if h_supp then μ_C hd.2 else 0)
    --              * pe_C.probOfRemaining canonical rest,
    -- where canonical = ⟨m.e_C.init, m.e_C.trans.append (Seq.cons hd Seq.nil)⟩.
    -- Then the d-supported part equals pe_C.kernel m.e_C hd (by joint_kernel_marginal_s_A's
    -- last-stage identity), multiplied by pe_C.probOfRemaining canonical rest.
    -- Naming the canonical extension simplifies all subsequent rewrites.
    set canonical : AlterSeq State_C Label :=
      ⟨m.e_C.init, m.e_C.trans.append (Seq.cons hd Seq.nil)⟩ with h_canon_def
    -- For a given μ_C with (hd.1, μ_C) ∈ d.support, abbreviate γ-decomp:
    --   γ_at(μ_C, h_supp) := the γ-PMF over State_C × PMF State_A.
    -- Step 5: bring μ_C outermost (swap a↔b, then a↔μ_C inside b-sum, then b↔μ_C outer).
    rw [ENNReal.tsum_comm,
        tsum_congr (fun (_ : { l : List State_A // l.length = rest.length }) =>
                     ENNReal.tsum_comm),
        ENNReal.tsum_comm]
    -- Now: ∑' μ_C, ∑' b, ∑' a, d (hd.1, μ_C) * F(a, b, μ_C).
    -- Step 6: collapse the (b, a) sums inside the if-then-else.
    -- For each μ_C with h_supp, the inner ∑' a, ∑' b, ∑' μ_A_next, ... factors as
    --   ∑' μ_A_next, γ * (∑' a, μ_A_next a) * (∑' b, ∑' m_next, [ind] * jmp m_next rest ...)
    -- = ∑' μ_A_next, γ * 1 * (∑' m_next, [ind] * pe_C.probOfRemaining canonical rest)
    -- = pe_C.probOfRemaining canonical rest * ∑' μ_A_next, γ * [R-ind]
    -- = pe_C.probOfRemaining canonical rest * μ_C hd.2
    -- (the last by PMFRelDecomp.fst_apply_eq_tsum, since γ(hd.2, ·) integrates to μ_C hd.2).
    -- Then total: ∑' μ_C, d(hd.1, μ_C) * (if h_supp then μ_C hd.2 else 0) *
    --             pe_C.probOfRemaining canonical rest, which collapses to
    -- pe_C.kernel m.e_C hd * pe_C.probOfRemaining canonical rest.
    have h_inner : ∀ μ_C : PMF State_C,
        (∑' (b : { l // l.length = rest.length }) (a : State_A),
          d (hd.1, μ_C) *
            (if h_supp : (hd.1, μ_C) ∈ d.support then
              ∑' (μ_A_next : PMF State_A),
                (PMFRel.decomp (sim.stepWitness_pmfRel (m.current_R h_valid)
                    (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq hd.1 μ_C h_supp))
                ).γ (hd.2, μ_A_next) * μ_A_next a *
                ∑' (m_next : MatchingState sim pe_C μ_A_init h_init_R),
                  (if m_next.e_C = canonical ∧
                      m_next.μ_A_chain = m.μ_A_chain ++ [μ_A_next]
                    then 1 else 0) *
                  joint_mass_path m_next rest
                    (List.zipWith (fun p s_A => (p.1, s_A)) rest b.1)
            else 0)) =
        d (hd.1, μ_C) * μ_C hd.2 * pe_C.probOfRemaining canonical rest := by
      intro μ_C
      by_cases h_supp : (hd.1, μ_C) ∈ d.support
      · -- h_supp: pull d out and process the integration.
        rw [tsum_congr (fun (_ : { l : List State_A // l.length = rest.length }) =>
              ENNReal.tsum_mul_left),
            ENNReal.tsum_mul_left]
        rw [mul_assoc]
        congr 1
        simp only [dif_pos h_supp]
        -- Now: ∑' b, ∑' a, ∑' μ_A_next, γ * μ_A_next a * ∑' m_next, [ind] * jmp
        --   = μ_C hd.2 * pe_C.probOfRemaining canonical rest.
        -- Abbreviate the γ-decomposition (depends only on μ_C and h_supp).
        set γ : PMF (State_C × PMF State_A) :=
          (PMFRel.decomp (sim.stepWitness_pmfRel (m.current_R h_valid)
              (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq hd.1 μ_C h_supp))).γ
          with hγ_def
        -- Abbreviate the m_next-sum indicator (depends only on μ_A_next and b).
        -- This is now: ∑' b a μ_A_next, γ (hd.2, μ_A_next) * μ_A_next a *
        --                ∑' m_next, [ind μ_A_next] * jmp m_next rest (zw rest b.1).
        -- Reorder: bring μ_A_next outermost (3 swaps: b↔a, then a↔μ_A_next inside b, then b↔μ_A_next).
        rw [ENNReal.tsum_comm,
            tsum_congr (fun (_ : State_A) => ENNReal.tsum_comm),
            ENNReal.tsum_comm]
        -- Goal: ∑' μ_A_next, ∑' s_A, ∑' rest_s_A_list, γ (hd.2, μ_A_next) * μ_A_next s_A *
        --       ∑' m_next, [ind μ_A_next] * jmp m_next rest (zw rest rest_s_A_list.1)
        --   = μ_C hd.2 * pe_C.probOfRemaining canonical rest.
        -- Step A: for each μ_A_next, transform the (s_A, rest_s_A_list, m_next)-sums.
        -- The inner expression equals γ(hd.2, μ_A_next) * pOR whenever γ > 0 (R then holds,
        -- so the m_next-sum picks out canonical and jmp(canonical, ...) sums via IH to pOR;
        -- the s_A-sum of μ_A_next s_A = 1).
        -- When γ = 0, both sides are 0.
        have h_per : ∀ μ_A_next : PMF State_A,
            (∑' (s_A : State_A) (rest_s_A_list : { l // l.length = rest.length }),
              γ (hd.2, μ_A_next) * μ_A_next s_A *
                ∑' (m_next : MatchingState sim pe_C μ_A_init h_init_R),
                  (if m_next.e_C = canonical ∧
                      m_next.μ_A_chain = m.μ_A_chain ++ [μ_A_next]
                    then 1 else 0) *
                  joint_mass_path m_next rest
                    (List.zipWith (fun p s_A => (p.1, s_A)) rest rest_s_A_list.1)) =
            γ (hd.2, μ_A_next) * pe_C.probOfRemaining canonical rest := by
          intro μ_A_next
          by_cases h_γ : γ (hd.2, μ_A_next) = 0
          · simp [h_γ, tsum_zero]
          · -- γ > 0 → R hd.2 μ_A_next holds.
            have h_R : R hd.2 μ_A_next := by
              have h_supp_γ : (hd.2, μ_A_next) ∈ γ.support := by
                rw [PMF.mem_support_iff]; exact h_γ
              have := (PMFRel.decomp (sim.stepWitness_pmfRel (m.current_R h_valid)
                  (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq hd.1 μ_C h_supp))).h_R
                (hd.2, μ_A_next)
              rw [← hγ_def] at this
              exact this h_supp_γ
            -- Step: factor γ out of s_A-sum (both inner parts µ_A_next s_A and
            -- m_next-sum don't depend on s_A's value in the µ_A_next-sum sense...).
            -- Pull γ(hd.2, μ_A_next) out via mul_assoc.
            simp_rw [mul_assoc, ENNReal.tsum_mul_left]
            congr 1
            -- Goal: ∑' s_A, μ_A_next s_A * (∑' rest_s_A_list, ∑' m_next, [ind] * jmp).
            -- Pull μ_A_next s_A out of (a constant in) rest_s_A_list-sum to factor s_A-sum.
            rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
            -- Goal: ∑' rest_s_A_list, ∑' m_next, [ind] * jmp = pOR(canonical).
            -- Swap rest_s_A_list and m_next, then pull [ind] out per m_next.
            rw [ENNReal.tsum_comm]
            simp_rw [ENNReal.tsum_mul_left]
            -- ∑' m_next, [ind] * (∑' rest_s_A_list, jmp m_next rest (zw rest rest_s_A_list.1)).
            -- For each m_next: case-split on the indicator; if true, apply IH.
            have h_per_mn : ∀ m_next : MatchingState sim pe_C μ_A_init h_init_R,
                (if m_next.e_C = canonical ∧
                    m_next.μ_A_chain = m.μ_A_chain ++ [μ_A_next] then (1 : ENNReal) else 0) *
                  (∑' (rest_s_A_list : { l // l.length = rest.length }),
                    joint_mass_path m_next rest
                      (List.zipWith (fun p s_A => (p.1, s_A)) rest rest_s_A_list.1)) =
                (if m_next.e_C = canonical ∧
                    m_next.μ_A_chain = m.μ_A_chain ++ [μ_A_next] then (1 : ENNReal) else 0) *
                  pe_C.probOfRemaining canonical rest := by
              intro m_next
              by_cases h_ind : m_next.e_C = canonical ∧
                  m_next.μ_A_chain = m.μ_A_chain ++ [μ_A_next]
              · rw [if_pos h_ind]
                have h_mn_valid : m_next.has_valid_R := by
                  left; rw [h_ind.2]; exact List.concat_ne_nil μ_A_next m.μ_A_chain
                have h_ih := ih m_next h_mn_valid
                -- h_ih : ∑' s, jmp m_next rest (buildToListA rest s.1) = pOR(m_next.e_C) rest
                change (1 : ENNReal) * _ = (1 : ENNReal) * _
                rw [one_mul, one_mul]
                rw [show (∑' (s : { l // l.length = rest.length }),
                      joint_mass_path m_next rest
                        (List.zipWith (fun p s_A => (p.1, s_A)) rest s.1)) =
                    ∑' (s : { l // l.length = rest.length }),
                      joint_mass_path m_next rest (buildToListA rest s.1) from rfl]
                rw [h_ih, h_ind.1]
              · rw [if_neg h_ind, zero_mul, zero_mul]
            rw [tsum_congr h_per_mn]
            -- Goal: ∑' m_next, [ind] * pOR(canonical) = pOR(canonical).
            rw [ENNReal.tsum_mul_right,
                matchingState_indicator_sum_eq_one m hd.1 hd.2 μ_A_next h_R, one_mul]
        rw [tsum_congr h_per]
        -- Goal: ∑' μ_A_next, γ (hd.2, μ_A_next) * pe_C.probOfRemaining canonical rest
        --   = μ_C hd.2 * pe_C.probOfRemaining canonical rest.
        rw [ENNReal.tsum_mul_right]
        congr 1
        -- Goal: ∑' μ_A_next, γ (hd.2, μ_A_next) = μ_C hd.2.
        rw [← (PMFRel.decomp (sim.stepWitness_pmfRel (m.current_R h_valid)
            (pe_C_step_witness pe_C m.e_C m.e_C_term d h_d_eq hd.1 μ_C h_supp))).fst_apply_eq_tsum hd.2]
      · -- ¬h_supp: d (hd.1, μ_C) = 0.
        have h_d0 : d (hd.1, μ_C) = 0 := by
          rw [PMF.mem_support_iff] at h_supp
          push Not at h_supp
          exact h_supp
        rw [h_d0]
        simp [tsum_zero]
    -- Apply h_inner. The current outer LHS has the form
    --   ∑' μ_C, ∑' a (= rest_s_A_list), ∑' a_1 (= s_A), d * (if ...).
    -- h_inner has the form ∑' b (= rest_s_A_list), ∑' a (= s_A), d * (if ...).
    -- So after pulling μ_C outside and ignoring its order, we just need to apply h_inner.
    rw [tsum_congr h_inner]
    -- Goal: ∑' μ_C, d (hd.1, μ_C) * μ_C hd.2 * pOR = pe_C.kernel * pOR.
    rw [ENNReal.tsum_mul_right]
    congr 1
    -- Goal: ∑' μ_C, d (hd.1, μ_C) * μ_C hd.2 = pe_C.kernel m.e_C hd.
    -- Use kernel definition + h_d_eq.
    unfold ProbabilisticExecution.kernel
    rw [h_d_eq, Option.elim_some, PMF.bind_apply, ENNReal.tsum_prod']
    -- ∑' l', ∑' μ_C, d (l', μ_C) * (PMF.map (l', ·) μ_C) hd
    have h_map : ∀ (l' : Label) (μ_C : PMF State_C),
        (PMF.map (fun s => (l', s)) μ_C) hd =
        (if hd.1 = l' then μ_C hd.2 else 0) := by
      intro l' μ_C
      rw [PMF.map_apply]
      by_cases h_l : hd.1 = l'
      · subst h_l
        rw [if_pos rfl]
        rw [tsum_eq_single hd.2 (fun s h_ne => by
          have h_neq : hd ≠ (hd.1, s) := fun h => h_ne (Prod.mk.inj h).2.symm
          simp [h_neq])]
        simp
      · rw [if_neg h_l]
        apply ENNReal.tsum_eq_zero.mpr
        intro s
        have : hd ≠ (l', s) := fun h => h_l (Prod.mk.inj h).1
        simp [this]
    simp_rw [h_map]
    rw [tsum_eq_single hd.1 (fun l' h_ne => ?_)]
    · -- l' = hd.1 case.
      apply tsum_congr
      intro μ_C
      rw [if_pos rfl]
    · -- l' ≠ hd.1: inner is 0.
      apply ENNReal.tsum_eq_zero.mpr
      intro μ_C
      rw [if_neg (Ne.symm h_ne), mul_zero]

/-- **§9.4**: marginalising the joint over `e_A`'s state samples
recovers `pe_C.probOf e_C`. Proven by composing per-step
`joint_kernel_marginal_s_A` across the trajectory. -/
theorem joint_marginalises_to_pe_C
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (μ_A_init : PMF State_A)
    (h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init)
    (e_C : AlterSeq State_C Label) (e_C_term : e_C.trans.Terminates) :
    -- Summing joint_mass over (e_A : AlterSeq) with |e_A.trans| = |e_C.trans|
    -- and labels matching step-by-step yields pe_C.probOf e_C.
    -- The summation includes the choice of e_A.init: the μ_A_init(e_A.init)
    -- factor on the LHS is absorbed by ∑' init_A, μ_A_init(init_A) = 1
    -- (PMF total mass).
    (∑' (e_A : {e_A : AlterSeq State_A Label //
                ∃ h_term : e_A.trans.Terminates,
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
