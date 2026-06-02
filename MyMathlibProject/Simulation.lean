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

/-! ### Matching-state machinery for `exists_coupling`

The challenge in constructing `pe_A` is: for each abstract prefix `e_A`, the
scheduler must emit a next step that emulates whatever `pe_C` does at a
*matching* concrete prefix. The matching is non-trivial because one concrete
step lifts (via `sim.step`) to a *weak* abstract transition — which unrolls
into a sequence of single abstract steps. The scheduler plays them one at
a time, tracking position both in the concrete trajectory and within the
current weak transition.

This section provides the data structures and helper functions that
encode this matching. -/

namespace ProbabilisticForwardSimulation

variable {State_C State_A Label : Type}
variable {sys_C : LabelledSystem State_C Label} {sys_A : LabelledSystem State_A Label}
variable {R : State_C → PMF State_A → Prop}

/-- A *weak-stage* identifies which step inside a weak transition the
abstract scheduler is about to emit.

A weak transition emulating a concrete step `(l_C, μ_C)`:
* **Internal `l_C`** — `weakTau`: a `WeakScheduler` with `runtime` steps
  running from `μ_A` to (flattened) `stepWitness.bind id`. The stage
  indexes the position in `0..runtime`.
* **External `l_C`** — `weakStep`: three phases:
  - A *pre*-`weakTau` `WeakScheduler` running from `μ_A` to some `μ_A'`.
  - One single labelled external step from `μ_A'` to (flattened intermediate).
  - A *post*-`weakTau` `WeakScheduler` running to the final distribution.
  The stage tracks which phase + position within. -/
inductive WeakStage where
  /-- Stage `k` of an internal weak transition's tau-scheduler. -/
  | tauInternal (k : ℕ) : WeakStage
  /-- Stage `k` of an external weak transition's *pre*-tau. -/
  | preExternal (k : ℕ) : WeakStage
  /-- About to emit the external label itself. -/
  | externalEmit : WeakStage
  /-- Stage `k` of an external weak transition's *post*-tau. -/
  | postExternal (k : ℕ) : WeakStage
  deriving DecidableEq

/-- Bundled data for the next-step transition in the matching state:
the concrete step being emulated, the post-step abstract distribution
to switch to, and the `R`-coupling witness. -/
structure NextStepData
    (State_C State_A Label : Type)
    (R : State_C → PMF State_A → Prop) where
  /-- The label of the concrete step. -/
  l_C : Label
  /-- The post-step concrete state (sampled from the concrete kernel). -/
  s_C' : State_C
  /-- The post-step abstract distribution to switch to. -/
  μ_A_next : PMF State_A
  /-- The new `R`-coupling: `R s_C' μ_A_next`. -/
  h_R_next : R s_C' μ_A_next

/-- The `hyperStep` witness data carried by `MatchingState` for external
weak transitions: the pre-emission distribution `μ_pre`, the external
label `l`, and a per-state kernel-distribution `State → PMF (PMF State)`
(matching `hyperStep`'s shape) with validity on `μ_pre.support`. Used by
`computeNext`'s `externalEmit` case to emit `(l, μ)` for each `μ` in
`(kernel m.cas).support` (assuming the support invariant on `m.cas`). -/
structure HyperWitness (sys_A : LabelledSystem State_A Label) where
  /-- The pre-emission abstract distribution (post-pretau in `weakStep`). -/
  μ_pre : PMF State_A
  /-- The external label being emitted. -/
  l : Label
  /-- The per-state kernel-distribution. -/
  kernel : State_A → PMF (PMF State_A)
  /-- Validity of `kernel` on `μ_pre.support`. -/
  valid : ∀ s ∈ μ_pre.support, ∀ μ ∈ (kernel s).support,
    sys_A.toSystem.step s l μ

/-- A *matching state*: the concrete prefix being emulated, the current
abstract distribution `R`-related to its end-state, and the in-flight
weak-transition stage.

This is the "private state" of `pe_A`'s scheduler — it accumulates as
abstract steps are taken and gets advanced according to `WeakStage`.

Fields:
* `e_C`: the concrete prefix walked so far.
* `h_term_C`: `e_C`'s termination proof (always finite).
* `μ_A_current`: the abstract distribution currently `R`-related to
  `e_C`'s end-state.
* `h_R`: the `R`-coupling witness, `R (e_C.endState h_term_C) μ_A_current`.
* `next_step`: bundled data for the concrete step the in-flight weak
  transition is emulating (with its post-step `μ_A_next` and the new
  `R`-coupling). `none` when no weak transition is in flight.
* `weak_sched`: `Option (WeakScheduler sys_A)`. When `some σ`, we are
  in the middle of executing the weak transition driven by `σ` (from
  `sim.step`'s witness); when `none`, the previous weak transition has
  completed and the next abstract step should start a fresh one.
* `stage`: position within the current weak transition. Meaningful only
  when `weak_sched = some σ` (otherwise reset to `tauInternal 0`). -/
structure MatchingState (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem) where
  /-- The concrete prefix walked so far. -/
  e_C : AlterSeq State_C Label
  /-- Termination proof for the concrete prefix. -/
  h_term_C : e_C.trans.Terminates
  /-- The current abstract distribution `R`-related to `e_C`'s end-state. -/
  μ_A_current : PMF State_A
  /-- Witness of the `R`-coupling between the concrete end-state and the
  current abstract distribution. -/
  h_R : R (e_C.endState h_term_C) μ_A_current
  /-- Bundled data for the next concrete step being emulated. -/
  next_step : Option (NextStepData State_C State_A Label R)
  /-- The `WeakScheduler` driving the current weak transition.
  `none` means "no weak transition in flight — start a fresh one next". -/
  weak_sched : Option (WeakScheduler sys_A)
  /-- The post-`externalEmit` `WeakScheduler` for external weak transitions
  (the post-tau of `weakStep`). Used when `stage` advances to
  `postExternal 0`; at that point `weak_sched` is replaced by this. -/
  post_weak_sched : Option (WeakScheduler sys_A)
  /-- Position within the current weak transition. Only meaningful when
  `weak_sched` is `some σ`. -/
  stage : WeakStage
  /-- The abstract state the execution is currently at. Maintained as
  the end-state of the abstract prefix walked so far; for the matching
  state derived via `fromAbstractPrefix e_A`, this equals `e_A.endState`.
  Used by `computeNext` and validity proofs to align with `μ_A_current`. -/
  current_abstract_state : State_A
  /-- Optional `hyperStep` witness for the in-flight external weak
  transition. Populated by `setupNextTransition` in the external case;
  cleared by `extendOnCompletion`. Read by `computeNext`'s
  `externalEmit` case to emit `(witness.l, witness.kernel m.cas)`. -/
  hyper_witness : Option (HyperWitness sys_A)

namespace MatchingState

variable {sim : ProbabilisticForwardSimulation sys_C sys_A R}
variable {pe_C : ProbabilisticExecution sys_C.toSystem}

-- A `currentAbstractState` accessor (sampling from `μ_A_current` at the
-- position dictated by `stage`) is deferred: it depends on how `stage`
-- indexes into the weak-transition unrolling, which itself comes from
-- `sim.step`. To be filled in alongside `computeNext` below.

/-- Bridge `WeakScheduler.next`'s output (`PMF (Option α)`) to our
`Scheduler.next` shape (`Option (PMF α)`).

* If the input PMF has any `some` element in its support, return
  `some (PMF.pure ⟨…⟩)` where `⟨…⟩` is Classical-chosen from the
  `some`-supported elements.
* Else (the PMF is concentrated on `none`), return `none` (the
  scheduler stops).

This is a coarse bridge — it collapses the input PMF's distribution to
a single-step `PMF.pure` emit, losing proportional information. A
finer bridge should `condition` on the `some` mass to preserve
probabilities. -/
noncomputable def liftOption {α : Type*} (p : PMF (Option α)) :
    Option (PMF α) :=
  letI : Decidable (∃ a, some a ∈ p.support) := Classical.propDecidable _
  if h : ∃ a, some a ∈ p.support then some (PMF.pure h.choose) else none

lemma liftOption_eq_some_iff {α : Type*} (p : PMF (Option α)) (q : PMF α) :
    liftOption p = some q ↔
      ∃ (h : ∃ a, some a ∈ p.support), q = PMF.pure h.choose := by
  classical
  unfold liftOption
  split_ifs with h
  · refine ⟨?_, ?_⟩
    · intro h_eq
      exact ⟨h, (Option.some.inj h_eq).symm⟩
    · rintro ⟨_, rfl⟩; rfl
  · simp only [false_iff, not_exists]
    intro h_ex _
    exact h h_ex

/-- Compute the next abstract step from a matching state. Structurally
case-analyzes on `m.weak_sched` × `m.stage`:

* `weak_sched = none`:
  - Consult `pe_C.scheduler.next m.e_C`.
  - If `none`, the concrete side has stopped; emit `none`.
  - If `some d`, sample `(l_C, μ_C)` from `d` and use `sim.step`
    to produce the corresponding abstract step. The simplest
    realization: `PMF.bind` over `d` mirroring the concrete distribution.
    The "first step of the weak transition" we'd emit depends on
    whether `l_C` is internal/external and the structure of the
    weak transition. For *now* we collapse the weak-transition
    unrolling by emitting the step `(l_C, μ_A_next.bind id)` where
    `μ_A_next` comes from a `Classical.choice` over `sim.step`'s
    `stepWitness`. This skips intermediate `tau` stages — the
    trace-coupling proof will need to argue this is sound, OR a
    future refinement will properly unroll the weak transition.

* `weak_sched = some σ` with `stage = externalEmit`: emit
  `PMF.pure (l_C, μ_A_next)` from `next_step`.

* `weak_sched = some σ` with mid-tau stages: emit `σ.next`. Deferred. -/
noncomputable def computeNext (m : MatchingState sim pe_C) :
    Option (PMF (Label × PMF State_A)) :=
  match m.weak_sched, m.stage with
  | none, _ =>
    match pe_C.scheduler.next m.e_C with
    | none =>
      -- pe_C stopped; abstract side stops too.
      none
    | some _ =>
      -- pe_C has a step distribution to emit, but setting up the
      -- corresponding abstract weak transition requires Classical
      -- extraction from `sim.step`. **Deferred** — returns `none`
      -- for now; a future refinement will:
      --   1. Sample `(l_C, μ_C)` from `d` via PMF.bind.
      --   2. Apply `sim.step` (using `m.h_R`) to get `stepWitness`.
      --   3. Build a fresh `WeakScheduler` from
      --      `stepWitness_weakTau` (internal) or `stepWitness_weakStep`
      --      (external).
      --   4. Update the matching state's `weak_sched`, `next_step`,
      --      `stage`. (Note: this requires `computeNext` to also
      --      return state updates, or the work to be split with
      --      `advance` initialization.)
      none
  | some _, WeakStage.externalEmit =>
    match m.hyper_witness with
    | none => none
    | some w =>
      letI : Decidable (m.current_abstract_state ∈ w.μ_pre.support) :=
        Classical.propDecidable _
      if m.current_abstract_state ∈ w.μ_pre.support then
        some ((w.kernel m.current_abstract_state).map (Prod.mk w.l))
      else
        none
  | some σ, _ =>
    -- Mid-tau cases (tauInternal/preExternal/postExternal): bridge
    -- `WeakScheduler.next : AlterSeq → PMF (Option (l, μ))` to our
    -- `Scheduler.next : AlterSeq → Option (PMF (l, μ))` via
    -- `MatchingState.liftOption`. The query state is
    -- `m.current_abstract_state` (the actual abstract state at this
    -- prefix), so `σ.valid` directly gives validity for the emission.
    MatchingState.liftOption
      (σ.next ⟨m.current_abstract_state, Seq.nil⟩)

/-- Helper used by `advance`: on weak-transition completion, install
the next weak transition based on `pe_C.scheduler.next m.e_C`.

When `some d`, we Classical-extract:
* `(l_C, μ_C) ∈ d.support` (the concrete step).
* `s_C' ∈ μ_C.support` (the post-step concrete state).
* `h_step : sys_C.step (endState e_C) l_C μ_C` (from
  `pe_C.scheduler.valid`).
* The remaining steps — sim.step's stepWitness, PMFRel extraction for
  `μ_A_next`, WeakScheduler from `stepWitness_weakTau` /
  `stepWitness_weakStep` — are deferred. The current implementation
  populates `next_step` (via Classical placeholder for `μ_A_next` and
  its R-witness) but leaves `weak_sched = none` until the full
  extraction lands. -/
noncomputable def setupNextTransition (m : MatchingState sim pe_C) :
    MatchingState sim pe_C :=
  match h_d : pe_C.scheduler.next m.e_C with
  | none => m
  | some d =>
    let pair := d.support_nonempty.choose
    let h_pair_supp : pair ∈ d.support := d.support_nonempty.choose_spec
    let l_C := pair.1
    let μ_C := pair.2
    let s_C' := μ_C.support_nonempty.choose
    let h_s_C'_supp : s_C' ∈ μ_C.support := μ_C.support_nonempty.choose_spec
    let h_step : sys_C.toSystem.step (m.e_C.endState m.h_term_C) l_C μ_C :=
      pe_C.scheduler.valid m.e_C (Nat.find m.h_term_C)
        (m.e_C.endState m.h_term_C) (Nat.find_spec m.h_term_C)
        (AlterSeq.stateAt_find_eq_endState m.e_C m.h_term_C) d h_d l_C μ_C
        (show (l_C, μ_C) ∈ d.support from h_pair_supp)
    let ω : PMF (PMF State_A) := sim.stepWitness m.h_R h_step
    let h_pmfRel : PMFRel R μ_C ω := sim.stepWitness_pmfRel m.h_R h_step
    let γ : PMF (State_C × PMF State_A) := h_pmfRel.choose
    let h_pmfRel_spec := h_pmfRel.choose_spec
    let h_marg_fst : PMF.map Prod.fst γ = μ_C := h_pmfRel_spec.1
    let h_R_on_supp : ∀ p ∈ γ.support, R p.1 p.2 := h_pmfRel_spec.2.2
    let h_s_C'_in_map_raw : s_C' ∈ (PMF.map Prod.fst γ).support :=
      h_marg_fst ▸ h_s_C'_supp
    let h_s_C'_in_map : s_C' ∈ Prod.fst '' γ.support :=
      PMF.support_map _ _ ▸ h_s_C'_in_map_raw
    let p : State_C × PMF State_A := h_s_C'_in_map.choose
    let h_p_spec := h_s_C'_in_map.choose_spec
    let h_p_supp : p ∈ γ.support := h_p_spec.1
    let h_p_fst : p.1 = s_C' := h_p_spec.2
    let μ_A_next : PMF State_A := p.2
    let h_R_next : R s_C' μ_A_next := h_p_fst ▸ h_R_on_supp p h_p_supp
    letI : Decidable (sys_C.internal l_C) := Classical.propDecidable _
    if h_int : sys_C.internal l_C then
      let σ : WeakScheduler sys_A :=
        (sim.stepWitness_weakTau m.h_R h_step h_int).choose
      { m with
        weak_sched := some σ
        next_step := some ⟨l_C, s_C', μ_A_next, h_R_next⟩
        stage := WeakStage.tauInternal 0 }
    else
      let h_step_w : weakStep sys_A m.μ_A_current l_C (ω.bind id) :=
        sim.stepWitness_weakStep m.h_R h_step h_int
      let μ_inter : PMF State_A := h_step_w.choose
      let h_step_w_spec := h_step_w.choose_spec
      let μ_inter' : PMF State_A := h_step_w_spec.choose
      let h_step_w_spec_2 := h_step_w_spec.choose_spec
      let h_pre : weakTau sys_A m.μ_A_current μ_inter := h_step_w_spec_2.1
      let h_hyper : hyperStep sys_A.toSystem μ_inter l_C μ_inter' :=
        h_step_w_spec_2.2.1
      let h_post : weakTau sys_A μ_inter' (ω.bind id) := h_step_w_spec_2.2.2
      let σ_pre : WeakScheduler sys_A := h_pre.choose
      let σ_post : WeakScheduler sys_A := h_post.choose
      { m with
        weak_sched := some σ_pre
        post_weak_sched := some σ_post
        next_step := some ⟨l_C, s_C', μ_A_next, h_R_next⟩
        stage := WeakStage.preExternal 0
        hyper_witness := some
          { μ_pre := μ_inter
            l := l_C
            kernel := h_hyper.kernel
            valid := h_hyper.kernel_step } }

/-- Helper used by `advance`: on weak-transition completion, extend
`e_C` by `next_step` if present, then call `setupNextTransition` to
install the next weak transition. -/
noncomputable def extendOnCompletion (m : MatchingState sim pe_C) :
    MatchingState sim pe_C :=
  let extended : MatchingState sim pe_C :=
    match m.next_step with
    | none =>
      { m with weak_sched := none, post_weak_sched := none, stage := WeakStage.tauInternal 0 }
    | some ⟨l_C, s_C', μ_A_next, h_R_next⟩ =>
      { e_C := ⟨m.e_C.init, m.e_C.trans.append (Seq.cons (l_C, s_C') Seq.nil)⟩
        h_term_C := ⟨Nat.find m.h_term_C + 1,
          Stream'.Seq.terminatedAt_append_find m.h_term_C
            (show (Seq.cons (l_C, s_C') Seq.nil).TerminatedAt 1 from rfl)⟩
        μ_A_current := μ_A_next
        h_R := (AlterSeq.endState_append_singleton m.e_C m.h_term_C l_C s_C').symm ▸ h_R_next
        next_step := none
        weak_sched := none
        post_weak_sched := none
        stage := WeakStage.tauInternal 0
        current_abstract_state := m.current_abstract_state
        hyper_witness := none }
  setupNextTransition extended

/-- Advance the matching state after the abstract scheduler emitted a step
`(l_A, μ_A')`. State-machine on `m.weak_sched` + `m.stage`:

* `weak_sched = none`: no weak transition in flight; returns `m` unchanged.
* `weak_sched = some σ`:
  - `tauInternal k`: advance within (`k + 1 < σ.runtime`) or, on
    completion, append `next_concrete_step` to `e_C` via
    `extendOnCompletion`.
  - `preExternal k`: advance within, or on completion transition to
    `externalEmit`.
  - `externalEmit`: → `postExternal 0`.
  - `postExternal k`: like `tauInternal k`.

Remaining semantic gap: `μ_A_current` / `h_R` are held constant rather
than evolving with each stage transition; closing this requires
threading `σ.runFromState`-derived distributions. -/
noncomputable def advance (m : MatchingState sim pe_C)
    (_l_A : Label) (s_A' : State_A) :
    MatchingState sim pe_C :=
  let m' := { m with current_abstract_state := s_A' }
  match m'.weak_sched with
  | none => m'
  | some σ =>
    match m'.stage with
    | WeakStage.tauInternal k =>
      if k + 1 < σ.runtime then
        { m' with stage := WeakStage.tauInternal (k + 1) }
      else
        m'.extendOnCompletion
    | WeakStage.preExternal k =>
      if k + 1 < σ.runtime then
        { m' with stage := WeakStage.preExternal (k + 1) }
      else
        { m' with stage := WeakStage.externalEmit }
    | WeakStage.externalEmit =>
      -- Transition from external-emit to the post-tau: swap weak_sched.
      { m' with
        weak_sched := m'.post_weak_sched
        post_weak_sched := none
        stage := WeakStage.postExternal 0 }
    | WeakStage.postExternal k =>
      if k + 1 < σ.runtime then
        { m' with stage := WeakStage.postExternal (k + 1) }
      else
        m'.extendOnCompletion

/-- `setupNextTransition` preserves `current_abstract_state`. -/
private lemma setupNextTransition_current_abstract_state
    (m : MatchingState sim pe_C) :
    m.setupNextTransition.current_abstract_state = m.current_abstract_state := by
  unfold MatchingState.setupNextTransition
  split
  · rfl
  · dsimp only
    split_ifs <;> rfl

/-- `extendOnCompletion` preserves `current_abstract_state`. -/
private lemma extendOnCompletion_current_abstract_state
    (m : MatchingState sim pe_C) :
    m.extendOnCompletion.current_abstract_state = m.current_abstract_state := by
  unfold MatchingState.extendOnCompletion
  rw [setupNextTransition_current_abstract_state]
  cases m.next_step with
  | none => rfl
  | some d => rfl

/-- `advance` sets `current_abstract_state := s_A'`. -/
private lemma advance_current_abstract_state
    (m : MatchingState sim pe_C) (l_A : Label) (s_A' : State_A) :
    (MatchingState.advance m l_A s_A').current_abstract_state = s_A' := by
  unfold MatchingState.advance
  dsimp only
  split
  · rfl
  rename_i σ _
  split
  all_goals first
    | rfl
    | (split_ifs <;>
        first | rfl | exact extendOnCompletion_current_abstract_state _)

/-- `foldl advance` over a list `xs` ends at a state whose
`current_abstract_state` equals the foldl over `xs` taking the second
projection (starting from `m₀.current_abstract_state`). -/
private lemma foldl_advance_current_abstract_state
    (xs : List (Label × State_A)) (m₀ : MatchingState sim pe_C) :
    (xs.foldl (fun m p => MatchingState.advance m p.1 p.2) m₀).current_abstract_state =
    xs.foldl (fun _ p => p.2) m₀.current_abstract_state := by
  induction xs generalizing m₀ with
  | nil => rfl
  | cons head tail ih =>
    change (tail.foldl _ (MatchingState.advance m₀ head.1 head.2)).current_abstract_state =
      tail.foldl _ head.2
    rw [ih, advance_current_abstract_state]

end MatchingState

/-- The *initial* matching state for an abstract state `s_A`, given:
* `pe_C` and `init_match` from `exists_coupling`'s STEP 1.
* `h_match_R`: the `R`-coupling between concrete initial states and their
  matched abstract distributions.

Picks (via Classical) a concrete initial state `s_C ∈ pe_C.init.support`
with `s_A ∈ (init_match s_C).support`. The starting `MatchingState`:
* `e_C := ⟨s_C, Seq.nil⟩` (the trivial empty concrete prefix at `s_C`).
* `μ_A_current := init_match s_C`.
* `h_R := h_match_R s_C h_s_C_supp` (`R s_C (init_match s_C)`).
* `stage := tauInternal 0` (initial sentinel).
Returns `none` if no such concrete state exists. -/
noncomputable def MatchingState.initial
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (init_match : State_C → PMF State_A)
    (h_match_R : ∀ s_C, s_C ∈ pe_C.init.support → R s_C (init_match s_C))
    (s_A : State_A) :
    Option (MatchingState sim pe_C) :=
  letI : Decidable (∃ s_C, s_C ∈ pe_C.init.support ∧ s_A ∈ (init_match s_C).support) :=
    Classical.propDecidable _
  if h_exists : ∃ s_C, s_C ∈ pe_C.init.support ∧ s_A ∈ (init_match s_C).support then
    let s_C := h_exists.choose
    let h_s_C_supp : s_C ∈ pe_C.init.support := h_exists.choose_spec.1
    let h_endState :
        (⟨s_C, (Seq.nil : Seq (Label × State_C))⟩ :
          AlterSeq State_C Label).endState Stream'.Seq.terminates_nil = s_C := by
      have h_eq := AlterSeq.stateAt_find_eq_endState
        ({init := s_C, trans := Seq.nil} : AlterSeq State_C Label)
        Stream'.Seq.terminates_nil
      have h_find : Nat.find (Stream'.Seq.terminates_nil :
          (Seq.nil : Seq (Label × State_C)).Terminates) = 0 := by
        apply Nat.find_eq_zero _ |>.mpr; rfl
      rw [h_find] at h_eq
      exact (Option.some.inj h_eq).symm
    let base : MatchingState sim pe_C :=
      { e_C := ⟨s_C, Seq.nil⟩
        h_term_C := Stream'.Seq.terminates_nil
        μ_A_current := init_match s_C
        h_R := h_endState.symm ▸ h_match_R s_C h_s_C_supp
        next_step := none
        weak_sched := none
        post_weak_sched := none
        stage := WeakStage.tauInternal 0
        current_abstract_state := s_A
        hyper_witness := none }
    some base.setupNextTransition
  else
    none

/-- For each abstract prefix `e_A`, the (Classical) matching state that
the scheduler should consult to determine `compute_next e_A`. Computed by
threading `MatchingState.advance` through `e_A.trans` from the initial
matching state corresponding to `e_A.init`. -/
noncomputable def MatchingState.fromAbstractPrefix
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (init_match : State_C → PMF State_A)
    (h_match_R : ∀ s_C, s_C ∈ pe_C.init.support → R s_C (init_match s_C))
    (e_A : AlterSeq State_A Label) :
    Option (MatchingState sim pe_C) :=
  match MatchingState.initial sim pe_C init_match h_match_R e_A.init with
  | none => none
  | some m₀ =>
    letI : Decidable (e_A.trans.Terminates) := Classical.propDecidable _
    if h_fin : e_A.trans.Terminates then
      some ((e_A.trans.toList h_fin).foldl
        (fun m p => MatchingState.advance m p.1 p.2) m₀)
    else
      some m₀

/-- `foldl` with the "always take the second projection" function returns
the last element's `.snd`, or the initial accumulator if the list is empty. -/
private lemma foldl_snd_eq_getLast_elim
    {α β : Type*} (xs : List (α × β)) (init : β) :
    xs.foldl (fun _ p => p.2) init = xs.getLast?.elim init Prod.snd := by
  induction xs generalizing init with
  | nil => rfl
  | cons head tail ih =>
    cases tail with
    | nil => rfl
    | cons head' rest =>
      change (head' :: rest).foldl _ head.2 =
        ((head :: head' :: rest).getLast?).elim init Prod.snd
      rw [ih]
      rfl

/-- For a finite sequence `seq` (of type `Seq (Label × State)`), `endState`
of the alternating-sequence `⟨init, seq⟩` equals the `foldl` over
`seq.toList` taking the second projection. -/
private lemma endState_eq_foldl_toList
    (init : State_A) (seq : Seq (Label × State_A))
    (h_term : seq.Terminates) :
    ({ init := init, trans := seq } : AlterSeq State_A Label).endState h_term =
    (seq.toList h_term).foldl (fun _ p => p.2) init := by
  rw [foldl_snd_eq_getLast_elim, Stream'.Seq.getLast?_toList]
  -- Goal: endState = (seq.get? (length - 1)).elim init Prod.snd.
  -- Use stateAt_find_eq_endState in reverse to push endState into stateAt.
  have h_endState_some :
      ({ init := init, trans := seq } : AlterSeq State_A Label).stateAt
        (Nat.find h_term) =
      some (({ init := init, trans := seq } : AlterSeq State_A Label).endState
        h_term) :=
    AlterSeq.stateAt_find_eq_endState _ h_term
  -- Case on whether Nat.find h_term = 0.
  rcases Nat.eq_zero_or_pos (Nat.find h_term) with h_zero | h_pos
  · -- Length 0: seq.TerminatedAt 0, so seq.get? 0 = none.
    have h_term_0 : seq.TerminatedAt 0 := h_zero ▸ Nat.find_spec h_term
    have h_len_zero : Stream'.Seq.length seq h_term = 0 := h_zero
    rw [h_len_zero]
    -- Goal: endState = (seq.get? 0).elim init Prod.snd. With seq.get? 0 = none, RHS = init.
    rw [show seq.get? 0 = none from h_term_0]
    change _ = init
    -- LHS: endState = stateAt 0's content = init.
    have h_stateAt_0 :
        ({ init := init, trans := seq } : AlterSeq State_A Label).stateAt 0 =
        some init := rfl
    rw [h_zero] at h_endState_some
    rw [h_stateAt_0] at h_endState_some
    exact (Option.some.inj h_endState_some).symm
  · -- Length = n + 1 for some n ≥ 0.
    obtain ⟨n, h_n⟩ := Nat.exists_eq_succ_of_ne_zero h_pos.ne'
    have h_len_succ : Stream'.Seq.length seq h_term = n + 1 := h_n
    rw [h_len_succ]
    simp only [Nat.add_sub_cancel]
    -- Length - 1 = n. seq.get? n is some (since n < Nat.find = n+1).
    have h_not_term_n : ¬ seq.TerminatedAt n :=
      Nat.find_min h_term (by rw [h_n]; exact Nat.lt_succ_self n)
    have h_get_n : (seq.get? n).isSome :=
      Option.ne_none_iff_isSome.mp h_not_term_n
    obtain ⟨⟨l, s⟩, h_get_eq⟩ := Option.isSome_iff_exists.mp h_get_n
    rw [h_get_eq]
    change _ = s
    -- LHS: endState = stateAt (n+1)'s content = snd of seq.get? n = s.
    have h_stateAt_succ :
        ({ init := init, trans := seq } : AlterSeq State_A Label).stateAt (n + 1) =
        some s := by
      change (seq.get? n).map Prod.snd = some s
      rw [h_get_eq]; rfl
    rw [h_n] at h_endState_some
    rw [h_stateAt_succ] at h_endState_some
    exact (Option.some.inj h_endState_some).symm

/-- The state-alignment invariant: when `fromAbstractPrefix` returns
`some m` on a finite abstract prefix `e_A`, the matching state's
`current_abstract_state` equals `e_A.endState`. -/
private lemma fromAbstractPrefix_current_abstract_state
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (init_match : State_C → PMF State_A)
    (h_match_R : ∀ s_C, s_C ∈ pe_C.init.support → R s_C (init_match s_C))
    (e_A : AlterSeq State_A Label) (h_term : e_A.trans.Terminates)
    (m : MatchingState sim pe_C)
    (h : MatchingState.fromAbstractPrefix sim pe_C init_match h_match_R e_A = some m) :
    m.current_abstract_state = e_A.endState h_term := by
  classical
  unfold MatchingState.fromAbstractPrefix at h
  -- Split on `MatchingState.initial ... e_A.init` and on `h_term`.
  split at h
  · -- initial returned none, contradicting h : none = some m.
    exact absurd h (by simp)
  · rename_i m₀ h_init
    -- m₀ is the initial matching state for e_A.init.
    -- Goal: m.current_abstract_state = e_A.endState h_term.
    -- h_init is now in scope: `MatchingState.initial ... e_A.init = some m₀`.
    -- After the initial-split, the body is the `if h_fin : ...` branch.
    -- Since h_term holds, h_fin = true.
    rw [dif_pos h_term] at h
    -- h : some (foldl ... m₀) = some m.
    have h_m_eq : m = (e_A.trans.toList h_term).foldl
        (fun m p => MatchingState.advance m p.1 p.2) m₀ :=
      (Option.some.inj h).symm
    rw [h_m_eq]
    -- m₀.current_abstract_state = e_A.init via initial's structure.
    have h_m₀_cas : m₀.current_abstract_state = e_A.init := by
      -- initial returns some m₀ via `some base.setupNextTransition`,
      -- with `base.current_abstract_state = e_A.init`. Use
      -- setupNextTransition_cas to transfer this.
      unfold MatchingState.initial at h_init
      split at h_init
      · rename_i h_exists
        have h_m₀_eq : m₀ =
            ({ e_C := ⟨h_exists.choose, Seq.nil⟩,
                h_term_C := Stream'.Seq.terminates_nil,
                μ_A_current := init_match h_exists.choose,
                h_R := _,
                next_step := none,
                weak_sched := none,
                post_weak_sched := none,
                stage := WeakStage.tauInternal 0,
                current_abstract_state := e_A.init,
                hyper_witness := none } :
              MatchingState sim pe_C).setupNextTransition :=
          (Option.some.inj h_init).symm
        rw [h_m₀_eq, MatchingState.setupNextTransition_current_abstract_state]
      · exact absurd h_init (by simp)
    rw [MatchingState.foldl_advance_current_abstract_state, h_m₀_cas,
        ← endState_eq_foldl_toList]

/-- `fromAbstractPrefix` on the empty-trans prefix `⟨s_A, Seq.nil⟩` reduces
to `MatchingState.initial s_A` (the foldl is over the empty list). -/
private lemma fromAbstractPrefix_empty
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (init_match : State_C → PMF State_A)
    (h_match_R : ∀ s_C, s_C ∈ pe_C.init.support → R s_C (init_match s_C))
    (s_A : State_A) :
    MatchingState.fromAbstractPrefix sim pe_C init_match h_match_R ⟨s_A, Seq.nil⟩ =
    MatchingState.initial sim pe_C init_match h_match_R s_A := by
  unfold MatchingState.fromAbstractPrefix
  split
  · rename_i h_init
    exact h_init.symm
  · rename_i m₀ h_init
    rw [dif_pos Stream'.Seq.terminates_nil]
    rw [show (Seq.nil : Seq (Label × State_A)).toList Stream'.Seq.terminates_nil = []
      from Stream'.Seq.toList_nil]
    exact h_init.symm

/-! ### Trace-coupling helpers for `exists_coupling`

The trace-coupling proof reduces — via `traceProb_first_step` on both
sides — to equality of two tsums over `(s₀, l₀, s₁)`. This equality is
captured by `traceCoupling_tsum_eq` below; the proof itself decomposes
into:

* **Tau-collapse on the abstract side**: tau-internal labels emitted by
  `pe_A_scheduler` (via `WeakScheduler.next` during `tauInternal` /
  `preExternal` / `postExternal` stages) do not contribute to the
  observed trace — when summed out, they cancel out and leave only the
  externalEmit contributions.

* **Initial-state coupling**: `pe_A.init = pe_C.init.bind init_match`;
  every `(s_C, s_A)` with `s_A ∈ (init_match s_C).support` is `R`-coupled
  via `h_match_R`.

* **First-step PMFRel coupling**: at each `R`-coupled `(s_C, μ_A)`,
  `sim.stepWitness_pmfRel` couples `pe_C.kernel ⟨s_C, _⟩` with an
  abstract-side distribution; this distribution corresponds, after
  marginalisation through the weak-transition stages, to the *external
  label's* emission from `pe_A`.

* **Continuation coupling**: for each step outcome `(s_C', μ_A_next)`
  with the preserved `R s_C' μ_A_next`, the continuations of both
  executions are again trace-coupled — handled by induction on `τ` via
  this same theorem (the recursive structure is implicit in the τ
  parameter, since `traceProb` on `continuationFrom` over a shorter
  trace appears in the tsum).

This is the *core* of Segala's theorem; the proof is non-trivial and
deferred. Once the helpers (currently inlined as sorries) are filled,
this theorem closes via term-by-term tsum manipulation. -/

/-- **First-step recognition**: the kernel-times-continuation sum from
state `s` matches the `traceProb` of the continuation-pe starting from
`⟨s, Seq.nil⟩`. This is just `traceProb_first_step` applied to
`pe.continuationFrom ⟨s, Seq.nil⟩` (whose init is `PMF.pure s`), with
the s₀-sum collapsed. -/
private lemma kernel_contA_eq_traceProb_from_state
    {State Label : Type}
    (sys : LabelledSystem State Label)
    (pe : ProbabilisticExecution sys.toSystem)
    (s : State) (l : Label) (τ : Seq Label) :
    (∑' (l₀ : Label) (s₁ : State), pe.kernel ⟨s, Seq.nil⟩ (l₀, s₁) *
        (sys.consumeLabel l₀ (Seq.cons l τ)).elim 0
          (fun τ' => sys.traceProb
            (pe.continuationFrom ⟨s, Seq.cons (l₀, s₁) Seq.nil⟩
              ⟨1, by
                change (Seq.cons (l₀, s₁) Seq.nil).get? 1 = none
                rw [Stream'.Seq.get?_cons_succ]
                exact Stream'.Seq.terminatedAt_nil⟩) τ')) =
    sys.traceProb (pe.continuationFrom ⟨s, Seq.nil⟩
      Stream'.Seq.terminates_nil) (Seq.cons l τ) := by
  classical
  -- Apply `traceProb_first_step` to RHS.
  rw [sys.traceProb_first_step (pe.continuationFrom ⟨s, Seq.nil⟩
        Stream'.Seq.terminates_nil) l τ]
  -- The s₀-summation collapses since the init is PMF.pure s.
  have h_init_zero : ∀ s₀, s₀ ≠ s →
      (pe.continuationFrom ⟨s, Seq.nil⟩ Stream'.Seq.terminates_nil).init s₀ = 0 := by
    intro s₀ h_ne
    change (PMF.pure (({init := s, trans := Seq.nil} :
        AlterSeq State Label).endState Stream'.Seq.terminates_nil)) s₀ = 0
    -- endState ⟨s, nil⟩ = s.
    have h_eq := AlterSeq.stateAt_find_eq_endState
      ({init := s, trans := Seq.nil} : AlterSeq State Label)
      Stream'.Seq.terminates_nil
    have h_find : Nat.find (Stream'.Seq.terminates_nil :
        (Seq.nil : Seq (Label × State)).Terminates) = 0 := by
      apply Nat.find_eq_zero _ |>.mpr; rfl
    rw [h_find] at h_eq
    have h_endState : ({init := s, trans := Seq.nil} :
        AlterSeq State Label).endState Stream'.Seq.terminates_nil = s :=
      (Option.some.inj h_eq).symm
    rw [h_endState]
    exact PMF.pure_apply_of_ne s s₀ h_ne
  -- Collapse outer s₀-sum: tsum_eq_single at s₀ = s.
  rw [tsum_eq_single s (fun s₀ h_ne => by
    simp [h_init_zero s₀ h_ne])]
  -- Compute pe_from_s.init s = 1 (PMF.pure at the support point).
  have h_endState_eq :
      ({init := s, trans := Seq.nil} : AlterSeq State Label).endState
        Stream'.Seq.terminates_nil = s := by
    have h_eq := AlterSeq.stateAt_find_eq_endState
      ({init := s, trans := Seq.nil} : AlterSeq State Label)
      Stream'.Seq.terminates_nil
    have h_find : Nat.find (Stream'.Seq.terminates_nil :
        (Seq.nil : Seq (Label × State)).Terminates) = 0 := by
      apply Nat.find_eq_zero _ |>.mpr; rfl
    rw [h_find] at h_eq
    exact (Option.some.inj h_eq).symm
  have h_init_one :
      (pe.continuationFrom ⟨s, Seq.nil⟩ Stream'.Seq.terminates_nil).init s = 1 := by
    change (PMF.pure (({init := s, trans := Seq.nil} :
        AlterSeq State Label).endState Stream'.Seq.terminates_nil)) s = 1
    rw [h_endState_eq, PMF.pure_apply, if_pos rfl]
  rw [h_init_one]
  simp_rw [one_mul]
  -- Bridge: `(pe.continuationFrom ⟨s, Seq.nil⟩).continuationFrom ⟨s, history⟩
  -- = pe.continuationFrom ⟨s, history⟩` as ProbabilisticExecutions.
  -- Bridge: `(pe.continuationFrom ⟨s, Seq.nil⟩).continuationFrom ⟨s, history⟩
  -- = pe.continuationFrom ⟨s, history⟩` as ProbabilisticExecutions.
  have h_cont_cont : ∀ (history : Seq (Label × State)) (h_term : history.Terminates),
      (pe.continuationFrom ⟨s, Seq.nil⟩ Stream'.Seq.terminates_nil).continuationFrom
          ⟨s, history⟩ h_term =
      pe.continuationFrom ⟨s, history⟩ h_term := by
    intro history h_term
    -- Both have init = PMF.pure (⟨s, history⟩.endState h_term).
    -- Schedulers' `next` agree pointwise (via `Seq.nil.append = id`).
    -- `valid` are propositions, equal by proof irrelevance.
    -- Use mk-equality to break into fields.
    change ProbabilisticExecution.mk _ _ = ProbabilisticExecution.mk _ _
    congr 1
    show Scheduler.mk _ _ = Scheduler.mk _ _
    congr 1
    · funext e'
      classical
      change (if e'.init = (⟨s, history⟩ : AlterSeq State Label).endState h_term then
          (pe.continuationFrom ⟨s, Seq.nil⟩ Stream'.Seq.terminates_nil).scheduler.next
            ⟨s, history.append e'.trans⟩
          else none) =
        if e'.init = (⟨s, history⟩ : AlterSeq State Label).endState h_term then
          pe.scheduler.next ⟨s, history.append e'.trans⟩
          else none
      by_cases h_init : e'.init = (⟨s, history⟩ : AlterSeq State Label).endState h_term
      · rw [if_pos h_init, if_pos h_init]
        change (if (⟨s, history.append e'.trans⟩ : AlterSeq State Label).init =
            (⟨s, Seq.nil⟩ : AlterSeq State Label).endState
              Stream'.Seq.terminates_nil then
            pe.scheduler.next ⟨s, Seq.nil.append (history.append e'.trans)⟩
            else none) =
          pe.scheduler.next ⟨s, history.append e'.trans⟩
        rw [if_pos h_endState_eq.symm]
        congr 1
        show (⟨s, Seq.nil.append (history.append e'.trans)⟩ : AlterSeq State Label) =
          ⟨s, history.append e'.trans⟩
        rw [Stream'.Seq.nil_append]
      · rw [if_neg h_init, if_neg h_init]
  -- Apply h_cont_cont in the RHS continuation.
  simp_rw [h_cont_cont]
  -- Also need to bridge the kernel.
  have h_kernel_eq : ∀ (l₀ : Label) (s₁ : State),
      (pe.continuationFrom ⟨s, Seq.nil⟩ Stream'.Seq.terminates_nil).kernel
        ⟨s, Seq.nil⟩ (l₀, s₁) = pe.kernel ⟨s, Seq.nil⟩ (l₀, s₁) := by
    intro l₀ s₁
    have h := pe.kernel_continuationFrom ⟨s, Seq.nil⟩ Stream'.Seq.terminates_nil
      Seq.nil (l₀, s₁)
    rw [h_endState_eq] at h
    rw [h, Stream'.Seq.nil_append]
  simp_rw [h_kernel_eq]

/-- **Weighted trace probability**: the average of `traceProb` from each
state `s`, weighted by `μ s`. When `μ = PMF.pure s_0`, this collapses to
`traceProb` from `s_0`. -/
noncomputable def weighted_traceProb
    {State Label : Type}
    (sys : LabelledSystem State Label)
    (pe : ProbabilisticExecution sys.toSystem)
    (μ : PMF State) (τ : Seq Label) : ENNReal :=
  ∑' s, μ s * sys.traceProb
    (pe.continuationFrom ⟨s, Seq.nil⟩ Stream'.Seq.terminates_nil) τ

/-- When the weight is `PMF.pure s_0`, the weighted trace prob collapses
to the trace prob starting from `s_0`. -/
private lemma weighted_traceProb_pure
    {State Label : Type}
    (sys : LabelledSystem State Label)
    (pe : ProbabilisticExecution sys.toSystem) (s_0 : State) (τ : Seq Label) :
    weighted_traceProb sys pe (PMF.pure s_0) τ =
    sys.traceProb (pe.continuationFrom ⟨s_0, Seq.nil⟩
      Stream'.Seq.terminates_nil) τ := by
  unfold weighted_traceProb
  classical
  rw [tsum_eq_single s_0]
  · rw [PMF.pure_apply, if_pos rfl, one_mul]
  · intro s h_ne
    rw [PMF.pure_apply_of_ne s_0 s h_ne, zero_mul]

/-- The **PMFRel-style coupling** stating Segala's theorem in its full
generality: given two distributions `μ_C` (concrete) and `μ_A` (abstract)
related by a per-state R-coupling via `f`, the weighted trace
probabilities match. The original `per_state_trace_coupling` is the
special case `μ_C = PMF.pure s_C, f = init_match`. -/
private theorem weighted_trace_coupling
    {sys_C : LabelledSystem State_C Label} {sys_A : LabelledSystem State_A Label}
    {R : State_C → PMF State_A → Prop}
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (init_match : State_C → PMF State_A)
    (h_match_R : ∀ s_C, s_C ∈ pe_C.init.support → R s_C (init_match s_C))
    (pe_A : ProbabilisticExecution sys_A.toSystem)
    (_h_sched_eq : pe_A.scheduler.next = fun e_A =>
      (MatchingState.fromAbstractPrefix sim pe_C init_match h_match_R e_A).bind
        MatchingState.computeNext)
    (μ_C : PMF State_C) (f : State_C → PMF State_A)
    (_h_coupled : ∀ s_C, s_C ∈ μ_C.support → R s_C (f s_C))
    (τ : Seq Label) :
    weighted_traceProb sys_C pe_C μ_C τ =
    weighted_traceProb sys_A pe_A (μ_C.bind f) τ := by
  -- Case on τ. Nil case: both sides equal 1 (PMF mass).
  cases τ with
  | nil =>
    unfold weighted_traceProb
    -- LHS: ∑' s, μ_C s * traceProb pe_C_from_s nil = ∑' s, μ_C s * 1 = 1.
    -- RHS: ∑' s_A, (μ_C.bind f) s_A * traceProb pe_A_from_sA nil = 1.
    have h_lhs : (∑' (s : State_C), μ_C s * sys_C.traceProb
        (pe_C.continuationFrom ⟨s, Seq.nil⟩ Stream'.Seq.terminates_nil)
          Seq.nil) = 1 := by
      simp_rw [sys_C.traceProb_nil_eq_one, mul_one]
      exact PMF.tsum_coe μ_C
    have h_rhs : (∑' (s_A : State_A), (μ_C.bind f) s_A * sys_A.traceProb
        (pe_A.continuationFrom ⟨s_A, Seq.nil⟩ Stream'.Seq.terminates_nil)
          Seq.nil) = 1 := by
      simp_rw [sys_A.traceProb_nil_eq_one, mul_one]
      exact PMF.tsum_coe (μ_C.bind f)
    rw [h_lhs, h_rhs]
  | cons l₀ τ' =>
    -- Inductive case: apply `kernel_contA_eq_traceProb_from_state` to expose
    -- the kernel-level structure on both sides.
    unfold weighted_traceProb
    -- LHS = ∑' s_C, μ_C s_C * traceProb (pe_C_from_sC) (l₀ :: τ')
    --     = ∑' s_C, μ_C s_C * (∑' l_first s_first, pe_C.kernel ⟨s_C, _⟩ * cont_C)
    simp_rw [← kernel_contA_eq_traceProb_from_state sys_C pe_C _ l₀ τ',
             ← kernel_contA_eq_traceProb_from_state sys_A pe_A _ l₀ τ']
    -- The remaining goal is the per-step coupling:
    --   ∑' s_C, μ_C s_C * (∑' l_first s_first, pe_C.kernel * cont_C s_C l_first s_first) =
    --   ∑' s_A, (μ_C.bind f) s_A * (∑' l_first s_first, pe_A.kernel * cont_A s_A l_first s_first)
    -- Closing this requires:
    --   1. Unfolding `(μ_C.bind f) s_A = ∑' s_C, μ_C s_C * f s_C s_A` and
    --      reorganizing tsums to reduce to a per-s_C inner equality.
    --   2. At each s_C ∈ μ_C.support (where R s_C (f s_C) holds via h_coupled),
    --      use `sim.stepWitness_pmfRel` to obtain a PMFRel-coupling between
    --      `pe_C.kernel ⟨s_C, _⟩` (a PMF over `(l_C, s_C')`) and an abstract
    --      witness PMF `ω` (a PMF over abstract distributions).
    --   3. The continuation factor `cont_C s_C l_first s_first` (= traceProb on
    --      continuation pe) recursively matches `cont_A` via another
    --      `weighted_trace_coupling` invocation with:
    --        - new μ_C' = pe_C.kernel emission distribution
    --        - new f' = derived from the matching state's `h_R_next` chain
    --        - smaller τ (for external matching) or unchanged (for internal —
    --          well-founded by σ.runtime).
    --
    -- **DEFERRED**: this is the mathematical heart of Segala's theorem, requiring
    -- well-founded recursion on a custom measure (external trace length +
    -- bounded tau-padding count from σ.runtime).
    sorry
private theorem per_state_trace_coupling
    {sys_C : LabelledSystem State_C Label} {sys_A : LabelledSystem State_A Label}
    {R : State_C → PMF State_A → Prop}
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (init_match : State_C → PMF State_A)
    (h_match_R : ∀ s_C, s_C ∈ pe_C.init.support → R s_C (init_match s_C))
    (pe_A : ProbabilisticExecution sys_A.toSystem)
    (s_C : State_C) (h_s_C_supp : s_C ∈ pe_C.init.support) (τ : Seq Label)
    (_h_sched_eq : pe_A.scheduler.next = fun e_A =>
      (MatchingState.fromAbstractPrefix sim pe_C init_match h_match_R e_A).bind
        MatchingState.computeNext) :
    sys_C.traceProb (pe_C.continuationFrom ⟨s_C, Seq.nil⟩
      Stream'.Seq.terminates_nil) τ =
    ∑' (s_A : State_A), init_match s_C s_A *
      sys_A.traceProb (pe_A.continuationFrom ⟨s_A, Seq.nil⟩
        Stream'.Seq.terminates_nil) τ := by
  -- Dispatch to the more general `weighted_trace_coupling`, with
  -- `μ_C := PMF.pure s_C, f := init_match`. The LHS collapses via
  -- `weighted_traceProb_pure`; the RHS unfolds the `bind`.
  have h_general := weighted_trace_coupling sim pe_C init_match h_match_R pe_A
    _h_sched_eq (PMF.pure s_C) init_match (fun s_C' h_s_C' => by
      rw [PMF.mem_support_pure_iff] at h_s_C'
      rw [h_s_C']
      exact h_match_R s_C h_s_C_supp) τ
  rw [weighted_traceProb_pure] at h_general
  rw [h_general]
  unfold weighted_traceProb
  refine tsum_congr (fun s_A => ?_)
  rw [PMF.bind_apply]
  -- (PMF.pure s_C).bind init_match s_A = ∑' s_C', (PMF.pure s_C) s_C' * init_match s_C' s_A
  --                                     = init_match s_C s_A.
  classical
  rw [show (∑' (a : State_C), (PMF.pure s_C) a * (init_match a) s_A) =
        init_match s_C s_A from by
    rw [tsum_eq_single s_C]
    · rw [PMF.pure_apply, if_pos rfl, one_mul]
    · intro s_C' h_ne
      rw [PMF.pure_apply_of_ne s_C s_C' h_ne, zero_mul]]

theorem traceCoupling_tsum_eq
    (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (pe_C : ProbabilisticExecution sys_C.toSystem)
    (init_match : State_C → PMF State_A)
    (h_match_R : ∀ s_C, s_C ∈ pe_C.init.support → R s_C (init_match s_C))
    (pe_A : ProbabilisticExecution sys_A.toSystem)
    (l : Label) (τ : Seq Label)
    (h_init_eq : pe_A.init = pe_C.init.bind init_match)
    (h_sched_eq : pe_A.scheduler.next = fun e_A =>
      (MatchingState.fromAbstractPrefix sim pe_C init_match h_match_R e_A).bind
        MatchingState.computeNext) :
    (∑' (s₀ : State_C) (l₀ : Label) (s₁ : State_C),
        pe_C.init s₀ * pe_C.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
        (sys_C.consumeLabel l₀ (Seq.cons l τ)).elim 0
          (fun τ' => sys_C.traceProb
            (pe_C.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
              ⟨1, by
                change (Seq.cons (l₀, s₁) Seq.nil).get? 1 = none
                rw [Stream'.Seq.get?_cons_succ]
                exact Stream'.Seq.terminatedAt_nil⟩) τ')) =
    ∑' (s₀ : State_A) (l₀ : Label) (s₁ : State_A),
        pe_A.init s₀ * pe_A.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
        (sys_A.consumeLabel l₀ (Seq.cons l τ)).elim 0
          (fun τ' => sys_A.traceProb
            (pe_A.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
              ⟨1, by
                change (Seq.cons (l₀, s₁) Seq.nil).get? 1 = none
                rw [Stream'.Seq.get?_cons_succ]
                exact Stream'.Seq.terminatedAt_nil⟩) τ') := by
  -- Continuation traceProb abbreviations to keep the expressions short.
  let contC : State_C → Label → State_C → ENNReal := fun s₀ l₀ s₁ =>
    (sys_C.consumeLabel l₀ (Seq.cons l τ)).elim 0
      (fun τ' => sys_C.traceProb
        (pe_C.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
          ⟨1, by
            change (Seq.cons (l₀, s₁) Seq.nil).get? 1 = none
            rw [Stream'.Seq.get?_cons_succ]
            exact Stream'.Seq.terminatedAt_nil⟩) τ')
  let contA : State_A → Label → State_A → ENNReal := fun s₀ l₀ s₁ =>
    (sys_A.consumeLabel l₀ (Seq.cons l τ)).elim 0
      (fun τ' => sys_A.traceProb
        (pe_A.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
          ⟨1, by
            change (Seq.cons (l₀, s₁) Seq.nil).get? 1 = none
            rw [Stream'.Seq.get?_cons_succ]
            exact Stream'.Seq.terminatedAt_nil⟩) τ')
  change (∑' (s_C : State_C) (l_C : Label) (s_C' : State_C),
      pe_C.init s_C * pe_C.kernel ⟨s_C, Seq.nil⟩ (l_C, s_C') *
      contC s_C l_C s_C') =
    ∑' (s_A : State_A) (l_A : Label) (s_A' : State_A),
      pe_A.init s_A * pe_A.kernel ⟨s_A, Seq.nil⟩ (l_A, s_A') *
      contA s_A l_A s_A'
  -- ============================================================
  -- STAGE 1: rewrite pe_A.init via h_init_eq + PMF.bind_apply and
  --          reorganize the abstract tsum to start with ∑' s_C.
  -- ============================================================
  -- LHS: pull pe_C.init s_C out of inner sums.
  -- ∑' s_C l_C s_C', pe_C.init s_C * pe_C.kernel ... * contC
  --  = ∑' s_C, pe_C.init s_C * (∑' l_C s_C', pe_C.kernel ... * contC).
  simp_rw [mul_assoc (pe_C.init _), ENNReal.tsum_mul_left]
  -- RHS: rewrite pe_A.init s_A = ∑' s_C, pe_C.init s_C * init_match s_C s_A,
  -- distribute, and reorder.
  have h_pe_A_init : ∀ s_A, pe_A.init s_A =
      ∑' s_C, pe_C.init s_C * init_match s_C s_A := by
    intro s_A; rw [h_init_eq, PMF.bind_apply]
  simp_rw [h_pe_A_init]
  -- After simp_rw, RHS has: ∑' s_A l_A s_A', (∑' s_C, ...) * pe_A.kernel ... * contA.
  -- Distribute the inner ∑' s_C via tsum_mul_right (twice for two outer *'s).
  conv_rhs =>
    enter [1, s_A, 1, l_A, 1, s_A']
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
  -- Goal RHS = ∑' s_A l_A s_A' s_C, pe_C.init s_C * init_match s_C s_A *
  --   pe_A.kernel ⟨s_A, _⟩ (l_A, s_A') * contA s_A l_A s_A'.
  -- Reorganize: convert the four-nested tsum to ∑' s_C s_A l_A s_A'.
  -- Three tsum_comm swaps move s_C from innermost to outermost.
  conv_rhs =>
    enter [1, s_A, 1, l_A]
    rw [ENNReal.tsum_comm]
  conv_rhs =>
    enter [1, s_A]
    rw [ENNReal.tsum_comm]
  rw [ENNReal.tsum_comm]
  -- Factor pe_C.init s_C out of the inner sum.
  conv_rhs =>
    enter [1, s_C]
    rw [show (∑' (s_A : State_A) (l_A : Label) (s_A' : State_A),
            pe_C.init s_C * init_match s_C s_A *
            pe_A.kernel ⟨s_A, Seq.nil⟩ (l_A, s_A') * contA s_A l_A s_A') =
          pe_C.init s_C * ∑' (s_A : State_A) (l_A : Label) (s_A' : State_A),
            init_match s_C s_A * pe_A.kernel ⟨s_A, Seq.nil⟩ (l_A, s_A') *
            contA s_A l_A s_A' from by
      simp_rw [mul_assoc (pe_C.init s_C), ENNReal.tsum_mul_left]]
  -- Both sides are now ∑' s_C, pe_C.init s_C * (inner). Reduce to per-s_C.
  refine tsum_congr (fun s_C => ?_)
  -- Case-split on whether s_C ∈ pe_C.init.support. For s_C out of support,
  -- pe_C.init s_C = 0 collapses both sides to 0. In-support uses
  -- `per_state_trace_coupling` which requires the support hypothesis.
  classical
  by_cases h_s_C_supp : s_C ∈ pe_C.init.support
  swap
  · have h_zero : pe_C.init s_C = 0 := by
      rwa [PMF.mem_support_iff, not_not] at h_s_C_supp
    rw [h_zero]
    ring
  congr 1
  -- ============================================================
  -- STAGE 3: recognize each side as `traceProb pe_from_state (l :: τ)`
  -- via `traceProb_first_step` in reverse.
  -- ============================================================
  -- LHS: ∑' l_C s_C', pe_C.kernel ⟨s_C, _⟩ (l_C, s_C') * contC ...
  --      = traceProb sys_C (pe_C.continuationFrom ⟨s_C, Seq.nil⟩) (l :: τ).
  -- RHS: ∑' s_A l_A s_A', init_match s_C s_A * pe_A.kernel ⟨s_A, _⟩ * contA ...
  --      = ∑' s_A, init_match s_C s_A *
  --          traceProb sys_A (pe_A.continuationFrom ⟨s_A, Seq.nil⟩) (l :: τ).
  rw [kernel_contA_eq_traceProb_from_state sys_C pe_C s_C l τ]
  -- Factor `init_match s_C s_A` out of the inner sum, then apply Stage 3
  -- recognition on the abstract side.
  rw [show (∑' (s_A : State_A) (l_A : Label) (s_A' : State_A),
          init_match s_C s_A * pe_A.kernel ⟨s_A, Seq.nil⟩ (l_A, s_A') *
          contA s_A l_A s_A') =
        ∑' (s_A : State_A), init_match s_C s_A *
          sys_A.traceProb (pe_A.continuationFrom ⟨s_A, Seq.nil⟩
              Stream'.Seq.terminates_nil) (Seq.cons l τ) from by
    refine tsum_congr (fun s_A => ?_)
    rw [← kernel_contA_eq_traceProb_from_state sys_A pe_A s_A l τ]
    simp_rw [mul_assoc (init_match s_C s_A), ENNReal.tsum_mul_left]
    rfl]
  -- ============================================================
  -- STAGES 4-7: dispatch to the per-state coupling lemma.
  exact per_state_trace_coupling sim pe_C init_match h_match_R pe_A s_C
    h_s_C_supp (Seq.cons l τ) h_sched_eq

end ProbabilisticForwardSimulation

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
  -- STEP 3: construct `σ_A` such that the resulting probabilistic execution
  -- is trace-coupled to `pe_C`. Decomposed into three sub-pieces.
  classical
  -- STEP 3 (combined): produce an abstract scheduler making `pe_A` trace-
  -- coupled to `pe_C` on every *non-empty* trace. The nil case is handled
  -- separately below (via `traceProb_nil_eq_one`, independent of the
  -- scheduler), so this existence statement only needs the cons case.
  --
  -- Why couple validity with trace-matching in one statement: a trivial
  -- `compute_next := fun _ => none` satisfies `Scheduler.valid` vacuously,
  -- but makes every non-nil `traceProb` zero on the abstract side, breaking
  -- cons-matching whenever `pe_C` has positive mass on `cons l τ`. So the
  -- two conditions must be discharged together with one scheduler choice.
  --
  -- Sketch: for each abstract prefix `e_A`, use `Classical.choose` to pick a
  -- "matching" concrete prefix `e_C` (matched at each transition via the
  -- weak-transition stages of `sim.step`). Then return the abstract single
  -- step that corresponds to the current stage of the weak transition
  -- emulating `pe_C.scheduler.next e_C`. Validity follows from `sim.step`'s
  -- conclusions on `sys_A.step`; trace matching follows from how
  -- `weakTau`/`weakStep` decompose along the external trace.
  -- Approach to building pe_A_scheduler:
  --
  -- The scheduler must, for each abstract prefix `e_A`, emit a next-step
  -- distribution that emulates what `pe_C` would do at a "matching" concrete
  -- prefix. The matching is via `sim`'s `stepWitness` machinery:
  --   * `sim.init` matches each concrete initial state `s_C` with a
  --     distribution `μ_A = init_match s_C` related via `R`.
  --   * Given a concrete prefix `e_C` related to `μ_A`, `sim.step` lifts
  --     `pe_C.scheduler.next e_C` to a weak abstract transition (`weakTau`
  --     when the concrete label is internal, `weakStep` when external).
  --   * A weak transition unrolls into a sequence of single abstract steps;
  --     the scheduler plays them one at a time, tracking position in `e_A`.
  --
  -- Classical.choose picks a matching `e_C` for each `e_A`. The bookkeeping
  -- for "which stage of which weak transition" is encoded by the `e_A`
  -- length (number of abstract transitions taken). This requires a
  -- recursive definition of the matching across all prefix lengths.
  --
  -- Trace-coupling proof: by induction on the trace shape, using
  -- `traceProb_first_step` on both sides. Each step reduces to a per-`(s₀,
  -- l₀, s₁)` matching that follows from `stepWitness_pmfRel`.
  --
  -- This is genuinely the deep content of Segala's theorem; left as the
  -- main outstanding sorry. Resolved in stages over multiple sessions.
  have h_build_pe_A :
      ∃ pe_A_scheduler : Scheduler sys_A.toSystem,
        ∀ l τ, sys_C.traceProb pe_C (Seq.cons l τ) =
          sys_A.traceProb ⟨pe_A_init, pe_A_scheduler⟩ (Seq.cons l τ) := by
    -- Build pe_A_scheduler from MatchingState machinery.
    let pe_A_scheduler : Scheduler sys_A.toSystem :=
      { next := fun e_A =>
          (MatchingState.fromAbstractPrefix sim pe_C init_match h_match_R e_A).bind
            MatchingState.computeNext
        valid := by
          classical
          intro e_A n s_A h_term_e h_state_e d h_some l_A μ_A h_supp
          rcases h_from :
              MatchingState.fromAbstractPrefix sim pe_C init_match h_match_R e_A
            with _ | m
          · simp [h_from] at h_some
          · simp only [h_from, Option.bind_some] at h_some
            rcases h_compute : MatchingState.computeNext m with _ | d'
            · rw [h_compute] at h_some; exact absurd h_some (by simp)
            · rw [h_compute] at h_some
              have h_d_eq : d = d' := (Option.some.inj h_some).symm
              subst h_d_eq
              -- **State-alignment invariant**: `s_A = m.current_abstract_state`.
              -- Decomposed into two equalities:
              -- (i) `s_A = e_A.endState` — from `h_state_e` + `h_term_e`.
              -- (ii) `e_A.endState = m.current_abstract_state` — from
              --      `fromAbstractPrefix`'s `advance`-fold which preserves
              --      this invariant inductively.
              have h_term_C : e_A.trans.Terminates := ⟨n, h_term_e⟩
              have h_state_align : s_A = m.current_abstract_state := by
                -- (i) s_A = e_A.endState h_term_C.
                have h_s_eq_endState : s_A = e_A.endState h_term_C := by
                  -- Show n = Nat.find h_term_C, then use stateAt_find_eq_endState.
                  have h_n_le : Nat.find h_term_C ≤ n := Nat.find_le h_term_e
                  have h_n_ge : n ≤ Nat.find h_term_C := by
                    by_contra h_not_le
                    have h_gt : Nat.find h_term_C < n := Nat.not_le.mp h_not_le
                    cases n with
                    | zero => exact absurd h_gt (Nat.not_lt_zero _)
                    | succ n' =>
                      have h_n'_ge : n' ≥ Nat.find h_term_C := Nat.lt_succ_iff.mp h_gt
                      have h_get_none : e_A.trans.get? n' = none :=
                        Stream'.Seq.terminated_stable e_A.trans h_n'_ge
                          (Nat.find_spec h_term_C)
                      have h_stateAt_def :
                          e_A.stateAt (n' + 1) = (e_A.trans.get? n').map Prod.snd := rfl
                      rw [h_get_none] at h_stateAt_def
                      rw [h_stateAt_def] at h_state_e
                      simp at h_state_e
                  have h_n_eq : n = Nat.find h_term_C := le_antisymm h_n_ge h_n_le
                  have h_eq := AlterSeq.stateAt_find_eq_endState e_A h_term_C
                  rw [← h_n_eq] at h_eq
                  rw [h_eq] at h_state_e
                  exact (Option.some.inj h_state_e).symm
                -- (ii) e_A.endState h_term_C = m.current_abstract_state.
                have h_endState_eq : e_A.endState h_term_C = m.current_abstract_state :=
                  (ProbabilisticForwardSimulation.fromAbstractPrefix_current_abstract_state
                    sim pe_C init_match h_match_R e_A h_term_C m h_from).symm
                rw [h_s_eq_endState, h_endState_eq]
              rw [h_state_align]
              -- Goal: sys_A.toSystem.step m.current_abstract_state l_A μ_A.
              -- Case-split on `computeNext`'s structure to identify
              -- which branch fired. Vacuous branches discharge via
              -- contradiction with `h_compute`; productive branches
              -- still need work (see sub-sorries).
              rcases h_ws : m.weak_sched with _ | σ
              · -- weak_sched = none: `computeNext m = none` in both
                -- pe_C.next sub-cases, contradicting `h_compute`.
                exfalso
                have h_cn_none : MatchingState.computeNext m = none := by
                  unfold MatchingState.computeNext
                  rw [h_ws]
                  rcases pe_C.scheduler.next m.e_C with _ | _ <;> rfl
                rw [h_cn_none] at h_compute
                exact absurd h_compute (by simp)
              · -- weak_sched = some σ. Case on stage.
                -- Shared mid-tau validity: when stage ≠ externalEmit,
                -- `computeNext m = liftOption (σ.next ⟨m.cas, Seq.nil⟩)`.
                -- `σ.valid` at this prefix (TerminatedAt 0, stateAt 0 = m.cas)
                -- gives `sys_A.step m.cas (l, μ)` for any `some (l, μ)` in
                -- the support; combined with `liftOption_eq_some_iff`, this
                -- closes validity.
                have h_mid_tau : ∀ (h_st_eq : MatchingState.computeNext m =
                    MatchingState.liftOption
                      (σ.next ⟨m.current_abstract_state, Seq.nil⟩)),
                    sys_A.toSystem.step m.current_abstract_state l_A μ_A := by
                  intro h_st_eq
                  rw [h_st_eq] at h_compute
                  rw [MatchingState.liftOption_eq_some_iff] at h_compute
                  obtain ⟨h_exists, h_d'_eq⟩ := h_compute
                  subst h_d'_eq
                  rw [PMF.mem_support_iff] at h_supp
                  simp only [PMF.pure_apply] at h_supp
                  have h_pair_eq : (l_A, μ_A) = h_exists.choose := by
                    by_contra h_ne
                    rw [if_neg h_ne] at h_supp
                    exact absurd h_supp (by norm_num)
                  have h_choose_supp := h_exists.choose_spec
                  have h_term : (Seq.nil : Seq (Label × State_A)).TerminatedAt 0 := rfl
                  have h_state :
                      (⟨m.current_abstract_state, Seq.nil⟩ : AlterSeq State_A Label).stateAt 0
                        = some m.current_abstract_state := rfl
                  have h_valid := σ.valid ⟨m.current_abstract_state, Seq.nil⟩ 0
                    m.current_abstract_state h_term h_state _ h_choose_supp
                  rw [← h_pair_eq] at h_valid
                  exact h_valid
                rcases h_st : m.stage with k | k | _ | k
                · -- tauInternal k
                  exact h_mid_tau (by unfold MatchingState.computeNext; rw [h_ws, h_st])
                · -- preExternal k
                  exact h_mid_tau (by unfold MatchingState.computeNext; rw [h_ws, h_st])
                · -- externalEmit case.
                  rcases h_hw : m.hyper_witness with _ | w
                  · -- hyper_witness = none: computeNext m = none, contradicts h_compute.
                    exfalso
                    have h_cn_none : MatchingState.computeNext m = none := by
                      unfold MatchingState.computeNext
                      rw [h_ws, h_st, h_hw]
                    rw [h_cn_none] at h_compute
                    exact absurd h_compute (by simp)
                  · -- hyper_witness = some w. Emission is guarded on
                    -- `m.cas ∈ w.μ_pre.support`; on that branch, emission is
                    -- `(w.kernel m.cas).map (Prod.mk w.l)` and validity follows
                    -- from `w.valid m.cas h_cas_in`.
                    classical
                    by_cases h_cas_in : m.current_abstract_state ∈ w.μ_pre.support
                    · have h_cn_eq : MatchingState.computeNext m =
                          some ((w.kernel m.current_abstract_state).map (Prod.mk w.l)) := by
                        unfold MatchingState.computeNext
                        rw [h_ws, h_st, h_hw]
                        simp [h_cas_in]
                      rw [h_cn_eq] at h_compute
                      have h_d_eq : d = (w.kernel m.current_abstract_state).map (Prod.mk w.l) :=
                        (Option.some.inj h_compute).symm
                      rw [h_d_eq, PMF.support_map, Set.mem_image] at h_supp
                      obtain ⟨μ, h_μ_supp, h_eq⟩ := h_supp
                      have h_l_eq : l_A = w.l := (Prod.mk.inj h_eq).1.symm
                      have h_μ_eq : μ_A = μ := (Prod.mk.inj h_eq).2.symm
                      have h_step :=
                        w.valid m.current_abstract_state h_cas_in μ h_μ_supp
                      rw [h_l_eq, h_μ_eq]
                      exact h_step
                    · exfalso
                      have h_cn_none : MatchingState.computeNext m = none := by
                        unfold MatchingState.computeNext
                        rw [h_ws, h_st, h_hw]
                        simp [h_cas_in]
                      rw [h_cn_none] at h_compute
                      exact absurd h_compute (by simp)
                · -- postExternal k
                  exact h_mid_tau (by unfold MatchingState.computeNext; rw [h_ws, h_st]) }
    refine ⟨pe_A_scheduler, ?_⟩
    intro l τ
    -- ============================================================
    -- TRACE-COUPLING PROOF (cons case)
    -- ============================================================
    -- Step A: Apply `traceProb_first_step` on both sides, reducing the
    -- goal to equality of tsums over `(s₀, l₀, s₁)`. The tsum equality
    -- is the heart of the coupling; it's decomposed into helper lemmas
    -- listed in `traceCoupling_*_aux` below. Currently sorried as a
    -- single block; each `aux` lemma is its own scoped sorry.
    rw [sys_C.traceProb_first_step pe_C l τ,
        sys_A.traceProb_first_step ⟨pe_A_init, pe_A_scheduler⟩ l τ]
    exact ProbabilisticForwardSimulation.traceCoupling_tsum_eq
      sim pe_C init_match h_match_R ⟨pe_A_init, pe_A_scheduler⟩ l τ rfl rfl
  obtain ⟨pe_A_scheduler, h_cons⟩ := h_build_pe_A
  -- Combine the nil case (from `traceProb_nil_eq_one`) and the cons case
  -- (from `h_build_pe_A`) into full `TraceCoupled` via `of_nil_and_cons`.
  have h_traces : TraceCoupled sys_C sys_A pe_C
      ⟨pe_A_init, pe_A_scheduler⟩ := by
    apply TraceCoupled.of_nil_and_cons
    · rw [sys_C.traceProb_nil_eq_one pe_C,
          sys_A.traceProb_nil_eq_one ⟨pe_A_init, pe_A_scheduler⟩]
    · exact h_cons
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
