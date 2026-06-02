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
  -- Step 4c: collapse iterated outer sums + inner into TraceDecomp's Σ'.
  -- Via `psigmaEquivSigma` × 3 + `tsum_sigma'` × 3 on the LHS to expose
  -- nested `∑' s₀ ∑' l₀ ∑' s₁ ∑' e_rest`, matching the rewritten RHS;
  -- then bridge `⟨s₁, e.trans⟩ = e` via `init = endState = s₁` and
  -- match summand-wise.
  sorry

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
  have h_build_pe_A :
      ∃ pe_A_scheduler : Scheduler sys_A.toSystem,
        ∀ l τ, sys_C.traceProb pe_C (Seq.cons l τ) =
          sys_A.traceProb ⟨pe_A_init, pe_A_scheduler⟩ (Seq.cons l τ) := by
    sorry
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
