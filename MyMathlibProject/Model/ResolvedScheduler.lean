/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Model.Fairness

/-!
# Resolved-history vs plain schedulers: the trace/fair comparison

The default `Scheduler` (`Model/System.lean`) is consulted on the **plain** history
`AlterSeq State Label` — the visited states and labels, but *not* the transition distributions
`μ` that were actually sampled. The **resolved-history** scheduler (`ResolvedScheduler`, in
`Model/Fairness.lean`) is consulted on the full
`ResolvedExec State Label = AlterSeq State (Label × PMF State)` (states, labels, *and* the chosen
`μ`s), and it is the scheduler notion underlying the canonical fair achievable set
`fairAchievableTraceDists`. This file develops the **comparison** between the two: they agree on
plain trace distributions but the resolved model is strictly more expressive for *sure-fair* trace
distributions.

## What changes and what doesn't

* **Trace distributions are unaffected.** `achievableTraceDistsR sys = achievableTraceDists sys`
  (`achievableTraceDistsR_eq`). One direction is the trivial coercion (a plain scheduler is a
  resolved scheduler that ignores the `μ`s); the other is the **de-resolution / averaging**
  argument: the posterior-average of a resolved scheduler over the `μ`-decorations of each plain
  history is a plain scheduler with the same one-step kernel, hence the same trace probabilities.
  The engine is the identity `probOf (average pe) e = ∑' (μ-decorations r of e), probOfR pe r`.

* **Fair trace distributions can change.** In the infinitely-branching setting a resolved scheduler
  can *commit* to an unbounded future (readable back from its own `μ`-history) and stay sure-fair,
  where every plain scheduler must fire within a bounded horizon and so realises only
  bounded-support fair trace distributions. See the worked separator in the comment block at the end
  of file.

* **The fair sets differ even under image-finiteness.** Only the trivial coercion
  `fairAchievableTraceDistsPlain F ⊆ fairAchievableTraceDists F`
  (`fairAchievableTraceDistsPlain_subset`, carrying fairness through `Scheduler.toResolved`) holds.
  The reverse inclusion is **false** — a finite-branching (image-finite) counterexample gives a
  resolved *sure*-fair trace distribution no plain scheduler achieves (`Model/ResolvedGap.lean`).
-/

open Stream'

namespace PLTS

variable {State Label : Type}

/-! ### The resolved-history scheduler and its comparison with plain schedulers

The resolved-history scheduler model — `ResolvedScheduler`, `ResolvedProbabilisticExecution`, the
path-measure `probOfR`, the trace distribution `traceProbR`, and the fair notions (`Consistent`,
`IsFair`, and the canonical `fairAchievableTraceDists`) — now lives in `Model/Fairness.lean`. This
file develops its **comparison** with the plain scheduler: the de-resolution / averaging argument
(the *trace* distributions coincide, `achievableTraceDistsR_eq`) and the plain-fair ⊆ resolved-fair
coercion. -/

/-! ### `ResolvedExec.toExec` reading lemmas

`toExec` forgets the chosen `μ`s: `r.toExec.trans = r.trans.map (fun p => (p.1.1, p.2))`. It
therefore preserves termination and the visited-state readout, which is all the plain scheduler is
consulted on. -/

/-- `Seq.map` commutes with `Seq.ofList`: forgetting to a list first, or mapping first, agree. -/
private theorem Seq.map_ofList {α β : Type} (f : α → β) (L : List α) :
    (Seq.ofList L).map f = Seq.ofList (L.map f) := by
  induction L with
  | nil => rw [Stream'.Seq.ofList_nil, Stream'.Seq.map_nil, List.map_nil, Stream'.Seq.ofList_nil]
  | cons a l ih =>
    rw [Stream'.Seq.ofList_cons, Stream'.Seq.map_cons, List.map_cons, Stream'.Seq.ofList_cons, ih]

/-- `Seq.map` commutes with the `n`-prefix `Seq.take` (both yield a list). -/
private theorem Seq.map_take {α β : Type} (f : α → β) (s : Seq α) (n : ℕ) :
    (Seq.take n s).map f = Seq.take n (s.map f) := by
  induction n generalizing s with
  | zero => rw [Stream'.Seq.take_zero, Stream'.Seq.take_zero, List.map_nil]
  | succ k ih =>
    induction s using Stream'.Seq.recOn with
    | nil => rw [Stream'.Seq.map_nil, Stream'.Seq.take_nil, Stream'.Seq.take_nil, List.map_nil]
    | cons a t =>
      rw [Stream'.Seq.map_cons, Stream'.Seq.take_succ_cons, Stream'.Seq.take_succ_cons,
        List.map_cons, ih]

namespace ResolvedExec

variable {State Label : Type}

@[simp] theorem toExec_init (r : ResolvedExec State Label) : r.toExec.init = r.init := rfl

theorem toExec_trans (r : ResolvedExec State Label) :
    r.toExec.trans = r.trans.map (fun p => (p.1.1, p.2)) := rfl

theorem toExec_terminatedAt_iff (r : ResolvedExec State Label) (n : ℕ) :
    r.toExec.trans.TerminatedAt n ↔ r.trans.TerminatedAt n := by
  unfold Stream'.Seq.TerminatedAt
  rw [toExec_trans, Stream'.Seq.map_get?, Option.map_eq_none_iff]

theorem toExec_terminates_iff (r : ResolvedExec State Label) :
    r.toExec.trans.Terminates ↔ r.trans.Terminates :=
  Stream'.Seq.terminates_map_iff

theorem toExec_stateAt (r : ResolvedExec State Label) (n : ℕ) :
    r.toExec.stateAt n = r.stateAt n := by
  cases n with
  | zero => rfl
  | succ k =>
    change ((r.trans.map (fun p => (p.1.1, p.2))).get? k).map Prod.snd
        = (r.trans.get? k).map Prod.snd
    rw [Stream'.Seq.map_get?]
    cases r.trans.get? k <;> rfl

/-- `toExec` commutes with the finite prefix `AlterSeq.take`: forgetting the `μ`s on the length-`n`
resolved prefix equals taking the length-`n` prefix of the forgotten history. -/
theorem toExec_take (r : ResolvedExec State Label) (n : ℕ) :
    ResolvedExec.toExec (r.take n) = (r.toExec).take n := by
  unfold ResolvedExec.toExec AlterSeq.take
  simp only [AlterSeq.mk.injEq, true_and]
  rw [Seq.map_ofList, Seq.map_take]

/-- A decoration of a terminating plain history terminates. -/
theorem terminates_of_toExec_eq {e : AlterSeq State Label} (he : e.trans.Terminates)
    {r : ResolvedExec State Label} (hr : r.toExec = e) : r.trans.Terminates :=
  (toExec_terminates_iff r).mp (by rw [hr]; exact he)

/-- `toExec` commutes with appending a final resolved transition `((l, μ), s')`: forgetting the
`μ` on the extended history is the same as extending the forgotten history by `(l, s')`. -/
theorem toExec_append_singleton (r' : ResolvedExec State Label)
    (l : Label) (μ : PMF State) (s' : State) :
    ResolvedExec.toExec ⟨r'.init, r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)⟩
      = ⟨r'.toExec.init, r'.toExec.trans.append (Seq.cons (l, s') Seq.nil)⟩ := by
  unfold ResolvedExec.toExec
  simp only [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil]

/-- A decoration of the empty plain history `⟨s₀, nil⟩` is itself `⟨s₀, nil⟩`. -/
theorem eq_nil_of_toExec_nil {r : ResolvedExec State Label} {s₀ : State}
    (hr : r.toExec = ⟨s₀, Seq.nil⟩) : r = ⟨s₀, Seq.nil⟩ := by
  have h_init : r.init = s₀ := by
    have := congrArg AlterSeq.init hr
    rwa [toExec_init] at this
  have h_trans : r.trans = Seq.nil := by
    have hz : r.toExec.trans.TerminatedAt 0 := by
      rw [hr]; exact Stream'.Seq.terminatedAt_zero_iff.mpr rfl
    exact Stream'.Seq.terminatedAt_zero_iff.mp ((toExec_terminatedAt_iff r 0).mp hz)
  cases r with
  | mk i t => cases h_init; cases h_trans; rfl

/-- Extend a decoration `r'` of `e'` by choosing `μ` for a final `(l, s')` transition, yielding a
decoration of `e' ++ (l, s')`. The forward object of the crux bijection "decorations of
`e' ++ (l, s')` ↔ decorations of `e'` times a chosen `μ`". -/
def snocDecoration (e' : AlterSeq State Label) (l : Label) (s' : State)
    (p : {r' : ResolvedExec State Label // r'.toExec = e'} × PMF State) :
    {r : ResolvedExec State Label //
      r.toExec = ⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩} :=
  ⟨⟨p.1.1.init, p.1.1.trans.append (Seq.cons ((l, p.2), s') Seq.nil)⟩, by
    rw [toExec_append_singleton, p.1.2]⟩

theorem snocDecoration_injective {e' : AlterSeq State Label} (he' : e'.trans.Terminates)
    (l : Label) (s' : State) :
    Function.Injective (snocDecoration e' l s') := by
  rintro ⟨⟨r₁, hr₁⟩, μ₁⟩ ⟨⟨r₂, hr₂⟩, μ₂⟩ h
  have hAlt :
      (⟨r₁.init, r₁.trans.append (Seq.cons ((l, μ₁), s') Seq.nil)⟩ : ResolvedExec State Label)
        = ⟨r₂.init, r₂.trans.append (Seq.cons ((l, μ₂), s') Seq.nil)⟩ := congrArg Subtype.val h
  rw [AlterSeq.mk.injEq] at hAlt
  obtain ⟨h_init, h_trans⟩ := hAlt
  have ht₁ : r₁.trans.Terminates := terminates_of_toExec_eq he' hr₁
  have ht₂ : r₂.trans.Terminates := terminates_of_toExec_eq he' hr₂
  have hlast : ((l, μ₁), s') = ((l, μ₂), s') :=
    Stream'.Seq.append_singleton_inj_right r₁.trans r₂.trans ht₁ ht₂ _ _ h_trans
  have htr : r₁.trans = r₂.trans :=
    Stream'.Seq.append_singleton_inj_left r₁.trans r₂.trans ht₁ ht₂ _ _ h_trans
  have hμ : μ₁ = μ₂ := congrArg (fun x => x.1.2) hlast
  have hr : r₁ = r₂ := by
    cases r₁ with | mk i₁ t₁ => cases r₂ with | mk i₂ t₂ => cases h_init; cases htr; rfl
  subst hr; subst hμ; rfl

theorem exists_snocDecoration {e' : AlterSeq State Label} (he' : e'.trans.Terminates)
    (l : Label) (s' : State)
    (r : {r : ResolvedExec State Label //
      r.toExec = ⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩}) :
    ∃ p, snocDecoration e' l s' p = r := by
  have hmap : r.1.trans.map (fun p => (p.1.1, p.2))
      = e'.trans.append (Seq.cons (l, s') Seq.nil) := by
    have := congrArg AlterSeq.trans r.2
    rwa [toExec_trans] at this
  have hs1 : (Seq.cons (l, s') Seq.nil : Seq (Label × State)).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  have hE : (e'.trans.append (Seq.cons (l, s') Seq.nil)).Terminates :=
    ⟨_, Stream'.Seq.terminatedAt_append_find he' hs1.choose_spec⟩
  have hRterm : r.1.trans.Terminates := terminates_of_toExec_eq hE r.2
  have hne : r.1.trans.toList hRterm ≠ [] := by
    intro hnil
    have htrans_nil : r.1.trans = Seq.nil := by
      have h := Stream'.Seq.ofList_toList r.1.trans hRterm
      rw [hnil, Stream'.Seq.ofList_nil] at h
      exact h.symm
    rw [htrans_nil, Stream'.Seq.map_nil] at hmap
    have h0 : (e'.trans.append (Seq.cons (l, s') Seq.nil)).get? (Nat.find he') = some (l, s') := by
      have := Stream'.Seq.get?_append_find he' (Seq.cons (l, s') Seq.nil) 0
      rw [Nat.add_zero] at this
      rw [this]; rfl
    rw [← hmap] at h0
    simp at h0
  obtain ⟨prev, last, hprev, hsplit, _, _⟩ := Stream'.Seq.exists_split_last r.1.trans hRterm hne
  have hmap' : (prev.map (fun p => (p.1.1, p.2))).append
        (Seq.cons ((fun p => (p.1.1, p.2)) last) Seq.nil)
      = e'.trans.append (Seq.cons (l, s') Seq.nil) := by
    have h1 : (prev.append (Seq.cons last Seq.nil)).map (fun p => (p.1.1, p.2))
        = e'.trans.append (Seq.cons (l, s') Seq.nil) := by rw [← hsplit]; exact hmap
    rwa [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil] at h1
  have htprevmap : (prev.map (fun p => (p.1.1, p.2))).Terminates :=
    Stream'.Seq.terminates_map_iff.mpr hprev
  have hprevmap : prev.map (fun p => (p.1.1, p.2)) = e'.trans :=
    Stream'.Seq.append_singleton_inj_left _ _ htprevmap he' _ _ hmap'
  have hlast : (fun p => (p.1.1, p.2)) last = (l, s') :=
    Stream'.Seq.append_singleton_inj_right _ _ htprevmap he' _ _ hmap'
  have hlast_eq : last = ((l, last.1.2), s') := by
    have h1 : last.1.1 = l := congrArg Prod.fst hlast
    have h2 : last.2 = s' := congrArg Prod.snd hlast
    rw [← h1, ← h2]
  have h_init : r.1.init = e'.init := by
    have := congrArg AlterSeq.init r.2
    rwa [toExec_init] at this
  refine ⟨(⟨⟨r.1.init, prev⟩, ?_⟩, last.1.2), ?_⟩
  · unfold ResolvedExec.toExec
    rw [hprevmap, h_init]
  · apply Subtype.ext
    change (⟨r.1.init, prev.append (Seq.cons ((l, last.1.2), s') Seq.nil)⟩ :
      ResolvedExec State Label) = r.1
    rw [← hlast_eq, ← hsplit]

end ResolvedExec

/-- Trace distributions achievable by a **resolved-history** execution started from the Dirac
initial distribution. The resolved analogue of `achievableTraceDists`. -/
def achievableTraceDistsR [Silent Label] (sys : System State Label) :
    Set (Seq Label → ENNReal) :=
  {D | ∃ pe : ResolvedProbabilisticExecution sys,
    pe.initState = PMF.pure sys.init ∧ ∀ τ, pe.traceProbR τ = D τ}

/-! ### Plain ⊆ Resolved (the trivial coercion) -/

/-- A plain scheduler as a resolved scheduler that ignores the `μ`-history. -/
def Scheduler.toResolved {sys : System State Label} (σ : Scheduler sys) :
    ResolvedScheduler sys where
  next r := σ.next r.toExec
  valid := by
    intro r n s hterm hstate l μ hmem
    refine σ.valid r.toExec n s ?_ ?_ l μ hmem
    · exact (ResolvedExec.toExec_terminatedAt_iff r n).mpr hterm
    · rw [ResolvedExec.toExec_stateAt]; exact hstate

/-- A plain probabilistic execution as a resolved one. -/
def ProbabilisticExecution.toResolved {sys : System State Label}
    (pe : ProbabilisticExecution sys) : ResolvedProbabilisticExecution sys :=
  ⟨pe.initState, pe.scheduler.toResolved⟩

/-! ### Resolved ⊆ Plain (the de-resolution / averaging argument)

Given a resolved execution `pe`, its **average** is the plain execution whose scheduler, at plain
history `e`, is the `probOfR`-posterior-weighted average of `pe.scheduler.next` over all resolved
histories `r` with `r.toExec = e`. The key identity (`probOf_average`) is

  `(average pe).probOf e = ∑' (r with r.toExec = e), pe.probOfR r`

proven by cons-end induction (the `μ`-sum in the plain kernel reassembles the resolved decorations).
Summing over tight terminating `e` with trace `τ` then gives
`traceProb (average pe) = traceProbR`. -/

/-- The marginal weight `∑' (r with r.toExec = e), probOfR pe r` of a plain history `e` under a
resolved execution. Equals `(average pe).probOf e` (see `probOf_average`). -/
noncomputable def ResolvedProbabilisticExecution.avgWeight {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (e : AlterSeq State Label)
    (he : e.trans.Terminates) : ENNReal :=
  ∑' r : {r : ResolvedExec State Label // r.toExec = e},
    pe.probOfR r.1 (ResolvedExec.terminates_of_toExec_eq he r.2)

namespace ResolvedProbabilisticExecution

variable {sys : System State Label}

/-- `avgWeight` depends only on the history, not the termination proof. -/
theorem avgWeight_congr (pe : ResolvedProbabilisticExecution sys)
    (e e' : AlterSeq State Label) (h : e = e')
    (he : e.trans.Terminates) (he' : e'.trans.Terminates) :
    pe.avgWeight e he = pe.avgWeight e' he' := by subst h; rfl

/-- The one-step resolved kernel summed over the chosen `μ` is bounded by `1` (mirror of
`ProbabilisticExecution.kernel_le_one`). -/
theorem resolved_step_le_one (pe : ResolvedProbabilisticExecution sys)
    (r : ResolvedExec State Label) (l : Label) (s' : State) :
    ∑' μ : PMF State, pe.scheduler.next r (some (l, μ)) * μ s' ≤ 1 := by
  calc ∑' μ : PMF State, pe.scheduler.next r (some (l, μ)) * μ s'
      ≤ ∑' μ : PMF State, pe.scheduler.next r (some (l, μ)) := by
        refine ENNReal.tsum_le_tsum (fun μ => ?_)
        exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
    _ ≤ ∑' lμ : Label × PMF State, pe.scheduler.next r (some lμ) := by
        exact ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun μ => (l, μ)) (fun μ₁ μ₂ h_eq => (Prod.mk.inj h_eq).2)
          (fun lμ => pe.scheduler.next r (some lμ))
    _ ≤ ∑' opt, pe.scheduler.next r opt := by
        exact ENNReal.tsum_comp_le_tsum_of_injective
          (f := some) (fun _ _ h => Option.some.inj h) (fun opt => pe.scheduler.next r opt)
    _ = 1 := (pe.scheduler.next r).tsum_coe

/-- **Value identity** for the crux bijection: producing the `snocDecoration` of `p` is producing
`p.1` then the resolved step `((l, p.2), s')`. -/
theorem probOfR_snocDecoration (pe : ResolvedProbabilisticExecution sys)
    {e' : AlterSeq State Label} (l : Label) (s' : State)
    (p : {r' : ResolvedExec State Label // r'.toExec = e'} × PMF State)
    (h1 : (ResolvedExec.snocDecoration e' l s' p).1.trans.Terminates)
    (h2 : p.1.1.trans.Terminates) :
    pe.probOfR (ResolvedExec.snocDecoration e' l s' p).1 h1
      = pe.probOfR p.1.1 h2 * (pe.scheduler.next p.1.1 (some (l, p.2)) * p.2 s') := by
  change pe.probOfR ⟨p.1.1.init, p.1.1.trans.append (Seq.cons ((l, p.2), s') Seq.nil)⟩ h1 = _
  rw [pe.probOfR_append_singleton p.1.1.init p.1.1.trans h2 ((l, p.2), s') h1]
  rfl

/-- **Base of the reindexing.** The empty plain history has a single decoration, so its marginal is
the initial mass. -/
theorem avgWeight_nil (pe : ResolvedProbabilisticExecution sys) (s₀ : State) :
    pe.avgWeight ⟨s₀, Seq.nil⟩ Stream'.Seq.terminates_nil = pe.initState s₀ := by
  unfold ResolvedProbabilisticExecution.avgWeight
  rw [tsum_eq_single ⟨⟨s₀, Seq.nil⟩, by unfold ResolvedExec.toExec; rw [Stream'.Seq.map_nil]⟩
    (fun b hb => absurd (Subtype.ext (ResolvedExec.eq_nil_of_toExec_nil b.2)) hb)]
  exact pe.probOfR_nil s₀

/-- **Cons-end step of the reindexing** (the crux bijection). The marginal of `e' ++ (l, s')` is the
`probOfR`-weighted average, over decorations `r'` of `e'` and chosen `μ`, of one more resolved
step. -/
theorem avgWeight_append_singleton (pe : ResolvedProbabilisticExecution sys)
    (e' : AlterSeq State Label) (he' : e'.trans.Terminates) (l : Label) (s' : State)
    (hE : (e'.trans.append (Seq.cons (l, s') Seq.nil)).Terminates) :
    pe.avgWeight ⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩ hE
      = ∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'}, ∑' μ : PMF State,
          pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
            * (pe.scheduler.next r'.1 (some (l, μ)) * μ s') := by
  unfold ResolvedProbabilisticExecution.avgWeight
  have key : (∑' r : {r : ResolvedExec State Label //
        r.toExec = ⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩},
        pe.probOfR r.1 (ResolvedExec.terminates_of_toExec_eq hE r.2))
      = ∑' p : {r' : ResolvedExec State Label // r'.toExec = e'} × PMF State,
          pe.probOfR p.1.1 (ResolvedExec.terminates_of_toExec_eq he' p.1.2)
            * (pe.scheduler.next p.1.1 (some (l, p.2)) * p.2 s') := by
    refine tsum_eq_tsum_of_ne_zero_bij
      (fun x => ResolvedExec.snocDecoration e' l s' x.1) ?_ ?_ ?_
    · exact fun x y hxy => Subtype.ext (ResolvedExec.snocDecoration_injective he' l s' hxy)
    · intro r hr
      obtain ⟨p, hp⟩ := ResolvedExec.exists_snocDecoration he' l s' r
      have hval : pe.probOfR p.1.1 (ResolvedExec.terminates_of_toExec_eq he' p.1.2)
            * (pe.scheduler.next p.1.1 (some (l, p.2)) * p.2 s')
          = pe.probOfR r.1 (ResolvedExec.terminates_of_toExec_eq hE r.2) := by
        rw [← hp]
        exact (pe.probOfR_snocDecoration l s' p _ _).symm
      exact ⟨⟨p, by rw [Function.mem_support, hval]; exact hr⟩, hp⟩
    · intro x
      exact pe.probOfR_snocDecoration l s' x.1 _ _
  rw [key]
  exact ENNReal.tsum_prod'

/-- **The marginal is bounded by the initial mass** (hence by `1`), via the cons-end reindexing. -/
theorem avgWeight_le_init (pe : ResolvedProbabilisticExecution sys)
    (e : AlterSeq State Label) (he : e.trans.Terminates) :
    pe.avgWeight e he ≤ pe.initState e.init := by
  suffices H : ∀ n (e : AlterSeq State Label) (he : e.trans.Terminates),
      (e.trans.toList he).length = n → pe.avgWeight e he ≤ pe.initState e.init from H _ e he rfl
  intro n
  induction n with
  | zero =>
    intro e he hlen
    have htoList : e.trans.toList he = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := e
    have h_nil : t = Seq.nil := by
      have h := Stream'.Seq.ofList_toList t he
      rw [htoList, Stream'.Seq.ofList_nil] at h
      exact h.symm
    subst h_nil
    exact le_of_eq (pe.avgWeight_nil i)
  | succ k ih =>
    intro e he hlen
    have hne : e.trans.toList he ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last e.trans he hne
    obtain ⟨l, s'⟩ := last
    have happ : (prev.append (Seq.cons (l, s') Seq.nil)).Terminates := hsplit ▸ he
    have he_eq : e = ⟨e.init, prev.append (Seq.cons (l, s') Seq.nil)⟩ := by
      obtain ⟨ei, et⟩ := e; exact congrArg (AlterSeq.mk ei) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (e.trans.toList he).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    have h1 : pe.avgWeight e he
        = ∑' r' : {r' : ResolvedExec State Label // r'.toExec = ⟨e.init, prev⟩},
            ∑' μ : PMF State,
              pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq hprev r'.2)
                * (pe.scheduler.next r'.1 (some (l, μ)) * μ s') := by
      rw [pe.avgWeight_congr e ⟨e.init, prev.append (Seq.cons (l, s') Seq.nil)⟩ he_eq he happ]
      exact pe.avgWeight_append_singleton ⟨e.init, prev⟩ hprev l s' happ
    have h2 : (∑' r' : {r' : ResolvedExec State Label // r'.toExec = ⟨e.init, prev⟩},
                ∑' μ : PMF State,
                  pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq hprev r'.2)
                    * (pe.scheduler.next r'.1 (some (l, μ)) * μ s'))
          ≤ ∑' r' : {r' : ResolvedExec State Label // r'.toExec = ⟨e.init, prev⟩},
              pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq hprev r'.2) := by
      refine ENNReal.tsum_le_tsum (fun r' => ?_)
      rw [ENNReal.tsum_mul_left]
      calc pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq hprev r'.2)
            * ∑' μ : PMF State, pe.scheduler.next r'.1 (some (l, μ)) * μ s'
          ≤ pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq hprev r'.2) * 1 := by
            gcongr; exact pe.resolved_step_le_one r'.1 l s'
        _ = pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq hprev r'.2) := mul_one _
    rw [h1]
    exact h2.trans (ih ⟨e.init, prev⟩ hprev hlen_prev)

/-- The total mass of the un-normalised averaged emission at `e` is the marginal `avgWeight e`. -/
theorem avgWeight_eq_tsum (pe : ResolvedProbabilisticExecution sys)
    (e : AlterSeq State Label) (hT : e.trans.Terminates) :
    (∑' x : Option (Label × PMF State), ∑' r : {r : ResolvedExec State Label // r.toExec = e},
        pe.probOfR r.1 (ResolvedExec.terminates_of_toExec_eq hT r.2) * pe.scheduler.next r.1 x)
      = pe.avgWeight e hT := by
  rw [ENNReal.tsum_comm]
  unfold ResolvedProbabilisticExecution.avgWeight
  refine tsum_congr (fun r => ?_)
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

end ResolvedProbabilisticExecution

open Classical in
/-- The averaged plain scheduler of a resolved execution (posterior-weighted mixture of the
resolved emissions over the `μ`-decorations of the plain history). -/
noncomputable def ResolvedProbabilisticExecution.average {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) : ProbabilisticExecution sys where
  initState := pe.initState
  scheduler :=
    { next := fun e =>
        if hT : e.trans.Terminates then
          if h0 : pe.avgWeight e hT ≠ 0 then
            PMF.normalize
              (fun x => ∑' r : {r : ResolvedExec State Label // r.toExec = e},
                pe.probOfR r.1 (ResolvedExec.terminates_of_toExec_eq hT r.2)
                  * pe.scheduler.next r.1 x)
              (by rw [pe.avgWeight_eq_tsum e hT]; exact h0)
              (by rw [pe.avgWeight_eq_tsum e hT]
                  exact (((pe.avgWeight_le_init e hT).trans (PMF.coe_le_one _ _)).trans_lt
                    ENNReal.one_lt_top).ne)
          else PMF.pure none
        else PMF.pure none
      valid := by
        intro e n s hterm hstate l μ hmem
        have hT : e.trans.Terminates := ⟨n, hterm⟩
        simp only [dif_pos hT] at hmem
        by_cases h0 : pe.avgWeight e hT ≠ 0
        · rw [dif_pos h0, PMF.mem_support_iff, PMF.normalize_apply] at hmem
          have hN := (mul_ne_zero_iff.mp hmem).1
          obtain ⟨r, hr⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hN)
          have hne : pe.scheduler.next r.1 (some (l, μ)) ≠ 0 := fun h => hr (by rw [h, mul_zero])
          refine pe.scheduler.valid r.1 n s ?_ ?_ l μ ((PMF.mem_support_iff _ _).mpr hne)
          · exact (ResolvedExec.toExec_terminatedAt_iff r.1 n).mp (by rw [r.2]; exact hterm)
          · rw [← ResolvedExec.toExec_stateAt, r.2]; exact hstate
        · rw [dif_neg h0] at hmem
          simp at hmem }

/-- The averaged emission on a `some (l, μ)` step: the posterior-weighted mixture of the resolved
emissions, normalised by the marginal. (Holds in both branches: when `avgWeight e' = 0` both sides
are `0`, using `0 * ⊤ = 0`.) -/
theorem ResolvedProbabilisticExecution.average_next_some {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (e' : AlterSeq State Label)
    (he' : e'.trans.Terminates) (l : Label) (μ : PMF State) :
    pe.average.scheduler.next e' (some (l, μ))
      = (∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
            pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
              * pe.scheduler.next r'.1 (some (l, μ)))
          * (pe.avgWeight e' he')⁻¹ := by
  classical
  by_cases hW : pe.avgWeight e' he' ≠ 0
  · simp only [ResolvedProbabilisticExecution.average]
    rw [dif_pos he', dif_pos hW, PMF.normalize_apply, pe.avgWeight_eq_tsum e' he']
  · rw [not_not] at hW
    have hW' : (∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
        pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)) = 0 := hW
    have hN : (∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
        pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
          * pe.scheduler.next r'.1 (some (l, μ))) = 0 := by
      refine ENNReal.tsum_eq_zero.mpr (fun r' => ?_)
      rw [ENNReal.tsum_eq_zero.mp hW' r', zero_mul]
    rw [hN, zero_mul]
    simp only [ResolvedProbabilisticExecution.average]
    rw [dif_pos he', dif_neg (fun h => h hW)]
    simp

/-- The averaged emission on the `none` (halt) step, in the branch where the marginal is positive:
the posterior-weighted mixture of the resolved halt-emissions, normalised by the marginal. (The
`none`-analogue of `average_next_some`; unlike that lemma the `avgWeight = 0` branch differs, since
the fallback `PMF.pure none` puts mass on `none`, so we take `avgWeight ≠ 0` as a hypothesis.) -/
theorem ResolvedProbabilisticExecution.average_next_none {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (e' : AlterSeq State Label)
    (he' : e'.trans.Terminates) (hW : pe.avgWeight e' he' ≠ 0) :
    pe.average.scheduler.next e' none
      = (∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
            pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
              * pe.scheduler.next r'.1 none)
          * (pe.avgWeight e' he')⁻¹ := by
  classical
  simp only [ResolvedProbabilisticExecution.average]
  rw [dif_pos he', dif_pos hW, PMF.normalize_apply, pe.avgWeight_eq_tsum e' he']

/-- **Cons-end step of `probOf_average`.** The one-step plain kernel of the average, weighted by the
marginal, reproduces the extended marginal (the posterior denominator cancels the marginal). -/
theorem ResolvedProbabilisticExecution.avgWeight_average_step {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (e' : AlterSeq State Label)
    (he' : e'.trans.Terminates) (l : Label) (s' : State)
    (happ : (e'.trans.append (Seq.cons (l, s') Seq.nil)).Terminates) :
    pe.avgWeight e' he' * pe.average.kernel e' (l, s')
      = pe.avgWeight ⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩ happ := by
  rw [pe.avgWeight_append_singleton e' he' l s' happ]
  have hRHS : (∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'}, ∑' μ : PMF State,
        pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
          * (pe.scheduler.next r'.1 (some (l, μ)) * μ s'))
      = ∑' μ : PMF State, (∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
          pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
            * pe.scheduler.next r'.1 (some (l, μ))) * μ s' := by
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun μ => ?_)
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr (fun r' => ?_)
    rw [mul_assoc]
  rw [hRHS]
  unfold ProbabilisticExecution.kernel
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun μ => ?_)
  rw [pe.average_next_some e' he' l μ]
  set N := ∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
    pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
      * pe.scheduler.next r'.1 (some (l, μ)) with hNdef
  by_cases hW : pe.avgWeight e' he' = 0
  · have hN0 : N = 0 := by
      rw [hNdef]
      refine ENNReal.tsum_eq_zero.mpr (fun r' => ?_)
      have hW' : (∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
          pe.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)) = 0 := hW
      rw [ENNReal.tsum_eq_zero.mp hW' r', zero_mul]
    rw [hN0]; simp
  · have hWtop : pe.avgWeight e' he' ≠ ⊤ :=
      (((pe.avgWeight_le_init e' he').trans (PMF.coe_le_one _ _)).trans_lt ENNReal.one_lt_top).ne
    rw [show pe.avgWeight e' he' * (N * (pe.avgWeight e' he')⁻¹ * μ s')
          = pe.avgWeight e' he' * (pe.avgWeight e' he')⁻¹ * (N * μ s') from by ring,
        ENNReal.mul_inv_cancel hW hWtop, one_mul]

theorem ResolvedProbabilisticExecution.probOf_average [Silent Label] {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (e : AlterSeq State Label)
    (he : e.trans.Terminates) :
    pe.average.probOf e he = pe.avgWeight e he := by
  suffices H : ∀ n (e : AlterSeq State Label) (he : e.trans.Terminates),
      (e.trans.toList he).length = n → pe.average.probOf e he = pe.avgWeight e he from H _ e he rfl
  intro n
  induction n with
  | zero =>
    intro e he hlen
    have htoList : e.trans.toList he = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := e
    have h_nil : t = Seq.nil := by
      have h := Stream'.Seq.ofList_toList t he
      rw [htoList, Stream'.Seq.ofList_nil] at h
      exact h.symm
    subst h_nil
    exact (pe.average.probOf_nil i).trans (pe.avgWeight_nil i).symm
  | succ k ih =>
    intro e he hlen
    have hne : e.trans.toList he ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last e.trans he hne
    obtain ⟨l, s'⟩ := last
    have happ : (prev.append (Seq.cons (l, s') Seq.nil)).Terminates := hsplit ▸ he
    have he_eq : e = ⟨e.init, prev.append (Seq.cons (l, s') Seq.nil)⟩ := by
      obtain ⟨ei, et⟩ := e; exact congrArg (AlterSeq.mk ei) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (e.trans.toList he).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    rw [pe.average.probOf_congr e ⟨e.init, prev.append (Seq.cons (l, s') Seq.nil)⟩ he_eq he happ,
        pe.avgWeight_congr e ⟨e.init, prev.append (Seq.cons (l, s') Seq.nil)⟩ he_eq he happ,
        pe.average.probOf_append_singleton e.init prev hprev (l, s') happ,
        ih ⟨e.init, prev⟩ hprev hlen_prev]
    exact pe.avgWeight_average_step ⟨e.init, prev⟩ hprev l s' happ

/-- **Shared reindexing.** Summing the marginal `avgWeight` over the tight terminating trace-`τ`
plain histories reproduces `traceProbR` (each resolved run is grouped under its plain image). -/
theorem ResolvedProbabilisticExecution.traceProbR_eq_sum_avgWeight [Silent Label]
    {sys : System State Label} (pe : ResolvedProbabilisticExecution sys) (τ : Seq Label) :
    (∑' e : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e}, pe.avgWeight e.1 e.2.1)
      = pe.traceProbR τ := by
  unfold ResolvedProbabilisticExecution.avgWeight ResolvedProbabilisticExecution.traceProbR
  rw [← ENNReal.tsum_sigma' (f := fun p : Σ e : {e : AlterSeq State Label //
      e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e}, {r : ResolvedExec State Label //
        r.toExec = e.1} => pe.probOfR p.2.1 (ResolvedExec.terminates_of_toExec_eq p.1.2.1 p.2.2))]
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun r => ⟨⟨r.1.1.toExec, (ResolvedExec.toExec_terminates_iff r.1.1).mpr r.1.2.1,
        r.1.2.2.1, r.1.2.2.2⟩, r.1.1, rfl⟩) ?_ ?_ ?_
  · intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun p => p.2.1) h))
  · intro p hp
    refine ⟨⟨⟨p.2.1, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · exact (ResolvedExec.toExec_terminates_iff p.2.1).mp (by rw [p.2.2]; exact p.1.2.1)
    · rw [p.2.2]; exact p.1.2.2.1
    · rw [p.2.2]; exact p.1.2.2.2
    · rw [Function.mem_support]; exact hp
    · exact Sigma.subtype_ext (Subtype.ext p.2.2) rfl
  · intro r; rfl

theorem ResolvedProbabilisticExecution.traceProb_average [Silent Label] {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (τ : Seq Label) :
    sys.traceProb pe.average τ = pe.traceProbR τ := by
  rw [← pe.traceProbR_eq_sum_avgWeight τ]
  unfold System.traceProb
  exact tsum_congr (fun e => pe.probOf_average e.1 e.2.1)

theorem achievableTraceDistsR_subset [Silent Label] (sys : System State Label) :
    achievableTraceDistsR sys ⊆ achievableTraceDists sys := by
  rintro D ⟨pe, h_init, h_tp⟩
  refine ⟨pe.average, ?_, fun τ => (pe.traceProb_average τ).trans (h_tp τ)⟩
  · change pe.initState = _; exact h_init

/-! ### Plain ⊆ Resolved (the trivial coercion, via the averaging identity)

A plain scheduler coerced to a resolved one ignores the `μ`-history, so at each decoration its
emission is constant; the marginal `avgWeight (toResolved pe)` collapses to `pe.probOf`. -/

/-- **Cons-end step of `avgWeight_toResolved`.** For the coerced scheduler the resolved emission is
constant in the `μ`-history, so the extended marginal factors through the plain one-step kernel. -/
theorem ProbabilisticExecution.avgWeight_toResolved_step {sys : System State Label}
    (pe : ProbabilisticExecution sys) (e' : AlterSeq State Label) (he' : e'.trans.Terminates)
    (l : Label) (s' : State) (happ : (e'.trans.append (Seq.cons (l, s') Seq.nil)).Terminates) :
    pe.toResolved.avgWeight ⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩ happ
      = pe.toResolved.avgWeight e' he' * pe.kernel e' (l, s') := by
  rw [pe.toResolved.avgWeight_append_singleton e' he' l s' happ]
  have hstep : ∀ (r' : {r' : ResolvedExec State Label // r'.toExec = e'}) (μ : PMF State),
      pe.toResolved.scheduler.next r'.1 (some (l, μ)) = pe.scheduler.next e' (some (l, μ)) := by
    intro r' μ
    change pe.scheduler.next r'.1.toExec (some (l, μ)) = pe.scheduler.next e' (some (l, μ))
    rw [r'.2]
  simp only [hstep]
  unfold ProbabilisticExecution.kernel
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun μ => ?_)
  rw [ENNReal.tsum_mul_right]
  rfl

theorem ProbabilisticExecution.avgWeight_toResolved {sys : System State Label}
    (pe : ProbabilisticExecution sys) (e : AlterSeq State Label) (he : e.trans.Terminates) :
    pe.toResolved.avgWeight e he = pe.probOf e he := by
  suffices H : ∀ n (e : AlterSeq State Label) (he : e.trans.Terminates),
      (e.trans.toList he).length = n → pe.toResolved.avgWeight e he = pe.probOf e he from
    H _ e he rfl
  intro n
  induction n with
  | zero =>
    intro e he hlen
    have htoList : e.trans.toList he = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := e
    have h_nil : t = Seq.nil := by
      have h := Stream'.Seq.ofList_toList t he
      rw [htoList, Stream'.Seq.ofList_nil] at h
      exact h.symm
    subst h_nil
    exact (pe.toResolved.avgWeight_nil i).trans (pe.probOf_nil i).symm
  | succ k ih =>
    intro e he hlen
    have hne : e.trans.toList he ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last e.trans he hne
    obtain ⟨l, s'⟩ := last
    have happ : (prev.append (Seq.cons (l, s') Seq.nil)).Terminates := hsplit ▸ he
    have he_eq : e = ⟨e.init, prev.append (Seq.cons (l, s') Seq.nil)⟩ := by
      obtain ⟨ei, et⟩ := e; exact congrArg (AlterSeq.mk ei) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (e.trans.toList he).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    rw [pe.toResolved.avgWeight_congr e ⟨e.init, prev.append (Seq.cons (l, s') Seq.nil)⟩ he_eq he
          happ,
        pe.probOf_congr e ⟨e.init, prev.append (Seq.cons (l, s') Seq.nil)⟩ he_eq he happ,
        pe.avgWeight_toResolved_step ⟨e.init, prev⟩ hprev l s' happ,
        pe.probOf_append_singleton e.init prev hprev (l, s') happ,
        ih ⟨e.init, prev⟩ hprev hlen_prev]

/-- The coercion preserves trace probabilities: the resolved kernel of the coerced scheduler, summed
over the `μ`-decorations, collapses to the plain kernel `∑' μ, next (some (l,μ)) · μ s'`. -/
theorem ProbabilisticExecution.traceProbR_toResolved [Silent Label] {sys : System State Label}
    (pe : ProbabilisticExecution sys) (τ : Seq Label) :
    pe.toResolved.traceProbR τ = sys.traceProb pe τ := by
  rw [← pe.toResolved.traceProbR_eq_sum_avgWeight τ]
  unfold System.traceProb
  exact tsum_congr (fun e => pe.avgWeight_toResolved e.1 e.2.1)

theorem achievableTraceDists_subset_resolved [Silent Label] (sys : System State Label) :
    achievableTraceDists sys ⊆ achievableTraceDistsR sys := by
  rintro D ⟨pe, h_init, h_tp⟩
  exact ⟨pe.toResolved, h_init, fun τ => (pe.traceProbR_toResolved τ).trans (h_tp τ)⟩

/-- **Trace distributions are model-invariant.** Feeding the scheduler the resolved history does not
change the set of achievable trace distributions. -/
theorem achievableTraceDistsR_eq [Silent Label] (sys : System State Label) :
    achievableTraceDistsR sys = achievableTraceDists sys :=
  Set.Subset.antisymm (achievableTraceDistsR_subset sys) (achievableTraceDists_subset_resolved sys)

/-! ### Plain-scheduler fairness (the weaker comparison notion)

The plain scheduler is consulted on the *plain* history only, so it cannot read back which
transition `(l, μ)` produced each step. Its fair achievable set `fairAchievableTraceDistsPlain` is
the weaker object the canonical resolved `fairAchievableTraceDists` (`Model/Fairness.lean`) is
compared against below; the two differ even for image-finite systems (`Model/ResolvedGap.lean`). -/

namespace ProbabilisticExecution

variable {sys : System State Label}

/-- A (possibly infinite) resolved execution `r` is **consistent** with the *plain* probabilistic
execution `pe` when its start state has positive initial mass and, at every step, the chosen
transition `(l, μ)` lies in the support of the scheduler's output at the preceding *plain* prefix
and the sampled next state lies in the support of `μ`. The plain-scheduler analogue of
`ResolvedProbabilisticExecution.Consistent`; it consults the plain history `r.toExec.take n`. -/
def Consistent (pe : ProbabilisticExecution sys) (r : ResolvedExec State Label) : Prop :=
  pe.initState r.init ≠ 0 ∧
    ∀ (n : ℕ) (l : Label) (μ : PMF State) (s' : State),
      r.trans.get? n = some ((l, μ), s') →
        pe.scheduler.next (r.toExec.take n) (some (l, μ)) ≠ 0 ∧ μ s' ≠ 0

end ProbabilisticExecution

/-- A *plain* probabilistic execution `pe` is **fair** for the marking `F` when it schedules `none`
(halts) only from a fair deadlock and every infinite consistent run takes infinitely many fair
transitions. The plain-scheduler analogue of `ResolvedProbabilisticExecution.IsFair`: the halting
emission and the scheduler are consulted on the *plain* history `r.toExec`. -/
structure ProbabilisticExecution.IsFair [Silent Label] {sys : System State Label} (F : Fairness sys)
    (pe : ProbabilisticExecution sys) : Prop where
  /-- Halting (`none`) happens only from a fair deadlock. -/
  halt_fairDeadlock : ∀ (r : ResolvedExec State Label) (h : r.trans.Terminates),
    pe.Consistent r → pe.scheduler.next r.toExec none ≠ 0 → F.FairDeadlock (r.endState h)
  /-- Every infinite consistent run takes infinitely many fair transitions. -/
  inf_fair : ∀ r : ResolvedExec State Label, ¬ r.trans.Terminates → pe.Consistent r →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ F.FairStepAt r n

/-- The set of trace distributions achievable by some **fair** *plain* probabilistic execution of
`sys` started from the Dirac initial distribution — the weaker, plain-scheduler analogue of the
canonical `fairAchievableTraceDists` (`Model/Fairness.lean`). Retained only for the comparison: it
is strictly smaller than `fairAchievableTraceDists` even for image-finite systems
(`Model/ResolvedGap.lean`). -/
def fairAchievableTraceDistsPlain [Silent Label] {sys : System State Label} (F : Fairness sys) :
    Set (Seq Label → ENNReal) :=
  {D | ∃ pe : ProbabilisticExecution sys,
    pe.initState = PMF.pure sys.init ∧ pe.IsFair F ∧ ∀ τ, sys.traceProb pe τ = D τ}

/-! ### Plain-fair ⊆ resolved-fair (the easy `⊇` direction)

A plain-fair `pe` coerces to a resolved-fair `pe.toResolved` with the same trace distribution.
The coerced resolved scheduler ignores the `μ`-history (`next r = σ.next r.toExec`), so its
consistent runs are exactly the consistent runs of `pe` (`consistent_toResolved`), and fairness —
`halt_fairDeadlock`/`inf_fair` — transfers clause-by-clause. Trace equality is
`traceProbR_toResolved` (already proven). No finiteness is needed for this direction. -/

/-- Consistency is preserved by the plain→resolved coercion: a resolved run `r` is consistent with
`pe.toResolved` iff it is consistent with `pe`. Both consult the plain history — the resolved side
via `(r.take n).toExec = r.toExec.take n` (`toExec_take`), the plain side directly. -/
theorem ResolvedProbabilisticExecution.consistent_toResolved [Silent Label]
    {sys : System State Label} (pe : ProbabilisticExecution sys) (r : ResolvedExec State Label) :
    pe.toResolved.Consistent r ↔ pe.Consistent r := by
  have hstep : ∀ n : ℕ, pe.toResolved.scheduler.next (r.take n)
      = pe.scheduler.next (r.toExec.take n) := by
    intro n
    change pe.scheduler.next (ResolvedExec.toExec (r.take n)) = _
    rw [ResolvedExec.toExec_take]
  unfold ResolvedProbabilisticExecution.Consistent ProbabilisticExecution.Consistent
  simp only [hstep]
  rfl

/-- A plain-fair execution coerces to a resolved-fair one: both fairness clauses transfer through
`consistent_toResolved` (the halting emission `next r none = σ.next r.toExec none` and the
`FairStepAt`/`FairDeadlock` data are literally identical). -/
theorem ProbabilisticExecution.isFair_toResolved [Silent Label] {sys : System State Label}
    {F : Fairness sys} (pe : ProbabilisticExecution sys) (hpe : pe.IsFair F) :
    pe.toResolved.IsFair F where
  halt_fairDeadlock := fun r h hcons hnone => hpe.halt_fairDeadlock r h
    ((ResolvedProbabilisticExecution.consistent_toResolved pe r).mp hcons) hnone
  inf_fair := fun r hinf hcons N =>
    hpe.inf_fair r hinf ((ResolvedProbabilisticExecution.consistent_toResolved pe r).mp hcons) N

/-- **`⊇` direction.** Every plain-fair achievable trace distribution is resolved-fair achievable,
witnessed by the coercion `pe.toResolved` (fairness via `isFair_toResolved`, traces via
`traceProbR_toResolved`). -/
theorem fairAchievableTraceDistsPlain_subset [Silent Label] {sys : System State Label}
    (F : Fairness sys) : fairAchievableTraceDistsPlain F ⊆ fairAchievableTraceDists F := by
  rintro D ⟨pe, h_init, hfair, h_tp⟩
  exact ⟨pe.toResolved, h_init, pe.isFair_toResolved hfair,
    fun τ => (pe.traceProbR_toResolved τ).trans (h_tp τ)⟩

/-! ### The fair sets differ for infinitely-branching systems

The following is the worked separator (kept as a comment: it is a *statement about a specific
system*, not a Lean theorem, and constructing that system in Lean is a large aside).

Fix `State := ℕ ⊕ Unit` with `c_m := Sum.inl m` the corridor and `d := Sum.inr ()` a deadlock, and
`Label := ℕ` with `Silent.τ` some reserved value, say encoded so that the corridor `τ`-steps are
internal and each firing label `m` is external. Transitions:

* `init` (say `c_0`) has, for every `k : ℕ`, a transition `init −τ→ μ_k` with
  `μ_k = (1 - ε_k)·δ_{c_0} + ε_k·δ_d` and `ε_k` injective — the deadlock mass encodes `k`. (This is
  the **infinite branching**: infinitely many outgoing transitions at `init`.)
* corridor: `c_m −τ→ δ_{c_{m+1}}` marked **unfair**;
* firing: `c_m −(label m)→ δ_d` external, hence **fair**; `d` is a deadlock (fair deadlock).

Target `D` of **infinite support**: `D([k]) = p_k` for a fixed `∑_k p_k = 1` with all `p_k > 0`.

* **Resolved achieves `D` fairly.** The resolved scheduler emits `μ_k` w.p. `p_k`, reads `k` back
  from the recorded `μ_k` (via `ε_k`), silently walks `k` steps down the corridor, then fires
  `label k`. Every run fires (at its committed `k`) ⇒ `inf_fair`/`halt_fairDeadlock` hold ⇒ fair;
  trace `[k]` w.p. `p_k` ⇒ trace dist `D`. So `D ∈ fairAchievableTraceDists F`.

* **No plain scheduler achieves `D` fairly.** After `init`, a plain scheduler is on the shared `c_0`
  and has lost `k`. The corridor reveals only the *position* `m`, not the target `k`, so a plain
  scheduler decides fire-vs-continue at `c_m` from `m` alone. To be sure-fair it must kill the
  never-fire run, i.e. force firing by some finite `M` (`r_M = 1`), capping the support of its trace
  distribution to `{0,…,M}`. An infinite-support `D` is thus unreachable fairly. So
  `D ∉ fairAchievableTraceDistsPlain F`.

Hence `fairAchievableTraceDists F ≠ fairAchievableTraceDistsPlain F` in general — the model change
*does* enlarge the fair achievable set, and it does so exactly through the infinite branching at
`init`. -/

/-! The formalized counterexample lives in `Model/ResolvedGap.lean`. -/

end PLTS
