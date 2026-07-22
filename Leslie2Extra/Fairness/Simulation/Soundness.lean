/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Extra.Fairness.Simulation.Trace

/-!
# Fairness of the abstract witness, and fair-trace soundness (steps 4–5)

The fairness half of the soundness of `FairStrongProbabilisticSimulation`. Lifting a consistent
abstract witness run to a consistent coupled run and projecting to a fair `pe_C`-run, this file
builds the two fairness clauses for the abstract witness `pe_A := abstractMarginal (simJointExecR
pe_C sim)`: the halt clause `pe_A_halt_fairDeadlock` (via `sim.fair_deadlock` on the concrete fair
deadlock, no finiteness) and the infinite clause `pe_A_inf_fair` (via the well-founded descent
`descent_of_infinitely_often` and the rank clause of `sim.step`). It includes the finite-prefix
(`take`) API and the König lift `exists_infinite_coupled_lift` (the finitely-branching-tree
construction, the single point where `sys_C.ImageFinite` enters) for the infinite case, and
concludes with the main soundness theorem `fairAchievableTraceDists_subset`
(`fairAchievableTraceDists F_C ⊆ fairAchievableTraceDists F_A`).
-/

open Stream'

namespace PLTS

/-! ### Finite branching of the constructed abstract scheduler (a corollary of `ImageFinite`)

Two reusable finiteness facts and the corollary they give: under `sys_C.ImageFinite`, the abstract
scheduler `abstractMarginal (simJointExecR pe_C sim)` built by the soundness construction is
finitely branching — at every terminating history it schedules only finitely many transitions
with positive probability. This is not used by `fairAchievableTraceDists_subset`; it records, as
an explicit theorem, the finite-branching intuition behind the König lift. -/

namespace ResolvedScheduler

variable {S Label : Type} {sys : System S Label}

/-- Under image-finiteness, a resolved-history scheduler emits only finitely many transitions with
positive probability at any terminating history: its `next`-support is finite. Every emission in the
support is, by `valid`, a `sys`-step from the current end-state, of which `ImageFinite` supplies
only finitely many. -/
theorem next_support_finite (sch : ResolvedScheduler sys)
    (hfin : sys.ImageFinite) (r : ResolvedExec S Label) (hT : r.trans.Terminates) :
    (sch.next r).support.Finite := by
  classical
  have hstate : r.stateAt (Nat.find hT) = some (r.endState hT) :=
    AlterSeq.stateAt_find_eq_endState r hT
  have hterm : r.trans.TerminatedAt (Nat.find hT) := Nat.find_spec hT
  apply Set.Finite.subset
    (Set.Finite.insert none ((hfin.1 (r.endState hT)).image (fun p => some p)))
  intro x hx
  cases x with
  | none => exact Set.mem_insert _ _
  | some lμ =>
    obtain ⟨l, μ⟩ := lμ
    have hstep : sys.step (r.endState hT) l μ :=
      sch.valid r (Nat.find hT) (r.endState hT) hterm hstate l μ hx
    exact Set.mem_insert_of_mem _ ⟨(l, μ), hstep, rfl⟩

end ResolvedScheduler

namespace ResolvedProbabilisticExecution

variable {S Label : Type} {sys : System S Label}

/-- The current state of a terminating resolved history, defaulting to the initial state on the
(never-used) non-terminating branch. A namespace-local helper mirroring `simLastStateR`. -/
noncomputable def lastStateAux (r : ResolvedExec S Label) : S :=
  open Classical in if h : r.trans.Terminates then r.endState h else r.init

/-- **Positive-mass histories of a fixed length form a finite set**, under image-finiteness (with a
finite initial support). This is the finitely-branching-tree fact behind König, packaged as a
standalone finiteness statement about a single resolved execution: a length-`(k+1)` positive history
is its length-`k` positive prefix extended by one step, and the extensions are finite by
`ImageFinite` (finitely many enabled transitions, each finitely supported). -/
theorem positive_histories_finite
    (pe : ResolvedProbabilisticExecution sys) (hfin : sys.ImageFinite)
    (hinitFin : pe.initState.support.Finite) (n : ℕ) :
    {r : ResolvedExec S Label | ∃ hT : r.trans.Terminates,
       (r.trans.toList hT).length = n ∧ pe.probOfR r hT ≠ 0}.Finite := by
  classical
  induction n with
  | zero =>
    apply Set.Finite.subset (hinitFin.image (fun i => (⟨i, Seq.nil⟩ : ResolvedExec S Label)))
    rintro r ⟨hT, hlen, hpm⟩
    have htoList : r.trans.toList hT = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := r
    have h_nil : t = Seq.nil := by
      have h := Stream'.Seq.ofList_toList t hT
      rw [htoList, Stream'.Seq.ofList_nil] at h; exact h.symm
    subst h_nil
    rw [pe.probOfR_nil i] at hpm
    exact ⟨i, (PMF.mem_support_iff _ _).mpr hpm, rfl⟩
  | succ k ih =>
    have hchild : ∀ r' : ResolvedExec S Label,
        {last : (Label × PMF S) × S |
          sys.step (lastStateAux r') last.1.1 last.1.2 ∧ last.2 ∈ last.1.2.support}.Finite := by
      intro r'
      apply Set.Finite.subset
        (Set.Finite.biUnion (hfin.1 (lastStateAux r'))
          (fun p hp => (hfin.2 (lastStateAux r') p.1 p.2 hp).image (fun s' => (p, s'))))
      rintro ⟨⟨l, μ⟩, s'⟩ ⟨hstep, hs'⟩
      exact Set.mem_biUnion hstep ⟨s', hs', rfl⟩
    apply Set.Finite.subset
      (Set.Finite.biUnion ih (fun r' _ =>
        Set.Finite.image
          (fun last => (⟨r'.init, r'.trans.append (Seq.cons last Seq.nil)⟩ : ResolvedExec S Label))
          (hchild r')))
    rintro r ⟨hT, hlen, hpm⟩
    have hne : r.trans.toList hT ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last r.trans hT hne
    have happ : (prev.append (Seq.cons last Seq.nil)).Terminates := hsplit ▸ hT
    have hr_eq : r = ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩ := by
      obtain ⟨ri, rt⟩ := r; exact congrArg (AlterSeq.mk ri) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (r.trans.toList hT).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    have hcongr : pe.probOfR r hT
        = pe.probOfR ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩ happ := by
      cases r; cases hr_eq; rfl
    rw [hcongr, pe.probOfR_append_singleton r.init prev hprev last happ] at hpm
    have hpm_prev : pe.probOfR ⟨r.init, prev⟩ hprev ≠ 0 := fun h => hpm (by rw [h, zero_mul])
    have hker : pe.rkernel ⟨r.init, prev⟩ last ≠ 0 := fun h => hpm (by rw [h, mul_zero])
    have hr'mem : (⟨r.init, prev⟩ : ResolvedExec S Label) ∈
        {r : ResolvedExec S Label | ∃ hT : r.trans.Terminates,
          (r.trans.toList hT).length = k ∧ pe.probOfR r hT ≠ 0} :=
      ⟨hprev, hlen_prev, hpm_prev⟩
    obtain ⟨la, qa⟩ := last
    obtain ⟨ll, μμ⟩ := la
    have hnext_ne : pe.scheduler.next ⟨r.init, prev⟩ (some (ll, μμ)) ≠ 0 := by
      unfold ResolvedProbabilisticExecution.rkernel at hker
      exact fun h => hker (by rw [h, zero_mul])
    have hμ_ne : μμ qa ≠ 0 := by
      unfold ResolvedProbabilisticExecution.rkernel at hker
      exact fun h => hker (by rw [h, mul_zero])
    have hlast_eq : lastStateAux (⟨r.init, prev⟩ : ResolvedExec S Label)
        = (⟨r.init, prev⟩ : ResolvedExec S Label).endState hprev := by
      rw [lastStateAux, dif_pos hprev]
    have hstate : (⟨r.init, prev⟩ : ResolvedExec S Label).stateAt (Nat.find hprev)
        = some ((⟨r.init, prev⟩ : ResolvedExec S Label).endState hprev) :=
      AlterSeq.stateAt_find_eq_endState _ hprev
    have hstep : sys.step (lastStateAux (⟨r.init, prev⟩ : ResolvedExec S Label)) ll μμ := by
      rw [hlast_eq]
      exact pe.scheduler.valid ⟨r.init, prev⟩ (Nat.find hprev) _ (Nat.find_spec hprev) hstate
        ll μμ ((PMF.mem_support_iff _ _).mpr hnext_ne)
    refine Set.mem_biUnion hr'mem ⟨((ll, μμ), qa), ⟨hstep, (PMF.mem_support_iff _ _).mpr hμ_ne⟩, ?_⟩
    rw [hr_eq]

end ResolvedProbabilisticExecution

variable {State_C State_A Label : Type} [Silent Label]

namespace FairStrongProbabilisticSimulation

variable {sys_C : System State_C Label} {sys_A : System State_A Label}
  {F_C : Fairness sys_C} {F_A : Fairness sys_A} {R : State_C → State_A → Prop}

/-! ### Fairness of the abstract witness (Phase 4)

The last obligation for fair soundness is `pe_A.IsFair F_A` for `pe_A := abstractMarginal
(simJointExecR pe_C sim)`. The helper lemmas below build the two clauses (`halt_fairDeadlock`,
`inf_fair`) by lifting a consistent abstract run to a consistent coupled run and projecting to a
fair `pe_C`-run. -/

omit [Silent Label] in
/-- **Bridge:** the length-`(prev.toList).length` prefix of a resolved history whose `trans` splits
as `prev.append (cons last nil)` is exactly `⟨r.init, prev⟩`. Powers the alignment of `Consistent`'s
`r.take n` with the cons-end split of `probOfR`. -/
private theorem take_prev_of_split {S : Type}
    (r : ResolvedExec S Label)
    (prev : Seq ((Label × PMF S) × S)) (last : (Label × PMF S) × S)
    (hprev : prev.Terminates) (hsplit : r.trans = prev.append (Seq.cons last Seq.nil)) :
    r.take (prev.toList hprev).length = ⟨r.init, prev⟩ := by
  unfold AlterSeq.take
  simp only [AlterSeq.mk.injEq, true_and]
  have hkey : Stream'.Seq.take (prev.toList hprev).length r.trans = prev.toList hprev := by
    apply List.ext_getElem?
    intro k
    rw [Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_toList]
    by_cases hk : k < (prev.toList hprev).length
    · rw [if_pos hk, hsplit, Stream'.Seq.length_toList] at *
      have hnt : ¬ prev.TerminatedAt k :=
        fun ht => absurd (Stream'.Seq.length_le_iff.mpr ht) (not_le.mpr hk)
      exact Stream'.Seq.get?_append_before_length hnt
    · rw [if_neg hk, Stream'.Seq.length_toList] at *
      exact (Stream'.Seq.length_le_iff.mp (Nat.le_of_not_lt hk)).symm
  rw [hkey, Stream'.Seq.ofList_toList]

omit [Silent Label] in
/-- **Bridge:** the transition at position `(prev.toList).length` of a history that splits as
`prev.append (cons last nil)` is `last`. -/
private theorem get?_last_of_split {S : Type}
    (r : ResolvedExec S Label)
    (prev : Seq ((Label × PMF S) × S)) (last : (Label × PMF S) × S)
    (hprev : prev.Terminates) (hsplit : r.trans = prev.append (Seq.cons last Seq.nil)) :
    r.trans.get? (prev.toList hprev).length = some last := by
  rw [hsplit]
  have hlen : (prev.toList hprev).length = Nat.find hprev := Stream'.Seq.length_toList prev hprev
  rw [hlen]
  have := Stream'.Seq.get?_append_find hprev (Seq.cons last Seq.nil) 0
  rw [Nat.add_zero] at this
  rw [this]; rfl

omit [Silent Label] in
/-- **Helper 1.** A run consistent with a resolved probabilistic execution has positive path mass:
`pe.Consistent r → pe.probOfR r hT ≠ 0`. Cons-end induction; each appended factor is nonzero from
the `Consistent` witness read at the corresponding position. -/
theorem consistent_imp_probOfR_ne_zero {S : Type} {sys : System S Label}
    (pe : ResolvedProbabilisticExecution sys) (r : ResolvedExec S Label)
    (hcons : pe.Consistent r) (hT : r.trans.Terminates) :
    pe.probOfR r hT ≠ 0 := by
  suffices H : ∀ n (r : ResolvedExec S Label) (hcons : pe.Consistent r)
      (hT : r.trans.Terminates), (r.trans.toList hT).length = n → pe.probOfR r hT ≠ 0 from
    H _ r hcons hT rfl
  intro n
  induction n with
  | zero =>
    intro r hcons hT hlen
    have htoList : r.trans.toList hT = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := r
    have h_nil : t = Seq.nil := by
      have h := Stream'.Seq.ofList_toList t hT
      rw [htoList, Stream'.Seq.ofList_nil] at h
      exact h.symm
    subst h_nil
    rw [pe.probOfR_nil i]
    exact hcons.1
  | succ k ih =>
    intro r hcons hT hlen
    have hne : r.trans.toList hT ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last r.trans hT hne
    have happ : (prev.append (Seq.cons last Seq.nil)).Terminates := hsplit ▸ hT
    have hr_eq : r = ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩ := by
      obtain ⟨ri, rt⟩ := r; exact congrArg (AlterSeq.mk ri) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (r.trans.toList hT).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    -- Consistency of the shorter prefix `⟨r.init, prev⟩`.
    have hcons_prev : pe.Consistent ⟨r.init, prev⟩ := by
      refine ⟨hcons.1, ?_⟩
      intro m l μ s' hget
      -- The `m`-th transition of `prev` is the `m`-th transition of `r` (before the append).
      have hntm : ¬ prev.TerminatedAt m := by
        intro htm; rw [Stream'.Seq.TerminatedAt] at htm; rw [htm] at hget
        exact absurd hget (by simp)
      have hgetr : r.trans.get? m = some ((l, μ), s') := by
        rw [hsplit]; rw [Stream'.Seq.get?_append_before_length hntm]; exact hget
      obtain ⟨hnext, hμ⟩ := hcons.2 m l μ s' hgetr
      refine ⟨?_, hμ⟩
      -- `r.take m = ⟨r.init, prev⟩.take m` since they agree on the first `prev`-worth of
      -- transitions.
      have htake_eq : r.take m = (⟨r.init, prev⟩ : ResolvedExec S Label).take m := by
        unfold AlterSeq.take
        simp only [AlterSeq.mk.injEq, true_and]
        congr 1
        apply List.ext_getElem?
        intro j
        rw [Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_take]
        by_cases hj : j < m
        · rw [if_pos hj, if_pos hj, hsplit]
          have hntj : ¬ prev.TerminatedAt j :=
            fun ht => hntm (Stream'.Seq.terminated_stable prev (Nat.le_of_lt hj) ht)
          exact Stream'.Seq.get?_append_before_length hntj
        · rw [if_neg hj, if_neg hj]
      rw [htake_eq] at hnext
      exact hnext
    -- Factor the path mass at the append and combine with the last-step factor.
    have hcongr : pe.probOfR r hT
        = pe.probOfR ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩ happ := by
      cases r; cases hr_eq; rfl
    rw [hcongr, pe.probOfR_append_singleton r.init prev hprev last happ]
    -- The last factor `rkernel ⟨r.init, prev⟩ last` is nonzero by `Consistent` at position `k`.
    have hgetlast : r.trans.get? (prev.toList hprev).length = some last :=
      get?_last_of_split r prev last hprev hsplit
    obtain ⟨la, qa⟩ := last
    obtain ⟨ll, μμ⟩ := la
    obtain ⟨hnextl, hμl⟩ := hcons.2 (prev.toList hprev).length ll μμ qa hgetlast
    have htake_prev : r.take (prev.toList hprev).length = ⟨r.init, prev⟩ :=
      take_prev_of_split r prev ((ll, μμ), qa) hprev hsplit
    rw [htake_prev] at hnextl
    have hker_ne : pe.rkernel ⟨r.init, prev⟩ ((ll, μμ), qa) ≠ 0 := by
      unfold ResolvedProbabilisticExecution.rkernel
      exact mul_ne_zero hnextl hμl
    exact mul_ne_zero (ih ⟨r.init, prev⟩ hcons_prev hprev hlen_prev) hker_ne

omit [Silent Label] in
/-- **Converse of helper 1.** A run with positive path mass is consistent: `pe.probOfR r hT ≠ 0 →
pe.Consistent r`. Cons-end induction; positivity of the whole product gives positivity of each
factor, i.e. the initial mass and every recorded emission/successor weight. -/
theorem probOfR_ne_zero_imp_consistent {S : Type} {sys : System S Label}
    (pe : ResolvedProbabilisticExecution sys) (r : ResolvedExec S Label)
    (hT : r.trans.Terminates) (hpm : pe.probOfR r hT ≠ 0) :
    pe.Consistent r := by
  suffices H : ∀ n (r : ResolvedExec S Label) (hT : r.trans.Terminates),
      (r.trans.toList hT).length = n → pe.probOfR r hT ≠ 0 → pe.Consistent r from
    H _ r hT rfl hpm
  intro n
  induction n with
  | zero =>
    intro r hT hlen hpm
    have htoList : r.trans.toList hT = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := r
    have h_nil : t = Seq.nil := by
      have h := Stream'.Seq.ofList_toList t hT
      rw [htoList, Stream'.Seq.ofList_nil] at h
      exact h.symm
    subst h_nil
    refine ⟨?_, ?_⟩
    · rw [pe.probOfR_nil i] at hpm; exact hpm
    · intro m l μ s' hget
      change (Seq.nil : Seq ((Label × PMF S) × S)).get? m = _ at hget
      rw [Stream'.Seq.get?_nil] at hget
      exact absurd hget (by simp)
  | succ k ih =>
    intro r hT hlen hpm
    have hne : r.trans.toList hT ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last r.trans hT hne
    have happ : (prev.append (Seq.cons last Seq.nil)).Terminates := hsplit ▸ hT
    have hr_eq : r = ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩ := by
      obtain ⟨ri, rt⟩ := r; exact congrArg (AlterSeq.mk ri) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (r.trans.toList hT).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    -- Factor the path mass: both factors are nonzero.
    have hcongr : pe.probOfR r hT
        = pe.probOfR ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩ happ := by
      cases r; cases hr_eq; rfl
    rw [hcongr, pe.probOfR_append_singleton r.init prev hprev last happ] at hpm
    have hpm_prev : pe.probOfR ⟨r.init, prev⟩ hprev ≠ 0 := fun h => hpm (by rw [h, zero_mul])
    have hker : pe.rkernel ⟨r.init, prev⟩ last ≠ 0 := fun h => hpm (by rw [h, mul_zero])
    have hcons_prev : pe.Consistent ⟨r.init, prev⟩ := ih ⟨r.init, prev⟩ hprev hlen_prev hpm_prev
    -- Consistency of `r`: init from the prefix; steps from the prefix (before `k`) or `hker`
    -- (at `k`).
    refine ⟨hcons_prev.1, ?_⟩
    intro m l μ s' hget
    by_cases hmk : m < (prev.toList hprev).length
    · -- `m`-th step is inside `prev`; reuse the prefix consistency + take-alignment.
      have hntm : ¬ prev.TerminatedAt m := by
        rw [Stream'.Seq.length_toList] at hmk
        exact fun ht => absurd (Stream'.Seq.length_le_iff.mpr ht) (not_le.mpr hmk)
      have hgetprev : prev.get? m = some ((l, μ), s') := by
        rw [hsplit] at hget; rwa [Stream'.Seq.get?_append_before_length hntm] at hget
      obtain ⟨hnext, hμ⟩ := hcons_prev.2 m l μ s' hgetprev
      refine ⟨?_, hμ⟩
      have htake_eq : r.take m = (⟨r.init, prev⟩ : ResolvedExec S Label).take m := by
        unfold AlterSeq.take
        simp only [AlterSeq.mk.injEq, true_and]
        congr 1
        apply List.ext_getElem?
        intro j
        rw [Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_take]
        by_cases hj : j < m
        · rw [if_pos hj, if_pos hj, hsplit]
          have hntj : ¬ prev.TerminatedAt j :=
            fun ht => hntm (Stream'.Seq.terminated_stable prev (Nat.le_of_lt hj) ht)
          exact Stream'.Seq.get?_append_before_length hntj
        · rw [if_neg hj, if_neg hj]
      rw [htake_eq]; exact hnext
    · -- `m` is the last position `k`; the recorded step is `last`, positivity from `hker`.
      have hmk' : (prev.toList hprev).length ≤ m := Nat.le_of_not_lt hmk
      -- positions beyond `k` are terminated, so `m = k`.
      have hget_last : r.trans.get? (prev.toList hprev).length = some last :=
        get?_last_of_split r prev last hprev hsplit
      -- `r.trans` terminates one past `prev`, so any `m` with a recorded step is at most `k`.
      have hlenk : (prev.toList hprev).length = Nat.find hprev :=
        Stream'.Seq.length_toList prev hprev
      have hterm1 : r.trans.TerminatedAt ((prev.toList hprev).length + 1) := by
        rw [hsplit, hlenk]
        exact Stream'.Seq.terminatedAt_append_find hprev
          (show (Seq.cons last Seq.nil).TerminatedAt 1 from rfl)
      have hntm : ¬ r.trans.TerminatedAt m := by
        intro ht
        rw [Stream'.Seq.TerminatedAt, hget] at ht
        exact absurd ht (by simp)
      have hm_le : m ≤ (prev.toList hprev).length := by
        by_contra hlt
        exact hntm (Stream'.Seq.terminated_stable r.trans (Nat.succ_le_of_lt (Nat.lt_of_not_le hlt))
          hterm1)
      have hmeq : m = (prev.toList hprev).length := Nat.le_antisymm hm_le hmk'
      subst hmeq
      rw [hget_last] at hget
      obtain rfl : last = ((l, μ), s') := Option.some.inj hget
      have htake_prev : r.take (prev.toList hprev).length = ⟨r.init, prev⟩ :=
        take_prev_of_split r prev ((l, μ), s') hprev hsplit
      rw [htake_prev]
      unfold ResolvedProbabilisticExecution.rkernel at hker
      exact ⟨fun h => hker (by rw [h, zero_mul]), fun h => hker (by rw [h, mul_zero])⟩

/-- `Seq.take n s` reads back `s.get?` below `n`. -/
private theorem seq_getElem?_take {α : Type} (s : Seq α) (n m : ℕ) (h : m < n) :
    (Seq.take n s)[m]? = s.get? m := by
  induction n generalizing s m with
  | zero => omega
  | succ k ih =>
    induction s using Stream'.Seq.recOn with
    | nil => simp [Stream'.Seq.take_nil, Stream'.Seq.get?_nil]
    | cons a t =>
      rw [Stream'.Seq.take_succ_cons]
      cases m with
      | zero => simp [Stream'.Seq.get?_cons_zero]
      | succ j =>
        rw [List.getElem?_cons_succ, Stream'.Seq.get?_cons_succ]
        exact ih t j (Nat.lt_of_succ_lt_succ h)

omit [Silent Label] in
/-- **Helper 2.** `concreteProjR` commutes with the finite prefix `AlterSeq.take` (mirror of
`ResolvedExec.toExec_take`). -/
theorem concreteProjR_take (r : ResolvedExec (State_C × State_A) Label) (n : ℕ) :
    concreteProjR (r.take n) = (concreteProjR r).take n := by
  unfold concreteProjR AlterSeq.take
  simp only [AlterSeq.mk.injEq, true_and]
  apply Stream'.Seq.ext
  intro k
  rw [Stream'.Seq.map_get?, Stream'.Seq.ofList_get?, Stream'.Seq.ofList_get?,
    Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_take]
  by_cases hk : k < n
  · rw [if_pos hk, if_pos hk, Stream'.Seq.map_get?]
  · rw [if_neg hk, if_neg hk, Option.map_none]

omit [Silent Label] in
/-- `absProjR` commutes with the finite prefix `AlterSeq.take` (abstract analogue of
`concreteProjR_take`). -/
theorem absProjR_take (r : ResolvedExec (State_C × State_A) Label) (n : ℕ) :
    absProjR (r.take n) = (absProjR r).take n := by
  unfold absProjR AlterSeq.take
  simp only [AlterSeq.mk.injEq, true_and]
  apply Stream'.Seq.ext
  intro k
  rw [Stream'.Seq.map_get?, Stream'.Seq.ofList_get?, Stream'.Seq.ofList_get?,
    Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_take]
  by_cases hk : k < n
  · rw [if_pos hk, if_pos hk, Stream'.Seq.map_get?]
  · rw [if_neg hk, if_neg hk, Option.map_none]

omit [Silent Label] in
/-- Nested prefixes collapse: `(r.take n).take m = r.take (min m n)`. In particular for `m ≤ n` it
is `r.take m`. -/
theorem take_take {S : Type} (r : ResolvedExec S Label) (n m : ℕ) (hmn : m ≤ n) :
    (r.take n).take m = r.take m := by
  unfold AlterSeq.take
  simp only [AlterSeq.mk.injEq, true_and]
  congr 1
  apply List.ext_getElem?
  intro j
  rw [Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_take]
  by_cases hj : j < m
  · rw [if_pos hj, if_pos hj, Stream'.Seq.ofList_get?, seq_getElem?_take r.trans n j
      (Nat.lt_of_lt_of_le hj hmn)]
  · rw [if_neg hj, if_neg hj]

omit [Silent Label] in
/-- **Helper 4a.** The concrete projection's end-state is the `Prod.fst` of the product
end-state. -/
theorem concreteProjR_endState (r : ResolvedExec (State_C × State_A) Label)
    (hT : r.trans.Terminates) (hTC : (concreteProjR r).trans.Terminates) :
    (concreteProjR r).endState hTC = (r.endState hT).1 := by
  have hfind : Nat.find hTC = Nat.find hT := by
    apply Nat.find_congr'
    intro n
    exact concreteProjR_terminatedAt_iff r n
  have h1 := AlterSeq.stateAt_find_eq_endState (concreteProjR r) hTC
  have h2 := AlterSeq.stateAt_find_eq_endState r hT
  rw [concreteProjR_stateAt r (Nat.find hTC), hfind, h2] at h1
  simp only [Option.map_some] at h1
  exact Option.some.inj h1.symm

omit [Silent Label] in
/-- **Helper 4b.** The abstract projection's end-state is the `Prod.snd` of the product
end-state. -/
theorem absProjR_endState (r : ResolvedExec (State_C × State_A) Label)
    (hT : r.trans.Terminates) (hTA : (absProjR r).trans.Terminates) :
    (absProjR r).endState hTA = (r.endState hT).2 := by
  have hfind : Nat.find hTA = Nat.find hT := by
    apply Nat.find_congr'
    intro n
    exact absProjR_terminatedAt_iff r n
  have h1 := AlterSeq.stateAt_find_eq_endState (absProjR r) hTA
  have h2 := AlterSeq.stateAt_find_eq_endState r hT
  rw [absProjR_stateAt r (Nat.find hTA), hfind, h2] at h1
  simp only [Option.map_some] at h1
  exact Option.some.inj h1.symm

/-- **Support extraction (strengthened).** If `some (l, ω)` lies in the support of
`(simJointSchedR pe_C sim).next r`, then the recorded coupling `ω` is `simCoupleF` over a concrete
`μ_C` that lies in the support of `pe_C`'s emission at `concreteProjR r`; in particular
`ω.map Prod.fst = μ_C`. Strengthens `simJointSchedR_next_support` by exposing the underlying
`pe_C.scheduler.next` fact needed to reflect consistency to the concrete projection. -/
theorem simJointSchedR_next_support_concrete
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (r : ResolvedExec (State_C × State_A) Label) (l : Label) (ω : PMF (State_C × State_A))
    (h_supp : some (l, ω) ∈ ((simJointSchedR pe_C sim).next r).support) :
    ∃ μ_C, pe_C.scheduler.next (concreteProjR r) (some (l, μ_C)) ≠ 0 ∧
      R (simLastStateR r).1 (simLastStateR r).2 ∧
      sys_C.step (simLastStateR r).1 l μ_C ∧
      ω.map Prod.fst = μ_C := by
  classical
  change some (l, ω) ∈ ((pe_C.scheduler.next (concreteProjR r)).bind (fun o =>
    match o with
    | none => PMF.pure none
    | some (l', μ_C) =>
      if h : R (simLastStateR r).1 (simLastStateR r).2 ∧
          sys_C.step (simLastStateR r).1 l' μ_C then
        PMF.pure (some (l', simCoupleF sim (simLastStateR r) l' μ_C))
      else PMF.pure none)).support at h_supp
  rw [PMF.mem_support_bind_iff] at h_supp
  obtain ⟨o, ho_supp, h_supp⟩ := h_supp
  cases o with
  | none =>
    rw [PMF.mem_support_pure_iff] at h_supp
    exact absurd h_supp.symm (by simp)
  | some lμ =>
    obtain ⟨l', μ_C⟩ := lμ
    simp only at h_supp
    by_cases hg : R (simLastStateR r).1 (simLastStateR r).2 ∧
        sys_C.step (simLastStateR r).1 l' μ_C
    · rw [dif_pos hg, PMF.mem_support_pure_iff] at h_supp
      rw [Option.some.injEq, Prod.mk.injEq] at h_supp
      obtain ⟨rfl, rfl⟩ := h_supp
      refine ⟨μ_C, (PMF.mem_support_iff _ _).mp ho_supp, hg.1, hg.2, ?_⟩
      exact simCoupleF_map_fst sim (simLastStateR r) l μ_C hg
    · rw [dif_neg hg, PMF.mem_support_pure_iff] at h_supp
      exact absurd h_supp (by simp)

/-- **Helper 3.** The concrete projection of a `simJointExecR`-consistent coupled run is a
`pe_C`-consistent concrete run. Initial mass from `Consistent`'s init clause (the joint init is
`(sys_C.init, sys_A.init)`, whose concrete projection is `sys_C.init`); each step from the
strengthened support extraction (`pe_C`'s emission is positive on `ω.map Prod.fst`) and the
coupling marginal `(ω.map Prod.fst) s'_C ≥ ω (s'_C, s'_A) > 0`. -/
theorem concreteProjR_consistent
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (h_init : pe_C.initState = PMF.pure sys_C.init)
    (r_J : ResolvedExec (State_C × State_A) Label)
    (hcons : (simJointExecR pe_C sim).Consistent r_J) :
    pe_C.Consistent (concreteProjR r_J) := by
  classical
  refine ⟨?_, ?_⟩
  · -- Initial mass.
    have hinitJ : (simJointExecR pe_C sim).initState r_J.init ≠ 0 := hcons.1
    change (PMF.pure (simProd sys_C sys_A R).init) r_J.init ≠ 0 at hinitJ
    rw [PMF.pure_apply] at hinitJ
    have hinit_eq : r_J.init = (simProd sys_C sys_A R).init := by
      by_contra hc; rw [if_neg hc] at hinitJ; exact hinitJ rfl
    change pe_C.initState (concreteProjR r_J).init ≠ 0
    rw [show (concreteProjR r_J).init = r_J.init.1 from rfl, hinit_eq, h_init]
    rw [PMF.pure_apply, if_pos (show (simProd sys_C sys_A R).init.1 = sys_C.init from rfl)]
    exact one_ne_zero
  · -- Step consistency.
    intro n l μ_C s'_C hget
    -- `(concreteProjR r_J).trans.get? n = some ((l, μ_C), s'_C)` unpicks a product transition.
    have hgetJ : ∃ ω s'_A,
        r_J.trans.get? n = some ((l, ω), (s'_C, s'_A)) ∧ ω.map Prod.fst = μ_C := by
      have hmap : (r_J.trans.map (fun p => ((p.1.1, p.1.2.map Prod.fst), p.2.1))).get? n
          = some ((l, μ_C), s'_C) := hget
      rw [Stream'.Seq.map_get?] at hmap
      cases hc : r_J.trans.get? n with
      | none => rw [hc] at hmap; simp at hmap
      | some p =>
        rw [hc] at hmap
        simp only [Option.map_some, Option.some.injEq] at hmap
        obtain ⟨⟨lp, ωp⟩, s'p, s'ap⟩ := p
        simp only [Prod.mk.injEq] at hmap
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hmap
        exact ⟨ωp, s'ap, rfl, rfl⟩
    obtain ⟨ω, s'_A, hgetω, hμeq⟩ := hgetJ
    obtain ⟨hnextJ, hωq⟩ := hcons.2 n l ω (s'_C, s'_A) hgetω
    -- Extract the `pe_C`-emission from the coupled scheduler.
    obtain ⟨μ_C', hnextC, _, _, hfstμ⟩ :=
      simJointSchedR_next_support_concrete pe_C sim (r_J.take n) l ω
        ((PMF.mem_support_iff _ _).mpr hnextJ)
    -- `μ_C = ω.map fst = μ_C'`, and the concrete prefix of the projection is the projection of the
    -- prefix (helper 2).
    have hμC : μ_C = μ_C' := by rw [← hμeq, hfstμ]
    subst hμC
    rw [← concreteProjR_take r_J n]
    refine ⟨hnextC, ?_⟩
    -- `(ω.map fst) s'_C ≥ ω (s'_C, s'_A) ≠ 0`.
    rw [← hμeq]
    rw [PMF.map_apply]
    intro htsum
    exact hωq (by
      have := ENNReal.tsum_eq_zero.mp htsum (s'_C, s'_A)
      simpa using this)

omit [Silent Label] in
/-- The abstract marginal's halt-emission (in the positive-belief branch): the posterior-weighted
mixture of the coupled halt-emissions over the `absProjR`-fibre, normalised by the belief weight.
The `none`-analogue of `abstractMarginal_next_some`; the pushforward `mapEmit Prod.snd` maps `none`
to `none`, so the emission weight is the coupled halt-emission `next r.1 none`. -/
theorem abstractMarginal_next_none
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (r_A : ResolvedExec State_A Label) (hT : r_A.trans.Terminates)
    (hW : absWeight peJ r_A hT ≠ 0) :
    (abstractMarginal peJ).scheduler.next r_A none
      = (∑' r : {r : ResolvedExec (State_C × State_A) Label // absProjR r = r_A},
            peJ.probOfR r.1 (terminates_of_absProjR_eq hT r.2)
              * peJ.scheduler.next r.1 none)
          * (absWeight peJ r_A hT)⁻¹ := by
  classical
  change (if hT' : r_A.trans.Terminates then _ else PMF.pure none) none = _
  rw [dif_pos hT, dif_pos hW, PMF.normalize_apply, absWeight_eq_tsum peJ r_A hT]
  congr 1
  refine tsum_congr (fun r => ?_)
  congr 1
  -- `((next r.1).map (mapEmit snd)) none = next r.1 none`.
  rw [mapEmit, PMF.map_apply]
  rw [tsum_eq_single none ?_]
  · simp
  · intro o ho
    cases o with
    | none => exact absurd rfl ho
    | some lμ => simp

omit [Silent Label] in
/-- On a terminating product history, `simLastStateR` is the end-state. -/
theorem simLastStateR_eq_endState (r : ResolvedExec (State_C × State_A) Label)
    (hT : r.trans.Terminates) : simLastStateR r = r.endState hT := by
  rw [simLastStateR, dif_pos hT]

/-- **Halt transfer.** If the coupled scheduler halts on a `simJointExecR`-consistent history with
positive path mass, then `pe_C` halts on its concrete projection. The coupled halt-emission
`simJointSchedR.next r none` is the `pe_C` halt-emission plus the guard-false emission terms; on a
consistent, `R`-related run the guard holds for every emission in `pe_C`'s support (R from the
R-invariant, `sys_C.step` from `pe_C`-validity), so the guard-false terms vanish. -/
theorem simJointSchedR_next_none_halt_transfer
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (r : ResolvedExec (State_C × State_A) Label) (hT : r.trans.Terminates)
    (hR : R (simLastStateR r).1 (simLastStateR r).2)
    (hhalt : (simJointExecR pe_C sim).scheduler.next r none ≠ 0) :
    pe_C.scheduler.next (concreteProjR r) none ≠ 0 := by
  classical
  -- Read `simLastStateR r` as the end-state; get the current concrete state for validity.
  have hTC : (concreteProjR r).trans.Terminates := (concreteProjR_terminates_iff r).mpr hT
  have hstate : (concreteProjR r).stateAt (Nat.find hTC) = some (simLastStateR r).1 := by
    rw [AlterSeq.stateAt_find_eq_endState (concreteProjR r) hTC,
      concreteProjR_endState r hT hTC, simLastStateR_eq_endState r hT]
  have hterm : (concreteProjR r).trans.TerminatedAt (Nat.find hTC) := Nat.find_spec hTC
  -- The guard holds for every `(l', μ_C)` in `pe_C`'s emission support at `concreteProjR r`.
  have hguard : ∀ l' μ_C, pe_C.scheduler.next (concreteProjR r) (some (l', μ_C)) ≠ 0 →
      R (simLastStateR r).1 (simLastStateR r).2 ∧ sys_C.step (simLastStateR r).1 l' μ_C := by
    intro l' μ_C hne
    refine ⟨hR, ?_⟩
    exact pe_C.scheduler.valid (concreteProjR r) (Nat.find hTC) (simLastStateR r).1 hterm hstate
      l' μ_C ((PMF.mem_support_iff _ _).mpr hne)
  -- Expand `next r none` over the bind: only `o = none` and guard-false `some` reach `none`.
  change ((pe_C.scheduler.next (concreteProjR r)).bind (fun o =>
    match o with
    | none => PMF.pure none
    | some (l', μ_C) =>
      if h : R (simLastStateR r).1 (simLastStateR r).2 ∧
          sys_C.step (simLastStateR r).1 l' μ_C then
        PMF.pure (some (l', simCoupleF sim (simLastStateR r) l' μ_C))
      else PMF.pure none)) none ≠ 0 at hhalt
  rw [PMF.bind_apply] at hhalt
  -- Every summand except `o = none` vanishes: guard-false `some` terms have `pe_C.next = 0`.
  rw [tsum_eq_single none ?_] at hhalt
  · -- surviving term: `pe_C.next (concreteProjR r) none * (pure none) none = pe_C.next .. none`.
    intro h0
    apply hhalt
    rw [h0]
    simp
  · intro o ho
    cases o with
    | none => exact absurd rfl ho
    | some lμ =>
      obtain ⟨l', μ_C⟩ := lμ
      by_cases hne : pe_C.scheduler.next (concreteProjR r) (some (l', μ_C)) = 0
      · rw [hne, zero_mul]
      · -- guard holds ⟹ the emission puts no mass on `none`.
        obtain ⟨_, hstep⟩ := hguard l' μ_C hne
        have hg : R (simLastStateR r).1 (simLastStateR r).2 ∧
            sys_C.step (simLastStateR r).1 l' μ_C := ⟨hR, hstep⟩
        change pe_C.scheduler.next (concreteProjR r) (some (l', μ_C))
            * ((if h : R (simLastStateR r).1 (simLastStateR r).2 ∧
                  sys_C.step (simLastStateR r).1 l' μ_C then
                PMF.pure (some (l', simCoupleF sim (simLastStateR r) l' μ_C))
              else PMF.pure none) none) = 0
        rw [dif_pos hg, PMF.pure_apply, if_neg (by simp), mul_zero]

/-- **Halt case.** A halting consistent abstract witness run ends at a fair `F_A`-deadlock. From
consistency the belief weight is positive, so the abstract halt-emission decomposes over the coupled
fibre; a positive fibre element gives a coupled run that halts (`simJointSchedR.next _ none ≠ 0`),
whose concrete projection is `pe_C`-consistent and halts, hence ends at a fair `F_C`-deadlock (by
`hfair_C`); its `R`-image is a fair `F_A`-deadlock (by `sim.fair_deadlock`). -/
theorem pe_A_halt_fairDeadlock
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (h_init : pe_C.initState = PMF.pure sys_C.init) (hfair_C : pe_C.IsFair F_C)
    (r_A : ResolvedExec State_A Label) (hT : r_A.trans.Terminates)
    (hcons : (abstractMarginal (simJointExecR pe_C sim)).Consistent r_A)
    (hnone : (abstractMarginal (simJointExecR pe_C sim)).scheduler.next r_A none ≠ 0) :
    F_A.FairDeadlock (r_A.endState hT) := by
  classical
  set peJ := simJointExecR pe_C sim with hpeJ
  -- Consistency ⟹ positive path mass ⟹ positive belief weight.
  have hpm : (abstractMarginal peJ).probOfR r_A hT ≠ 0 :=
    consistent_imp_probOfR_ne_zero (abstractMarginal peJ) r_A hcons hT
  rw [abstractMarginal_probOfR peJ r_A hT] at hpm
  -- Decompose the halt-emission over the coupled fibre.
  rw [abstractMarginal_next_none peJ r_A hT hpm] at hnone
  have hnum : (∑' r : {r : ResolvedExec (State_C × State_A) Label // absProjR r = r_A},
      peJ.probOfR r.1 (terminates_of_absProjR_eq hT r.2) * peJ.scheduler.next r.1 none) ≠ 0 :=
    (mul_ne_zero_iff.mp hnone).1
  obtain ⟨r_J, hrJ⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hnum)
  have hprobJ : peJ.probOfR r_J.1 (terminates_of_absProjR_eq hT r_J.2) ≠ 0 :=
    fun h => hrJ (by rw [h, zero_mul])
  have hhaltJ : peJ.scheduler.next r_J.1 none ≠ 0 := fun h => hrJ (by rw [h, mul_zero])
  have hTJ : r_J.1.trans.Terminates := terminates_of_absProjR_eq hT r_J.2
  -- `r_J` is `peJ`-consistent (positive path mass ⟹ consistent, the converse of helper 1).
  have hconsJ : peJ.Consistent r_J.1 :=
    probOfR_ne_zero_imp_consistent peJ r_J.1 hTJ hprobJ
  -- R at the coupled end (for the halt transfer's guard).
  have hRend : R (r_J.1.endState hTJ).1 (r_J.1.endState hTJ).2 :=
    simJointExecR_probOfR_R pe_C sim r_J.1 hTJ hprobJ
  have hRlast : R (simLastStateR r_J.1).1 (simLastStateR r_J.1).2 := by
    rw [simLastStateR_eq_endState r_J.1 hTJ]; exact hRend
  -- Halt transfer: the coupled halt-emission forces `pe_C` to halt on the concrete projection.
  have hnoneC : pe_C.scheduler.next (concreteProjR r_J.1) none ≠ 0 :=
    simJointSchedR_next_none_halt_transfer pe_C sim r_J.1 hTJ hRlast hhaltJ
  -- `pe_C`-fairness: the concrete projection halts at a fair `F_C`-deadlock.
  have hTC : (concreteProjR r_J.1).trans.Terminates :=
    (concreteProjR_terminates_iff r_J.1).mpr hTJ
  have hconsC : pe_C.Consistent (concreteProjR r_J.1) :=
    concreteProjR_consistent pe_C sim h_init r_J.1 hconsJ
  have hfd_C : F_C.FairDeadlock ((concreteProjR r_J.1).endState hTC) :=
    hfair_C.halt_fairDeadlock (concreteProjR r_J.1) hTC hconsC hnoneC
  rw [concreteProjR_endState r_J.1 hTJ hTC] at hfd_C
  -- R-invariant + `sim.fair_deadlock` transfer the fair deadlock to the abstract end.
  have hfd_A : F_A.FairDeadlock (r_J.1.endState hTJ).2 :=
    sim.fair_deadlock (r_J.1.endState hTJ).1 (r_J.1.endState hTJ).2 hRend hfd_C
  -- `(r_J.endState).2 = r_A.endState` via `absProjR r_J = r_A`.
  have hTA : (absProjR r_J.1).trans.Terminates := by rw [r_J.2]; exact hT
  have hend_eq : (r_J.1.endState hTJ).2 = r_A.endState hT := by
    rw [← absProjR_endState r_J.1 hTJ hTA]
    exact AlterSeq.endState_congr_pub r_J.2 hTA hT
  rw [hend_eq] at hfd_A
  exact hfd_A

/-! ### Finite-prefix (`take`) API for the infinite case

Generic facts about `AlterSeq.take` on an infinite resolved history (mirrors the private
`take_*` helpers of `Model/ResolvedGap.lean`), needed to read `r_J`'s recorded transitions,
end-states, and consistency at each finite prefix along the König lift. -/

omit [Silent Label] in
/-- The finite prefix `r.take n` records the same transitions as `r` below `n`. -/
private theorem take_trans_get? {S : Type} (r : ResolvedExec S Label) {n m : ℕ} (h : m < n) :
    (r.take n).trans.get? m = r.trans.get? m := by
  change (Seq.ofList (Seq.take n r.trans)).get? m = _
  rw [Stream'.Seq.ofList_get?, seq_getElem?_take r.trans n m h]

omit [Silent Label] in
/-- The length-`n` prefix always terminates (it is a finite list). -/
private theorem take_terminates {S : Type} (r : ResolvedExec S Label) (n : ℕ) :
    (r.take n).trans.Terminates :=
  Stream'.Seq.terminates_ofList _

omit [Silent Label] in
/-- For an infinite `r`, the length-`n` prefix terminates exactly at `n`. -/
private theorem take_terminatedAt {S : Type} (r : ResolvedExec S Label) (n : ℕ)
    (hinf : ¬ r.trans.Terminates) : (r.take n).trans.TerminatedAt n := by
  change (Seq.ofList (Seq.take n r.trans)).get? n = none
  rw [Stream'.Seq.ofList_get?]
  apply List.getElem?_eq_none
  have hlen : (Seq.take n r.trans).length = n :=
    Stream'.Seq.length_take_of_le_length (fun h => absurd h hinf)
  omega

omit [Silent Label] in
/-- For an infinite `r`, the canonical terminating index of `r.take n` is `n`. -/
private theorem take_find {S : Type} (r : ResolvedExec S Label) (n : ℕ)
    (hinf : ¬ r.trans.Terminates) : Nat.find (take_terminates r n) = n := by
  apply le_antisymm
  · exact Nat.find_le (take_terminatedAt r n hinf)
  · rw [Nat.le_find_iff]
    intro m hm
    change ¬ (Seq.ofList (Seq.take n r.trans)).get? m = none
    rw [Stream'.Seq.ofList_get?, seq_getElem?_take r.trans n m hm]
    exact fun hc => hinf ⟨m, hc⟩

omit [Silent Label] in
/-- `r.take n` reads the same state as `r` at positions `≤ n`. -/
private theorem take_stateAt {S : Type} (r : ResolvedExec S Label) {n m : ℕ} (hm : m ≤ n) :
    (r.take n).stateAt m = r.stateAt m := by
  cases m with
  | zero => rfl
  | succ k =>
    change ((r.take n).trans.get? k).map Prod.snd = (r.trans.get? k).map Prod.snd
    rw [take_trans_get? r (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hm)]

omit [Silent Label] in
/-- For an infinite `r`, the end-state of the length-`n` prefix is `r.stateAt n`. -/
private theorem take_endState {S : Type} (r : ResolvedExec S Label) (n : ℕ)
    (hinf : ¬ r.trans.Terminates) {s : S} (hs : r.stateAt n = some s) :
    (r.take n).endState (take_terminates r n) = s := by
  have hfind := take_find r n hinf
  have heq := AlterSeq.stateAt_find_eq_endState (r.take n) (take_terminates r n)
  rw [hfind, take_stateAt r (Nat.le_refl n), hs] at heq
  exact (Option.some.inj heq).symm

omit [Silent Label] in
/-- **Consistency restricts to prefixes.** If `r` is `pe`-consistent, so is every finite prefix
`r.take n`. -/
private theorem consistent_take {S : Type} {sys : System S Label}
    (pe : ResolvedProbabilisticExecution sys) (r : ResolvedExec S Label)
    (hcons : pe.Consistent r) (n : ℕ) : pe.Consistent (r.take n) := by
  refine ⟨hcons.1, ?_⟩
  intro m l μ s' hget
  -- The recorded transition of `r.take n` at `m` requires `m < n` (else it is `none`).
  have hmn : m < n := by
    by_contra hc
    have : (r.take n).trans.get? m = none := by
      change (Seq.ofList (Seq.take n r.trans)).get? m = none
      rw [Stream'.Seq.ofList_get?]
      apply List.getElem?_eq_none
      exact Nat.le_trans (Stream'.Seq.length_take_le) (Nat.le_of_not_lt hc)
    rw [this] at hget; exact absurd hget (by simp)
  rw [take_trans_get? r hmn] at hget
  obtain ⟨hnext, hμ⟩ := hcons.2 m l μ s' hget
  refine ⟨?_, hμ⟩
  -- `(r.take n).take m = r.take m` since `m < n`.
  have htk : (r.take n).take m = r.take m := by
    unfold AlterSeq.take
    simp only [AlterSeq.mk.injEq, true_and]
    congr 1
    apply List.ext_getElem?
    intro j
    rw [Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_take]
    by_cases hj : j < m
    · rw [if_pos hj, if_pos hj, Stream'.Seq.ofList_get?, seq_getElem?_take r.trans n j
        (Nat.lt_trans hj hmn)]
    · rw [if_neg hj, if_neg hj]
  rw [htk]; exact hnext

/-- **R at each prefix end.** For an infinite `simJointExecR`-consistent coupled run `r_J`, the
concrete/abstract state pair at every position `m` is `R`-related. (R-invariant applied to the
finite, consistent prefix `r_J.take m`, whose end-state is `r_J.stateAt m`.) -/
private theorem inf_coupled_R_at
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (r_J : ResolvedExec (State_C × State_A) Label) (hinf : ¬ r_J.trans.Terminates)
    (hcons : (simJointExecR pe_C sim).Consistent r_J) (m : ℕ) {p : State_C × State_A}
    (hp : r_J.stateAt m = some p) : R p.1 p.2 := by
  have hcm : (simJointExecR pe_C sim).Consistent (r_J.take m) := consistent_take _ r_J hcons m
  have hTm : (r_J.take m).trans.Terminates := take_terminates r_J m
  have hpm : (simJointExecR pe_C sim).probOfR (r_J.take m) hTm ≠ 0 :=
    consistent_imp_probOfR_ne_zero (simJointExecR pe_C sim) (r_J.take m) hcm hTm
  have hR := simJointExecR_probOfR_R pe_C sim (r_J.take m) hTm hpm
  rwa [take_endState r_J m hinf hp] at hR

/-- **Per-step rank access.** At each position `m` of an infinite consistent coupled run `r_J`, the
recorded coupling `ω` is `simCoupleF` over some concrete `μ_C`, its abstract marginal
`ω.map Prod.snd` is the recorded abstract transition, the current concrete state is
`(r_J.stateAt m).1`, and the sampled concrete successor `(r_J.stateAt (m+1)).1` lies in
`μ_C.support`. Packages the data the fairness
descent reads at each step. -/
private theorem inf_coupled_step_data
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (r_J : ResolvedExec (State_C × State_A) Label) (hinf : ¬ r_J.trans.Terminates)
    (hcons : (simJointExecR pe_C sim).Consistent r_J) (m : ℕ)
    (l : Label) (ω : PMF (State_C × State_A)) (s' : State_C × State_A)
    (hget : r_J.trans.get? m = some ((l, ω), s')) :
    ∃ (sC : State_C × State_A) (μ_C : PMF State_C),
      r_J.stateAt m = some sC ∧ r_J.stateAt (m + 1) = some s' ∧
      R sC.1 sC.2 ∧
      ω = simCoupleF sim sC l μ_C ∧
      sys_C.step sC.1 l μ_C ∧
      s'.1 ∈ μ_C.support := by
  classical
  -- Current state at `m` and successor state at `m+1`.
  have hstate_m : ∃ sC, r_J.stateAt m = some sC := by
    cases hc : r_J.stateAt m with
    | none =>
      exfalso
      -- if `stateAt m = none` then `get? m = none`, contradicting `hget`.
      cases m with
      | zero => simp [AlterSeq.stateAt] at hc
      | succ k =>
        change (r_J.trans.get? k).map Prod.snd = none at hc
        have hterm : r_J.trans.TerminatedAt k := by
          cases hk : r_J.trans.get? k with
          | none => exact hk
          | some v => rw [hk] at hc; simp at hc
        have : r_J.trans.TerminatedAt (k + 1) :=
          Stream'.Seq.terminated_stable r_J.trans (Nat.le_succ k) hterm
        rw [Stream'.Seq.TerminatedAt, hget] at this; exact absurd this (by simp)
    | some sC => exact ⟨sC, rfl⟩
  obtain ⟨sC, hsC⟩ := hstate_m
  have hsucc : r_J.stateAt (m + 1) = some s' := by
    change (r_J.trans.get? m).map Prod.snd = some s'
    rw [hget]; rfl
  -- R at `sC`.
  have hRsC : R sC.1 sC.2 := inf_coupled_R_at pe_C sim r_J hinf hcons m hsC
  -- Consistency at `m`: the emission is in the coupled scheduler's support.
  obtain ⟨hnext, hωs⟩ := hcons.2 m l ω s' hget
  -- Identify `simLastStateR (r_J.take m) = sC`.
  have hlast : simLastStateR (r_J.take m) = sC := by
    rw [simLastStateR_eq_endState (r_J.take m) (take_terminates r_J m),
      take_endState r_J m hinf hsC]
  -- Support extraction: `ω = simCoupleF ..`, over a `μ_C` with `sys_C.step`.
  obtain ⟨μ_C, hRpre, hstep, hωeq⟩ :=
    simJointSchedR_next_support pe_C sim (r_J.take m) l ω ((PMF.mem_support_iff _ _).mpr hnext)
  rw [hlast] at hstep hωeq hRpre
  -- The sampled successor's concrete part is in `μ_C.support`.
  have hsuppC : s'.1 ∈ μ_C.support := by
    have hfst : (ω.map Prod.fst) s'.1 ≠ 0 := by
      rw [PMF.map_apply]
      intro h0
      exact hωs (by
        have := ENNReal.tsum_eq_zero.mp h0 s'
        simpa using this)
    rw [hωeq, simCoupleF_map_fst sim sC l μ_C ⟨hRsC, hstep⟩] at hfst
    exact (PMF.mem_support_iff _ _).mpr hfst
  exact ⟨sC, μ_C, hsC, hsucc, hRsC, hωeq, hstep, hsuppC⟩

/-- **Reading `¬ FairStepAt` on the abstract projection.** If the coupled run records `((l, ω), s')`
at position `m` (with current state `sC`) and the abstract projection's step `m` is *not* fair, then
the recorded abstract marginal `ω.map Prod.snd` is unfair from `sC.2`. -/
private theorem absProjR_not_fairStepAt
    (r_J : ResolvedExec (State_C × State_A) Label) (m : ℕ)
    (l : Label) (ω : PMF (State_C × State_A)) (s' sC : State_C × State_A)
    (hget : r_J.trans.get? m = some ((l, ω), s')) (hsC : r_J.stateAt m = some sC)
    (hnf : ¬ F_A.FairStepAt (absProjR r_J) m) :
    ¬ F_A.fair sC.2 l (ω.map Prod.snd) := by
  intro hfair
  apply hnf
  refine ⟨sC.2, l, ω.map Prod.snd, s'.2, ?_, ?_, hfair⟩
  · rw [absProjR_stateAt, hsC]; rfl
  · change (r_J.trans.map (fun p => ((p.1.1, p.1.2.map Prod.snd), p.2.2))).get? m = _
    rw [Stream'.Seq.map_get?, hget]; rfl

omit [Silent Label] in
/-- **Prefixes of a positive-mass history have positive mass.** A finite prefix of a run with
positive `probOfR` is itself consistent (restrict), hence has positive `probOfR`. -/
private theorem probOfR_take_ne_zero {S : Type} {sys : System S Label}
    (pe : ResolvedProbabilisticExecution sys) (r : ResolvedExec S Label)
    (hT : r.trans.Terminates) (hpm : pe.probOfR r hT ≠ 0) (k : ℕ) :
    pe.probOfR (r.take k) (take_terminates r k) ≠ 0 :=
  consistent_imp_probOfR_ne_zero pe (r.take k)
    (consistent_take pe r (probOfR_ne_zero_imp_consistent pe r hT hpm) k) (take_terminates r k)

omit [Silent Label] in
/-- **A history terminated at `n` equals its own length-`n` prefix.** -/
private theorem take_self_of_terminatedAt {S : Type} (r : ResolvedExec S Label) (n : ℕ)
    (hT : r.trans.TerminatedAt n) : r.take n = r := by
  obtain ⟨i, t⟩ := r
  apply AlterSeq.mk.injEq .. |>.mpr
  refine ⟨rfl, ?_⟩
  apply Stream'.Seq.ext
  intro m
  by_cases hm : m < n
  · change (Seq.ofList (Seq.take n t)).get? m = _
    rw [Stream'.Seq.ofList_get?, seq_getElem?_take t n m hm]
  · have hmn : n ≤ m := Nat.le_of_not_lt hm
    have e1 : (Seq.ofList (Seq.take n t)).get? m = none := by
      rw [Stream'.Seq.ofList_get?]
      apply List.getElem?_eq_none
      exact Nat.le_trans (Stream'.Seq.length_take_le) hmn
    change (Seq.ofList (Seq.take n t)).get? m = t.get? m
    rw [e1, Stream'.Seq.le_stable t hmn hT]

omit [Silent Label] in
/-- **Two histories agreeing below `n`, both terminated at `n`, are equal.** Used to pin down a
child of a König node: a one-step extension of `w` at level `n` is determined by `w` (`= w'.take n`)
together with its single last transition `w'.trans.get? n`. -/
private theorem resolvedExec_eq_of_take_get?
    {S : Type} (w₁ w₂ : ResolvedExec S Label) (n : ℕ)
    (hi : w₁.init = w₂.init)
    (hle : w₁.take n = w₂.take n)
    (hn : w₁.trans.get? n = w₂.trans.get? n)
    (hT₁ : w₁.trans.TerminatedAt (n + 1)) (hT₂ : w₂.trans.TerminatedAt (n + 1)) :
    w₁ = w₂ := by
  obtain ⟨i₁, t₁⟩ := w₁
  obtain ⟨i₂, t₂⟩ := w₂
  simp only at hi; subst hi
  congr 1
  apply Stream'.Seq.ext
  intro m
  rcases lt_trichotomy m n with hm | hm | hm
  · have := congrArg (fun (e : ResolvedExec S Label) => e.trans.get? m) hle
    simpa only [take_trans_get? _ hm] using this
  · subst hm; exact hn
  · have e1 : t₁.get? m = none :=
      Stream'.Seq.le_stable _ (Nat.succ_le_of_lt hm) hT₁
    have e2 : t₂.get? m = none :=
      Stream'.Seq.le_stable _ (Nat.succ_le_of_lt hm) hT₂
    rw [e1, e2]

/-- For each `n`, a consistent abstract prefix `r_A.take n` admits a positive-mass coupled prefix
`w` projecting onto it (`absProjR w = r_A.take n`). From `pe_A.probOfR (r_A.take n) ≠ 0
= absWeight (simJointExecR …) (r_A.take n) ≠ 0`, the `absProjR`-fibre sum is positive, so it has a
positive summand — a coupled prefix with the required projection and positive path mass. -/
private theorem exists_positive_coupled_prefix
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (r_A : ResolvedExec State_A Label)
    (hcons : (abstractMarginal (simJointExecR pe_C sim)).Consistent r_A) (n : ℕ) :
    ∃ w : ResolvedExec (State_C × State_A) Label,
      absProjR w = r_A.take n ∧
      ∃ hT : w.trans.Terminates, (simJointExecR pe_C sim).probOfR w hT ≠ 0 := by
  classical
  set peJ := simJointExecR pe_C sim with hpeJ
  have hTA : (r_A.take n).trans.Terminates := take_terminates r_A n
  -- consistency of the prefix ⟹ positive path mass ⟹ positive belief weight.
  have hcm : (abstractMarginal peJ).Consistent (r_A.take n) := consistent_take _ r_A hcons n
  have hpm : (abstractMarginal peJ).probOfR (r_A.take n) hTA ≠ 0 :=
    consistent_imp_probOfR_ne_zero (abstractMarginal peJ) (r_A.take n) hcm hTA
  rw [abstractMarginal_probOfR peJ (r_A.take n) hTA] at hpm
  -- `absWeight = ∑' fibre, probOfR`, positive ⟹ a positive fibre element.
  rw [absWeight] at hpm
  obtain ⟨w, hw⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hpm)
  exact ⟨w.1, w.2, terminates_of_absProjR_eq hTA w.2, hw⟩

/-- **König lift.** An infinite
`abstractMarginal (simJointExecR pe_C sim)`-consistent abstract run `r_A` lifts to an infinite
`simJointExecR pe_C sim`-consistent coupled run `r_J` with `absProjR r_J = r_A`.

This is the single point where `sys_C.ImageFinite` is used in the fair-soundness development. The
proof drives `exists_infinite_chain` (König) on the tree of
*consistent coupled prefixes projecting onto `r_A`'s prefixes* (`exists_positive_coupled_prefix`
supplies the arbitrary-length chains):

* **Nodes / `succ`:** a node at level `n` is a coupled history `w` with `absProjR w = r_A.take n`
  and positive path mass `(simJointExecR pe_C sim).probOfR w ≠ 0`; `succ n w w'` says `w'` extends
  `w` by one coupled step and is a level-`n+1` node.
* **Finite branching (needs `ImageFinite`):** a one-step extension is determined by its last coupled
  transition `((l_n, ω), (s_C', a_{n+1}))`, whose label `l_n`, abstract marginal `ω.map snd = ν_n`,
  and abstract successor `a_{n+1}` are pinned by `r_A`'s `n`-th step; consistency forces
  `ω = simCoupleF … μ_C` with `sys_C.step (endState w).1 l_n μ_C`, so children inject into
  `{(μ_C, s_C') | sys_C.step (endState w).1 l_n μ_C ∧ s_C' ∈ μ_C.support}` — finite by the two
  clauses of `sys_C.ImageFinite` (finitely many transitions, each finitely supported).
* **Reconstruction:** from the König path `f` set `r_J.trans.get? n := (f (n+1)).trans.get? n`; then
  `r_J.take n = f n`, `absProjR r_J = r_A`, `(simJointExecR …).Consistent r_J`, and
  `¬ r_J.trans.Terminates`.

Everything else in the fairness half (`pe_A_inf_fair`, the descent, the halt case) is proven on top
of this interface. -/
private theorem exists_infinite_coupled_lift
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (hfin : sys_C.ImageFinite) (_h_init : pe_C.initState = PMF.pure sys_C.init)
    (r_A : ResolvedExec State_A Label) (hinf : ¬ r_A.trans.Terminates)
    (hcons : (abstractMarginal (simJointExecR pe_C sim)).Consistent r_A) :
    ∃ r_J : ResolvedExec (State_C × State_A) Label,
      absProjR r_J = r_A ∧ (simJointExecR pe_C sim).Consistent r_J ∧
      ¬ r_J.trans.Terminates := by
  classical
  set peJ := simJointExecR pe_C sim with hpeJ
  -- `r_A.init = sys_A.init` from consistency's initial clause.
  have hrAinit : r_A.init = sys_A.init := by
    have h1 : (abstractMarginal peJ).initState r_A.init ≠ 0 := hcons.1
    rw [abstractMarginal_simJointExecR_initState pe_C sim] at h1
    rw [PMF.pure_apply] at h1
    by_contra hc; rw [if_neg hc] at h1; exact h1 rfl
  -- The König tree.  A node at level `n` is a coupled history projecting onto `r_A.take n`, of
  -- canonical length `n` (terminated at `n`), with positive path mass.  `succ n w w'` extends `w`
  -- by one step to such a level-`n+1` node.
  set root : ResolvedExec (State_C × State_A) Label := ⟨(sys_C.init, r_A.init), Seq.nil⟩ with hroot
  set succ : ℕ → ResolvedExec (State_C × State_A) Label →
      ResolvedExec (State_C × State_A) Label → Prop := fun n w w' =>
    w'.take n = w ∧ absProjR w' = r_A.take (n + 1) ∧
      w'.trans.TerminatedAt (n + 1) ∧
      ∃ hT' : w'.trans.Terminates, peJ.probOfR w' hT' ≠ 0
    with hsucc
  -- A level-`k` node projects onto `r_A.take k`, so its init is `(sys_C.init, r_A.init)` and its
  -- prefix always terminates at `k`.
  -- **(A) König chains of every length.**
  have hchain : ∀ n : ℕ, ∃ f : ℕ → ResolvedExec (State_C × State_A) Label,
      f 0 = root ∧ ∀ i, i < n → succ i (f i) (f (i + 1)) := by
    intro n
    obtain ⟨W, hWproj, hWT, hWpm⟩ := exists_positive_coupled_prefix pe_C sim r_A hcons n
    -- `W.init = (sys_C.init, r_A.init)`.
    have hWcons : peJ.Consistent W := probOfR_ne_zero_imp_consistent peJ W hWT hWpm
    have hWinit : W.init = (sys_C.init, r_A.init) := by
      have hi1 : peJ.initState W.init ≠ 0 := hWcons.1
      change (PMF.pure (simProd sys_C sys_A R).init) W.init ≠ 0 at hi1
      rw [PMF.pure_apply] at hi1
      have hWi : W.init = (simProd sys_C sys_A R).init := by
        by_contra hc; rw [if_neg hc] at hi1; exact hi1 rfl
      rw [hWi]
      change (sys_C.init, sys_A.init) = (sys_C.init, r_A.init)
      rw [hrAinit]
    refine ⟨fun i => W.take i, ?_, ?_⟩
    · -- `f 0 = root`.
      change W.take 0 = root
      apply AlterSeq.mk.injEq .. |>.mpr
      exact ⟨hWinit, rfl⟩
    · intro i hi
      refine ⟨take_take W (i + 1) i (Nat.le_succ i), ?_, ?_, ?_⟩
      · -- `absProjR (W.take (i+1)) = r_A.take (i+1)`.
        rw [absProjR_take, hWproj, take_take r_A n (i + 1) hi]
      · -- terminated at `i+1`, transferred from `r_A`'s prefix through `absProjR`.
        rw [← absProjR_terminatedAt_iff, absProjR_take, hWproj, take_take r_A n (i + 1) hi]
        exact take_terminatedAt r_A (i + 1) hinf
      · exact ⟨take_terminates W (i + 1), probOfR_take_ne_zero peJ W hWT hWpm (i + 1)⟩
  -- **(B) Finite branching.**  A child `w'` of `w` at level `n` is determined by its single last
  -- transition `w'.trans.get? n = some ((l, ω), s')`, whose `l` and `s'.2` are pinned by
  -- `absProjR w' = r_A.take (n+1)` and whose `ω = simCoupleF … μ_C` is pinned (via consistency) by
  -- `μ_C = ω.map fst` and `s'.1 ∈ μ_C.support`.  So `w' ↦ (μ_C, s'.1)` injects the children into
  -- `{(μ_C, x) | sys_C.step (simLastStateR w).1 lₙ μ_C ∧ x ∈ μ_C.support}`, finite by `hfin`.
  have hfinChildren : ∀ (n : ℕ) (w : ResolvedExec (State_C × State_A) Label),
      {w' | succ n w w'}.Finite := by
    intro n w
    -- The pinned label / abstract successor: the `n`-th abstract transition of `r_A` (defined since
    -- `r_A` is infinite).  The finiteness target is over `simLastStateR w`.
    set sw := simLastStateR w with hsw
    obtain ⟨abstep, haget⟩ : ∃ t, r_A.trans.get? n = some t := by
      rcases hc : r_A.trans.get? n with _ | t
      · exact absurd ⟨n, hc⟩ hinf
      · exact ⟨t, rfl⟩
    obtain ⟨⟨lₙ, νₙ⟩, aₙ⟩ := abstep
    -- Target finite set: pairs `(μ_C, x)` with a `sys_C`-step and `x` in support.
    have hFinTarget : {p : PMF State_C × State_C |
        sys_C.step sw.1 lₙ p.1 ∧ p.2 ∈ p.1.support}.Finite := by
      -- `{μ_C | sys_C.step sw.1 lₙ μ_C}` is finite (a fibre of `hfin.1 sw.1`).
      have hμfin : {μ_C : PMF State_C | sys_C.step sw.1 lₙ μ_C}.Finite := by
        apply Set.Finite.subset ((hfin.1 sw.1).image Prod.snd)
        intro μ_C hμ
        exact ⟨(lₙ, μ_C), hμ, rfl⟩
      apply Set.Finite.subset
        (Set.Finite.biUnion hμfin (t := fun μ_C => (fun x => (μ_C, x)) '' μ_C.support)
          (fun μ_C hμ => (hfin.2 sw.1 lₙ μ_C hμ).image _))
      rintro ⟨μ_C, x⟩ ⟨hstep, hx⟩
      exact Set.mem_biUnion hstep ⟨x, hx, rfl⟩
    -- Map each child to `some (ω.map fst, s'.1)` at its `n`-th transition.
    set g : ResolvedExec (State_C × State_A) Label → Option (PMF State_C × State_C) :=
      fun w' => (w'.trans.get? n).map (fun t => (t.1.2.map Prod.fst, t.2.1)) with hg
    -- **Per-child data.**  For any child `w'`, its `n`-th transition is `((lₙ, ω), (s'C, aₙ))` with
    -- `ω = simCoupleF sim sw lₙ μ_C`, `μ_C = ω.map fst`, and `s'C ∈ μ_C.support`.
    have hchildData : ∀ w' ∈ {w' | succ n w w'}, ∃ (ω : PMF (State_C × State_A)) (s'C : State_C)
        (μ_C : PMF State_C),
        w'.trans.get? n = some ((lₙ, ω), (s'C, aₙ)) ∧
        ω = simCoupleF sim sw lₙ μ_C ∧ ω.map Prod.fst = μ_C ∧ s'C ∈ μ_C.support ∧
        sys_C.step sw.1 lₙ μ_C := by
      rintro w' ⟨htake, hproj, hterm, hT', hpm⟩
      -- The `n`-th transition of `w'` (exists since `w'.trans` terminates only at `n+1`).
      have hne : ¬ w'.trans.TerminatedAt n := by
        intro htn
        have : (absProjR w').trans.TerminatedAt n := (absProjR_terminatedAt_iff w' n).mpr htn
        rw [hproj] at this
        change ((r_A.take (n + 1)).trans).get? n = none at this
        rw [take_trans_get? r_A (Nat.lt_succ_self n), haget] at this
        exact absurd this (by simp)
      obtain ⟨t, hgett⟩ := Option.ne_none_iff_exists'.mp hne
      obtain ⟨⟨l', ω⟩, s'⟩ := t
      -- Pin `l' = lₙ` and `s'.2 = aₙ` from the abstract projection.
      have hpin : ((l', ω.map Prod.snd), s'.2) = ((lₙ, νₙ), aₙ) := by
        have h1 : (absProjR w').trans.get? n = some ((l', ω.map Prod.snd), s'.2) := by
          change (w'.trans.map (fun p => ((p.1.1, p.1.2.map Prod.snd), p.2.2))).get? n = _
          rw [Stream'.Seq.map_get?, hgett]; rfl
        rw [hproj, take_trans_get? r_A (Nat.lt_succ_self n), haget] at h1
        exact (Option.some.inj h1).symm
      have hl' : l' = lₙ := congrArg (·.1.1) hpin
      have hs'2 : s'.2 = aₙ := congrArg (·.2) hpin
      rw [hl'] at hgett
      rw [hl', hs'2] at hpin
      -- Consistency of `w'` at step `n`: emission in the coupled scheduler support.
      have hcons' : peJ.Consistent w' := probOfR_ne_zero_imp_consistent peJ w' hT' hpm
      obtain ⟨hnext, hωs⟩ := hcons'.2 n lₙ ω s' hgett
      rw [htake] at hnext
      obtain ⟨μ_C, hRpre, hstep, hωeq⟩ :=
        simJointSchedR_next_support pe_C sim w lₙ ω ((PMF.mem_support_iff _ _).mpr hnext)
      rw [← hsw] at hstep hωeq hRpre
      -- `μ_C = ω.map fst` and `s'.1 ∈ μ_C.support`.
      have hmapfst : ω.map Prod.fst = μ_C := by
        rw [hωeq, simCoupleF_map_fst sim sw lₙ μ_C ⟨hRpre, hstep⟩]
      have hsupp : s'.1 ∈ μ_C.support := by
        rw [← hmapfst]
        have : (ω.map Prod.fst) s'.1 ≠ 0 := by
          rw [PMF.map_apply]; intro h0
          exact hωs (by have := ENNReal.tsum_eq_zero.mp h0 s'; simpa using this)
        exact (PMF.mem_support_iff _ _).mpr this
      have hs'eq : s' = (s'.1, aₙ) := by rw [← hs'2]
      refine ⟨ω, s'.1, μ_C, ?_, hωeq, hmapfst, hsupp, hstep⟩
      rw [hgett, hs'eq]
    -- Finiteness via injective image.
    apply Set.Finite.of_injOn (f := g)
      (t := (fun p => some p) '' {p : PMF State_C × State_C |
        sys_C.step sw.1 lₙ p.1 ∧ p.2 ∈ p.1.support})
    · rintro w' hw'
      obtain ⟨ω, s'C, μ_C, hgett, hωeq, hmapfst, hsupp, hstep⟩ := hchildData w' hw'
      refine ⟨(μ_C, s'C), ⟨hstep, hsupp⟩, ?_⟩
      change some (μ_C, s'C) = g w'
      rw [hg]; simp only [hgett, Option.map_some]; rw [hmapfst]
    · -- Injectivity on children.
      rintro w'₁ hw'₁ w'₂ hw'₂ heq
      obtain ⟨ω₁, s'C₁, μ_C₁, hget₁, hωeq₁, hmap₁, _, _⟩ := hchildData w'₁ hw'₁
      obtain ⟨ω₂, s'C₂, μ_C₂, hget₂, hωeq₂, hmap₂, _, _⟩ := hchildData w'₂ hw'₂
      -- `g w'₁ = g w'₂` ⟹ `(μ_C₁, s'C₁) = (μ_C₂, s'C₂)`.
      rw [hg] at heq
      simp only [hget₁, hget₂, Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨hμ, hs⟩ := heq
      rw [hmap₁, hmap₂] at hμ
      subst hμ; subst hs
      -- Same `μ_C`, `s'C` ⟹ same `ω` (via `simCoupleF`), hence same `n`-th transition.
      have hωω : ω₁ = ω₂ := by rw [hωeq₁, hωeq₂]
      subst hωω
      have hgeteq : w'₁.trans.get? n = w'₂.trans.get? n := by rw [hget₁, hget₂]
      -- Both children terminate at `n+1` and share `w'.take n = w`.
      obtain ⟨htake₁, _, hterm₁, _⟩ := hw'₁
      obtain ⟨htake₂, _, hterm₂, _⟩ := hw'₂
      refine resolvedExec_eq_of_take_get? w'₁ w'₂ n ?_ (by rw [htake₁, htake₂]) hgeteq hterm₁ hterm₂
      -- `w'₁.init = w'₂.init` from `w'.take n = w`.
      have e1 : w'₁.init = w.init := by rw [← htake₁]; rfl
      have e2 : w'₂.init = w.init := by rw [← htake₂]; rfl
      rw [e1, e2]
    · -- the target is finite (image of `hFinTarget`).
      exact hFinTarget.image _
  -- **(C) König's lemma.**
  obtain ⟨f, hf0, hfstep⟩ := exists_infinite_chain succ root hfinChildren hchain
  -- Unpack the per-step data of the chain.
  have hfstep' : ∀ i, (f (i + 1)).take i = f i ∧ absProjR (f (i + 1)) = r_A.take (i + 1) ∧
      (f (i + 1)).trans.TerminatedAt (i + 1) ∧
      ∃ hT' : (f (i + 1)).trans.Terminates, peJ.probOfR (f (i + 1)) hT' ≠ 0 := hfstep
  -- **Prefix stability.**  `(f j).take i = f i` for `i ≤ j`.
  have hstable : ∀ i j, i ≤ j → (f j).take i = f i := by
    intro i j hij
    induction j with
    | zero =>
      obtain rfl : i = 0 := Nat.le_zero.mp hij
      rw [hf0]; rfl
    | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with hlt | heq
      · -- `i ≤ k`: peel one from `f (k+1)` down to `f k`.
        have hik : i ≤ k := Nat.lt_succ_iff.mp hlt
        rw [← take_take (f (k + 1)) k i hik, (hfstep' k).1]
        exact ih hik
      · subst heq; exact take_self_of_terminatedAt (f (k + 1)) (k + 1) (hfstep' k).2.2.1
  -- Each `f (n+1)` has a genuine `n`-th transition (its abstract projection does).
  have hsome : ∀ n, (f (n + 1)).trans.get? n ≠ none := by
    intro n htn
    have habs : (absProjR (f (n + 1))).trans.TerminatedAt n :=
      (absProjR_terminatedAt_iff (f (n + 1)) n).mpr htn
    rw [(hfstep' n).2.1] at habs
    change (r_A.take (n + 1)).trans.get? n = none at habs
    rw [take_trans_get? r_A (Nat.lt_succ_self n)] at habs
    exact hinf ⟨n, habs⟩
  -- Position-`n` transition of the assembled infinite run is `f m`'s for any `m > n`.
  have hgetstable : ∀ n m, n < m → (f m).trans.get? n = (f (n + 1)).trans.get? n := by
    intro n m hnm
    have h1 : (f m).take (n + 1) = f (n + 1) := hstable (n + 1) m hnm
    rw [← h1, take_trans_get? (f m) (Nat.lt_succ_self n)]
  -- **(D) Assemble the infinite coupled run `r_J`.**
  -- The underlying transition stream.
  have hstreamSeq : ∀ n, (fun m => (f (m + 1)).trans.get? m) n = none →
      (fun m => (f (m + 1)).trans.get? m) (n + 1) = none := fun n hn => absurd hn (hsome n)
  set r_J : ResolvedExec (State_C × State_A) Label :=
    ⟨(sys_C.init, r_A.init), ⟨fun n => (f (n + 1)).trans.get? n, hstreamSeq _⟩⟩ with hr_J
  -- `r_J.trans.get? n = (f (n+1)).trans.get? n`.
  have hrJget : ∀ n, r_J.trans.get? n = (f (n + 1)).trans.get? n := fun n => rfl
  -- `r_J` never terminates: every entry is `some`.
  have hrJinf : ¬ r_J.trans.Terminates := by
    rintro ⟨n, hn⟩
    rw [Stream'.Seq.TerminatedAt, hrJget n] at hn
    exact hsome n hn
  -- `r_J.init = f n .init = (sys_C.init, r_A.init)`, and `r_J.take n = f n`.
  have hrJtake : ∀ n, r_J.take n = f n := by
    intro n
    -- `f n` is terminated at `n`; both agree on transitions below `n` and on init.
    have hfnterm : (f n).trans.TerminatedAt n := by
      cases n with
      | zero => rw [hf0]; exact Stream'.Seq.terminatedAt_zero_iff.mpr rfl
      | succ k => exact (hfstep' k).2.2.1
    have hfninit : (f n).init = (sys_C.init, r_A.init) := by
      have := hstable 0 n (Nat.zero_le n)
      rw [hf0] at this
      have h2 : (f n).init = ((f n).take 0).init := rfl
      rw [h2, this]
    apply AlterSeq.mk.injEq .. |>.mpr
    refine ⟨hfninit.symm, ?_⟩
    apply Stream'.Seq.ext
    intro m
    by_cases hm : m < n
    · rw [Stream'.Seq.ofList_get?, seq_getElem?_take r_J.trans n m hm, hrJget m,
        ← hgetstable m n hm]
    · have hle : n ≤ m := Nat.le_of_not_lt hm
      rw [Stream'.Seq.ofList_get?]
      rw [List.getElem?_eq_none (Nat.le_trans Stream'.Seq.length_take_le hle),
        Stream'.Seq.le_stable (f n).trans hle hfnterm]
  refine ⟨r_J, ?_, ?_, hrJinf⟩
  · -- `absProjR r_J = r_A`.
    apply AlterSeq.mk.injEq .. |>.mpr
    refine ⟨rfl, ?_⟩
    apply Stream'.Seq.ext
    intro m
    -- Reduce the abstract projection's `m`-th transition to `f (m+1)`'s.
    rw [Stream'.Seq.map_get?, hrJget m,
      ← take_trans_get? r_A (Nat.lt_succ_self m), ← (hfstep' m).2.1]
    change _ = (Seq.map (fun p => ((p.1.1, p.1.2.map Prod.snd), p.2.2)) (f (m + 1)).trans).get? m
    rw [Stream'.Seq.map_get?]
  · -- `Consistent r_J`.
    refine ⟨?_, ?_⟩
    · -- Initial mass.
      change peJ.initState (sys_C.init, r_A.init) ≠ 0
      change (PMF.pure (simProd sys_C sys_A R).init) (sys_C.init, r_A.init) ≠ 0
      rw [PMF.pure_apply]
      have : (simProd sys_C sys_A R).init = (sys_C.init, r_A.init) := by
        change (sys_C.init, sys_A.init) = (sys_C.init, r_A.init); rw [hrAinit]
      rw [if_pos this.symm]; exact one_ne_zero
    · -- Step consistency at each `n`: transfer from the consistent node `f (n+1)`.
      intro n l μ s' hget
      -- `f (n+1)` is consistent (positive mass).
      obtain ⟨hTn, hpmn⟩ := (hfstep' n).2.2.2
      have hconsn : peJ.Consistent (f (n + 1)) := probOfR_ne_zero_imp_consistent peJ _ hTn hpmn
      -- The recorded transition of `r_J` at `n` is `f (n+1)`'s.
      have hgetn : (f (n + 1)).trans.get? n = some ((l, μ), s') := by
        rw [← hrJget n]; exact hget
      obtain ⟨hnext, hμ⟩ := hconsn.2 n l μ s' hgetn
      refine ⟨?_, hμ⟩
      -- `(f (n+1)).take n = f n = r_J.take n`.
      rw [hrJtake n, ← (hfstep' n).1]
      exact hnext

/-- **Infinite case.** An infinite consistent abstract witness run fires a fair `F_A`-step at some
position `≥ N`. Contradiction: assuming every step from `N` on is unfair, lift (König) to an
infinite consistent coupled run whose concrete projection is a fair `pe_C`-run (fires fairly
infinitely often); on the all-unfair-abstract tail the rank clause (`simCoupleF_rank`) gives
`sim.le` at each step and
`sim.lt` at each fair concrete step, and `descent_of_infinitely_often` (via `sim.lt_wf`) rules this
out. -/
theorem pe_A_inf_fair
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (hfin : sys_C.ImageFinite) (h_init : pe_C.initState = PMF.pure sys_C.init)
    (hfair_C : pe_C.IsFair F_C)
    (r_A : ResolvedExec State_A Label) (hinf : ¬ r_A.trans.Terminates)
    (hcons : (abstractMarginal (simJointExecR pe_C sim)).Consistent r_A) (N : ℕ) :
    ∃ n, N ≤ n ∧ F_A.FairStepAt r_A n := by
  classical
  by_contra hcontra
  push Not at hcontra
  -- All steps from `N` on are unfair.
  have hunfair : ∀ n, N ≤ n → ¬ F_A.FairStepAt r_A n := fun n hn => hcontra n hn
  -- (a) König lift to an infinite consistent coupled run.
  obtain ⟨r_J, hproj, hconsJ, hinfJ⟩ :=
    exists_infinite_coupled_lift pe_C sim hfin h_init r_A hinf hcons
  -- (b) The concrete projection is a fair `pe_C`-run: infinite and consistent.
  have hconsC : pe_C.Consistent (concreteProjR r_J) :=
    concreteProjR_consistent pe_C sim h_init r_J hconsJ
  have hinfC : ¬ (concreteProjR r_J).trans.Terminates :=
    fun h => hinfJ ((concreteProjR_terminates_iff r_J).mp h)
  have hfairC : ∀ M : ℕ, ∃ m, M ≤ m ∧ F_C.FairStepAt (concreteProjR r_J) m :=
    hfair_C.inf_fair (concreteProjR r_J) hinfC hconsC
  -- (c) Descent. `g k :=` concrete component of `r_J.stateAt (k + N)`.
  -- Since `r_J` is infinite, every state is defined; extract via a total function.
  have hstate : ∀ k, ∃ p, r_J.stateAt k = some p := by
    intro k
    cases hc : r_J.stateAt k with
    | none =>
      exfalso
      cases k with
      | zero => simp [AlterSeq.stateAt] at hc
      | succ j =>
        change (r_J.trans.get? j).map Prod.snd = none at hc
        have hterm : r_J.trans.TerminatedAt j := by
          cases hk : r_J.trans.get? j with
          | none => exact hk
          | some v => rw [hk] at hc; simp at hc
        exact hinfJ ⟨j, hterm⟩
    | some p => exact ⟨p, rfl⟩
  let stateAtTot : ℕ → State_C × State_A := fun k => (hstate k).choose
  have hstateAtTot : ∀ k, r_J.stateAt k = some (stateAtTot k) := fun k => (hstate k).choose_spec
  let g : ℕ → State_C := fun k => (stateAtTot (k + N)).1
  -- Each step `m ≥ N` is unfair on the abstract side, so `simCoupleF_rank` fires:
  -- at a non-fair concrete step it gives `sim.le`, at a fair concrete step `sim.lt`.
  have hrank : ∀ k, (¬ F_C.FairStepAt (concreteProjR r_J) (k + N) → sim.le (g (k + 1)) (g k)) ∧
      (F_C.FairStepAt (concreteProjR r_J) (k + N) → sim.lt (g (k + 1)) (g k)) := by
    intro k
    -- The recorded coupled transition at position `k + N`.
    obtain ⟨⟨l, ω⟩, s', hget⟩ : ∃ lω s', r_J.trans.get? (k + N) = some (lω, s') := by
      cases hc : r_J.trans.get? (k + N) with
      | none => exact absurd ⟨k + N, hc⟩ hinfJ
      | some v => obtain ⟨lω, s'⟩ := v; exact ⟨lω, s', rfl⟩
    obtain ⟨sC, μ_C, hsC, hsucc, hRsC, hωeq, hstep, hsuppC⟩ :=
      inf_coupled_step_data pe_C sim r_J hinfJ hconsJ (k + N) l ω s' hget
    -- Identify `sC = stateAtTot (k+N)` and `s' = stateAtTot (k+N+1)`.
    have hsC_eq : sC = stateAtTot (k + N) := by
      have := hstateAtTot (k + N); rw [hsC] at this; exact Option.some.inj this
    have hs'_eq : s' = stateAtTot (k + N + 1) := by
      have := hstateAtTot (k + N + 1); rw [hsucc] at this; exact Option.some.inj this
    -- Unfairness of the recorded abstract marginal.
    have hnf : ¬ F_A.FairStepAt r_A (k + N) := hunfair (k + N) (Nat.le_add_left N k)
    rw [← hproj] at hnf
    have hunf : ¬ F_A.fair sC.2 l (ω.map Prod.snd) :=
      absProjR_not_fairStepAt r_J (k + N) l ω s' sC hget hsC hnf
    -- `ω.map snd = (simCoupleF sim sC l μ_C).map snd`; feed to `simCoupleF_rank`.
    rw [hωeq] at hunf
    have hrankF := simCoupleF_rank sim sC l μ_C ⟨hRsC, hstep⟩ hunf
    -- `g k = sC.1`, `g (k+1) = s'.1`.
    have hgk : g k = sC.1 := by rw [show g k = (stateAtTot (k + N)).1 from rfl, ← hsC_eq]
    have hgk1 : g (k + 1) = s'.1 := by
      rw [show g (k + 1) = (stateAtTot (k + 1 + N)).1 from rfl,
        show k + 1 + N = k + N + 1 from by ring, ← hs'_eq]
    -- The concrete projection records `((l, μ_C), s'.1)` with current state `sC.1` at `k + N`.
    have hμ_C : ω.map Prod.fst = μ_C := by
      rw [hωeq]; exact simCoupleF_map_fst sim sC l μ_C ⟨hRsC, hstep⟩
    have hgetC : (concreteProjR r_J).trans.get? (k + N) = some ((l, μ_C), s'.1) := by
      change (r_J.trans.map (fun p => ((p.1.1, p.1.2.map Prod.fst), p.2.1))).get? (k + N) = _
      rw [Stream'.Seq.map_get?, hget]
      simp only [Option.map_some]
      rw [hμ_C]
    have hstateC : (concreteProjR r_J).stateAt (k + N) = some sC.1 := by
      rw [concreteProjR_stateAt, hsC]; rfl
    refine ⟨?_, ?_⟩
    · -- `¬ fair concrete step ⟹ le`.
      intro hnfair
      -- The concrete step at `k+N` is not fair, so `¬ F_C.fair sC.1 l μ_C`.
      have hnfc : ¬ F_C.fair sC.1 l μ_C := by
        intro hfc; exact hnfair ⟨sC.1, l, μ_C, s'.1, hstateC, hgetC, hfc⟩
      have := (hrankF.2 hnfc) s'.1 hsuppC
      rw [hgk, hgk1]; exact this
    · -- fair concrete step ⟹ `lt`.
      intro hfair_step
      obtain ⟨s, l', μ', s'', hst, hgt, hfair⟩ := hfair_step
      -- Identify the fair transition with `(sC.1, l, μ_C)` via `get?`/`stateAt` injectivity.
      rw [hstateC] at hst; rw [hgetC] at hgt
      obtain rfl : s = sC.1 := (Option.some.inj hst).symm
      obtain ⟨⟨rfl, rfl⟩, _⟩ := Prod.mk.injEq .. ▸ (Option.some.inj hgt)
      have := (hrankF.1 hfair) s'.1 hsuppC
      rw [hgk, hgk1]; exact this
  -- With `lt` the strict part of `le`, `le` holds at *every* step (via `le_of_lt` at the fair
  -- ones), so the standard `descent_of_infinitely_often` applies directly.
  have hle_all : ∀ k, sim.le (g (k + 1)) (g k) := fun k => by
    by_cases hP : F_C.FairStepAt (concreteProjR r_J) (k + N)
    · exact sim.le_of_lt ((hrank k).2 hP)
    · exact (hrank k).1 hP
  refine descent_of_infinitely_often sim.lt_wf sim.le_refl sim.le_trans sim.lt_of_le_of_lt
    g hle_all (fun k => F_C.FairStepAt (concreteProjR r_J) (k + N)) (fun k => (hrank k).2) ?_
  -- `P` holds infinitely often (from `hfairC`, reindexed by `+ N`).
  intro M
  obtain ⟨m, hmM, hfm⟩ := hfairC (M + N)
  exact ⟨m - N, by omega, by rwa [Nat.sub_add_cancel (by omega)]⟩

/-- **Ranked strong simulation preserves fair achievable trace distributions** (fair soundness),
under image-finiteness of the concrete system.

Every trace distribution achievable by a *fair* resolved-history execution of `sys_C` is achievable
by a *fair* resolved-history execution of `sys_A`.

The `sys_C.ImageFinite` hypothesis is what makes the fairness half go through: it bounds the
branching of the *consistent* coupled tree so König's lemma lifts an infinite consistent abstract
run to an infinite consistent coupled run whose concrete projection is a fair `pe_C`-run. (The trace
half needs no finiteness. The unconditional statement — dropping `ImageFinite` — is left open; see
the module docstring.) The proof is complete and axiom-clean; the König lift
`exists_infinite_coupled_lift` (used only by the infinite-run fairness clause) is the single point
where `ImageFinite` enters — see its docstring and
the module docstring for the full, finiteness-analysed plan.

Proof sketch:
* Drive the coupled product `simProd sys_C sys_A R` by the fair resolved `pe_C`, emitting at each
  step the single coupling `simCoupleF sim …` (so `simProd` is *not* image-finite as a step
  relation, but the coupled *execution* commits to one coupling per concrete transition, keeping the
  consistent coupled tree finitely branching under `sys_C.ImageFinite`).
* Marginalise onto `sys_A` (resolved posterior average); `pe_A.initState = PMF.pure sys_A.init` and
  `pe_A.traceProbR = pe_C.traceProbR` (no finiteness).
* `pe_A.IsFair F_A`:
  - `halt_fairDeadlock`: a halting consistent `pe_A`-run has a coupled witness that halts, so `pe_C`
    fairness puts its concrete end at a fair deadlock, whose `R`-image is a fair deadlock by
    `sim.fair_deadlock` (no finiteness).
  - `inf_fair`: an infinite consistent `pe_A`-run lifts (König, `exists_infinite_chain`, using
    `sys_C.ImageFinite`) to an infinite consistent coupled run; its concrete projection is a fair
    `pe_C`-run, so fires fairly infinitely often; on the all-unfair-abstract tail the rank clause of
    `sim.step` gives `le` at unfair and `lt` at fair concrete steps, and
    `descent_of_infinitely_often` (via `sim.lt_wf`, `sim.le_refl`, `sim.le_trans`,
    `sim.lt_of_le_of_lt`) rules out finitely many fair abstract steps. -/
theorem fairAchievableTraceDists_subset
    (sim : FairStrongProbabilisticSimulation F_C F_A R) (hfin : sys_C.ImageFinite) :
    fairAchievableTraceDists F_C ⊆ fairAchievableTraceDists F_A := by
  rintro D ⟨pe_C, h_init, hfair_C, htr⟩
  -- The abstract witness is the abstract marginal of the coupled resolved lift.
  refine ⟨abstractMarginal (simJointExecR pe_C sim),
    abstractMarginal_simJointExecR_initState pe_C sim, ?_, ?_⟩
  · -- `pe_A.IsFair F_A`: the halt clause is the halt case, the infinite clause is the infinite
    -- case.
    exact
      { halt_fairDeadlock := fun r_A hT hcons hnone =>
          pe_A_halt_fairDeadlock pe_C sim h_init hfair_C r_A hT hcons hnone
        inf_fair := fun r_A hinf hcons N =>
          pe_A_inf_fair pe_C sim hfin h_init hfair_C r_A hinf hcons N }
  · -- Trace preservation, composed with the source's `traceProbR = D`.
    exact fun τ => (abstractMarginal_simJointExecR_traceProbR pe_C sim h_init τ).trans (htr τ)

open ResolvedProbabilisticExecution in
/-- **The abstract scheduler built by the fair-soundness construction is finitely branching.** Under
`sys_C.ImageFinite`, at every terminating resolved history `r_A` the marginalised abstract scheduler
`abstractMarginal (simJointExecR pe_C sim)` schedules only finitely many transitions with positive
probability (its `next`-support is finite).

The two ingredients — matching the informal intuition — are both consequences of `ImageFinite`: each
abstract history simulates only finitely many concrete histories (`positive_histories_finite`, via
the finitely-branching consistent coupled tree), and on each the concrete scheduler emits only
finitely many transitions with positive probability (`ResolvedScheduler.next_support_finite`), each
mapping (through `simCoupleF`/`Prod.snd`) to a single abstract transition. Fairness of `pe_C` plays
no role; finite branching of `pe_C` is automatic from `ImageFinite` and resolved-scheduler validity.

Not needed for `fairAchievableTraceDists_subset` — an explicit record of the finite-branching fact
behind the König lift `exists_infinite_coupled_lift`. -/
theorem abstractMarginal_simJointExecR_next_support_finite
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (hfin : sys_C.ImageFinite) (h_init : pe_C.initState = PMF.pure sys_C.init)
    (r_A : ResolvedExec State_A Label) (hT : r_A.trans.Terminates) :
    ((abstractMarginal (simJointExecR pe_C sim)).scheduler.next r_A).support.Finite := by
  classical
  have hinitFin : pe_C.initState.support.Finite := by
    rw [h_init, PMF.support_pure]; exact Set.finite_singleton _
  set n := (r_A.trans.toList hT).length with hn
  have hposCfin : {r_C : ResolvedExec State_C Label | ∃ hTc : r_C.trans.Terminates,
      (r_C.trans.toList hTc).length = n ∧ pe_C.probOfR r_C hTc ≠ 0}.Finite :=
    ResolvedProbabilisticExecution.positive_histories_finite pe_C hfin hinitFin n
  -- the abstract emission read off a concrete history and its `pe_C`-emission
  set g : ResolvedExec State_C Label → Option (Label × PMF State_C) →
      Option (Label × PMF State_A) :=
    fun r_C o => o.map (fun lμ =>
      (lμ.1, (simCoupleF sim (lastStateAux r_C, r_A.endState hT) lμ.1 lμ.2).map Prod.snd)) with hg
  apply Set.Finite.subset (Set.Finite.insert none
    (Set.Finite.biUnion hposCfin (fun r_C hr_C =>
      Set.Finite.image (g r_C)
        (ResolvedScheduler.next_support_finite pe_C.scheduler hfin r_C hr_C.choose))))
  intro x hx
  cases x with
  | none => exact Set.mem_insert _ _
  | some lν =>
    obtain ⟨l, ν⟩ := lν
    apply Set.mem_insert_of_mem
    -- extract a positive fibre element and its pushed-forward emission
    have hval := abstractMarginal_next_some (simJointExecR pe_C sim) r_A hT l ν
    rw [PMF.mem_support_iff, hval] at hx
    have hnum : (∑' r : {r : ResolvedExec (State_C × State_A) Label // absProjR r = r_A},
        (simJointExecR pe_C sim).probOfR r.1 (terminates_of_absProjR_eq hT r.2)
          * (((simJointExecR pe_C sim).scheduler.next r.1).map (mapEmit Prod.snd))
              (some (l, ν))) ≠ 0 :=
      (mul_ne_zero_iff.mp hx).1
    obtain ⟨r, hr⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hnum)
    have hTr : r.1.trans.Terminates := terminates_of_absProjR_eq hT r.2
    have hprob : (simJointExecR pe_C sim).probOfR r.1 hTr ≠ 0 := fun h => hr (by rw [h, zero_mul])
    have hpush : (((simJointExecR pe_C sim).scheduler.next r.1).map (mapEmit Prod.snd))
        (some (l, ν)) ≠ 0 := fun h => hr (by rw [h, mul_zero])
    -- unpick the coupling `ω` over `ν`
    obtain ⟨ω, hωne, hνeq⟩ :
        ∃ ω : PMF (State_C × State_A),
          (simJointExecR pe_C sim).scheduler.next r.1 (some (l, ω)) ≠ 0 ∧ ν = ω.map Prod.snd := by
      rw [mapEmit, PMF.map_apply] at hpush
      obtain ⟨o, ho⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hpush)
      by_cases hc : some (l, ν) = Option.map
          (fun lμ : Label × PMF (State_C × State_A) => (lμ.1, lμ.2.map Prod.snd)) o
      · cases o with
        | none => simp at hc
        | some lμ =>
          obtain ⟨l', ω⟩ := lμ
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          exact ⟨ω, fun h0 => by rw [h0] at ho; simp at ho, rfl⟩
      · rw [if_neg hc] at ho; exact absurd rfl ho
    -- identify `ω` as `simCoupleF` and read off the underlying `pe_C`-emission
    obtain ⟨μ_C, hRpre, hstep, hωeq⟩ :=
      simJointSchedR_next_support pe_C sim r.1 l ω ((PMF.mem_support_iff _ _).mpr hωne)
    obtain ⟨μ_C', hnextC, _, _, hfstμ⟩ :=
      simJointSchedR_next_support_concrete pe_C sim r.1 l ω ((PMF.mem_support_iff _ _).mpr hωne)
    have hμeq : μ_C' = μ_C := by
      rw [← hfstμ, hωeq]
      exact simCoupleF_map_fst sim (simLastStateR r.1) l μ_C ⟨hRpre, hstep⟩
    rw [hμeq] at hnextC
    -- the concrete projection is a positive length-`n` `pe_C`-history
    have hTrC : (concreteProjR r.1).trans.Terminates := (concreteProjR_terminates_iff r.1).mpr hTr
    have hlenC : ((concreteProjR r.1).trans.toList hTrC).length = n := by
      have e1 : ((concreteProjR r.1).trans.toList hTrC).length = Nat.find hTrC :=
        Stream'.Seq.length_toList _ _
      have e2 : (r_A.trans.toList hT).length = Nat.find hT := Stream'.Seq.length_toList _ _
      have hfind1 : Nat.find hTrC = Nat.find hTr := by
        apply Nat.find_congr'; intro m; exact concreteProjR_terminatedAt_iff r.1 m
      have hfind2 : Nat.find hTr = Nat.find hT := by
        apply Nat.find_congr'; intro m; rw [← absProjR_terminatedAt_iff r.1 m, r.2]
      rw [hn, e1, e2, hfind1, hfind2]
    have hconsJ : (simJointExecR pe_C sim).Consistent r.1 :=
      probOfR_ne_zero_imp_consistent (simJointExecR pe_C sim) r.1 hTr hprob
    have hconsC : pe_C.Consistent (concreteProjR r.1) :=
      concreteProjR_consistent pe_C sim h_init r.1 hconsJ
    have hpmC : pe_C.probOfR (concreteProjR r.1) hTrC ≠ 0 :=
      consistent_imp_probOfR_ne_zero pe_C (concreteProjR r.1) hconsC hTrC
    have hr_Cmem : (concreteProjR r.1) ∈ {r_C : ResolvedExec State_C Label |
        ∃ hTc : r_C.trans.Terminates,
          (r_C.trans.toList hTc).length = n ∧ pe_C.probOfR r_C hTc ≠ 0} := ⟨hTrC, hlenC, hpmC⟩
    -- `simLastStateR r.1 = (lastStateAux (concreteProjR r.1), r_A.endState hT)`
    have hTrA : (absProjR r.1).trans.Terminates := by rw [r.2]; exact hT
    have hlast : simLastStateR r.1 = (lastStateAux (concreteProjR r.1), r_A.endState hT) := by
      rw [simLastStateR_eq_endState r.1 hTr]
      apply Prod.ext
      · rw [show (r.1.endState hTr).1 = (concreteProjR r.1).endState hTrC from
            (concreteProjR_endState r.1 hTr hTrC).symm, lastStateAux, dif_pos hTrC]
      · rw [show (r.1.endState hTr).2 = (absProjR r.1).endState hTrA from
            (absProjR_endState r.1 hTr hTrA).symm]
        exact AlterSeq.endState_congr_pub r.2 hTrA hT
    -- `some (l, ν) = g (concreteProjR r.1) (some (l, μ_C))`, whose input is a `pe_C`-emission
    refine Set.mem_biUnion hr_Cmem ⟨some (l, μ_C), (PMF.mem_support_iff _ _).mpr hnextC, ?_⟩
    have hνX : ν = (simCoupleF sim (lastStateAux (concreteProjR r.1), r_A.endState hT) l μ_C).map
        Prod.snd := by rw [hνeq, hωeq, hlast]
    simp only [hg, Option.map_some]
    rw [hνX]

end FairStrongProbabilisticSimulation

end PLTS
