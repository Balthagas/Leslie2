/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCASpec
import Leslie2Protocols.ABA.SpecSafety
import Leslie2Protocols.Framework.TraceSupport

/-!
# Safety of the GBCA specification instance

Binding is the promise a Graded Binding Crusader Agreement instance makes about
its *future*: there is a bit the instance will never hand out, in this run or in
any extension of it. On the specification state that promise is a field rather
than a theorem. `SpecState.dead : Finset Bool` is the set of bits the instance
can no longer hand out; the value-bearing returns refuse a dead bit and demand
that the other bit be dead, and the `C`-return demands that some bit be dead.

Binding and graded agreement rest on one fact: `dead` only grows. The single
writer is the internal `bindUnset`, which inserts, and `corrupt` does not touch
the field — so `Step.dead_mono` holds rule by rule, and `is_exec_stable` lifts
it to whole executions (`dead_mem_stable`). Binding is
therefore structural: a bit killed at any point of a run is killed at every
later point, and a guard reading `∉ dead` can never be re-enabled. That writer
also fires only from `dead = ∅`, so the exclusion set never holds more than one
bit (`dead_card_le_one`, from the step-level `Step.dead_card_le_one`): the kill
commits the round, and the surviving bit stays available to every later return.

* `retG_value_agree` — **graded agreement**. Two returns of one execution that
  hand out a bit hand out the same bit. A return of `v₁` fires from a state with
  `(!v₁) ∈ dead`; monotonicity carries that membership to the state of any other
  return; that return needs its own bit alive, so its bit is not `!v₁`, so on
  `Bool` it is `v₁`. No invariant, no quorum arithmetic, no reachability
  hypothesis beyond membership in one execution.
* `specInst_binding` — the same statement read off the trace: any two round-`r`
  graded-return labels of a positive-probability trace of `specInst P r` that
  name a bit (`outValue`, defined here: `A b` and `B b` name `b`, `C` names
  nothing) name the same bit.
* `retC_dead_nonempty` — the **Graded Binding witness**, as the complement of
  the bit the return kills. After a `C`-return,
  `dead` is nonempty in every later state of the execution. A member of `dead`
  is a bit no non-faulty party can be handed at grade `≥ 1` in any extension,
  which is ABDY22's Graded Binding clause; the witness is produced at the
  `C`-return and survives because `dead` never shrinks.
* `specInst_validity` — **Validity, safety half**. If every round-`r` call of
  the trace carries the bit `v` unless its caller is corrupted somewhere along
  the trace (`UnanimousInput`), then every round-`r` return of the trace hands
  out `v` (`ValidityTrace`); in particular no `C`-return occurs
  (`specInst_no_retC`). The other two halves of the papers' Validity clause —
  that the grade is the top one, and that every non-faulty process is answered
  at all — are fairness statements about which runs the scheduler must extend,
  outside the scope of a safety file.

"Corrupted somewhere along the trace" is `SpecSafety`'s never-corrupted
formulation, taken verbatim: `NeverCorrupted P t id` is non-membership in
`failSet P t k` for every `k`, the trace-level fold of D1-`corrupt` over the
`fail` labels, so a `fail id` that the budget refuses does not count as
corruption. Validity is the D15 counts read against that budget. The state
carries no invariant beyond a bookkeeping one (`CallInv`: every pending input
is attributed to a `callG` event of the history, and `F` is the fold of the
history's `fail` labels); the argument is then a pigeonhole. At any state,
every id supporting the dissenting bit `!v` is corrupted at some stage of the
trace — a caller of `!v` by unanimity, an `F`-member by the fold — and
`failSet` is monotone in the stage, so the whole support set sits inside one
`failSet P t K`, of size at most `f` (`supp_le_of_unanimous`). The D15 guards
asking `f + 1` there are therefore unreachable: `bindUnset v` never fires, so
`v` is alive at every state (`dead_notMem_of_unanimous`), which forces the
value-bearing returns to hand out `v` and refutes `retC` outright.

The scope is the specification instance alone. That the implementation refines
it — hence inherits these properties — is the subject of the per-instance
forward simulation.
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA

variable {P : Params} {r : ℕ}

/-! ### Monotonicity of the exclusion set -/

/-- **The exclusion set never shrinks.** -/
theorem Step.dead_mono {s s' : SpecState P.n} {l : Lab P.n}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s l μ) (hs' : s' ∈ μ.support) :
    s.dead ⊆ s'.dead := by
  cases hstep <;>
    · rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      first
        | exact Finset.subset_insert _ _
        | exact Finset.Subset.refl _
        | (rw [corrupt_dead])

/-! ### Run-level monotonicity -/

/-- **A dead bit stays dead along a run.** -/
theorem dead_mem_stable {e : AlterSeq (SpecState P.n) (Lab P.n)}
    (he : is_exec e (specInst P r)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {b : Bool}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hb : b ∈ s₁.dead) : b ∈ s₂.dead :=
  is_exec_stable (sys := specInst P r) (fun s => b ∈ s.dead)
    (fun _ _ _ _ hmem hstep hs' => Step.dead_mono hstep hs' hmem)
    he k₁ k₂ s₁ s₂ hk hst₁ hst₂ hb

/-! ### The exclusion set holds at most one bit -/

/-- **One kill per instance, step level.** `bindUnset` is the only writer and
it fires only from `dead = ∅`, so it leaves a singleton; every other rule
leaves the field alone. -/
theorem Step.dead_card_le_one {s s' : SpecState P.n} {l : Lab P.n}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s l μ) (hs' : s' ∈ μ.support)
    (h : s.dead.card ≤ 1) : s'.dead.card ≤ 1 := by
  cases hstep with
  | bindUnset b hq hw hd0 =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    change (insert b s.dead).card ≤ 1
    rw [hd0]
    simp
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    rw [corrupt_dead]
    exact h
  | _ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact h

/-- **One kill per instance.** Every state of every execution of the round-`r`
instance has `dead.card ≤ 1`: the field starts empty and the single writer
fires only from `∅`. Together with `Step.dead_mono` this pins the reachable
shape to `dead ∈ {∅, {b}}` — the killed-bit reading of the source blueprint's
bound value (D19). -/
theorem dead_card_le_one {e : AlterSeq (SpecState P.n) (Lab P.n)}
    (he : is_exec e (specInst P r)) {k : ℕ} {s : SpecState P.n}
    (hst : e.stateAt k = some s) : s.dead.card ≤ 1 :=
  is_exec_stable (sys := specInst P r) (fun s => s.dead.card ≤ 1)
    (fun _ _ _ _ h hstep hs' => Step.dead_card_le_one hstep hs' h)
    he 0 k e.init s (Nat.zero_le k) rfl hst
    (by rw [← he.2]; simp [specInst, SpecState.initial])

/-! ### Inverting the return rows -/

/-- The bit a graded outcome hands out, if any: `A b` and `B b` hand out `b`,
`C` hands out nothing. -/
def outValue : GbcaOut → Option Bool
  | .A b => some b
  | .B b => some b
  | .C => none

@[simp] theorem outValue_A (b : Bool) : outValue (.A b) = some b := rfl

@[simp] theorem outValue_B (b : Bool) : outValue (.B b) = some b := rfl

@[simp] theorem outValue_C : outValue .C = none := rfl

/-- An `A`-return pins its bit alive and the other bit dead. -/
private theorem retA_inv {s : SpecState P.n} {id : Fin P.n} {v : Bool}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s (.retG r id (.A v)) μ) :
    v ∉ s.dead ∧ (!v) ∈ s.dead :=
  match hstep with
  | .retA _ _ _ hlive hdead _ _ => ⟨hlive, hdead⟩

/-- A `B`-return pins its bit alive and the other bit dead. -/
private theorem retB_inv {s : SpecState P.n} {id : Fin P.n} {v : Bool}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s (.retG r id (.B v)) μ) :
    v ∉ s.dead ∧ (!v) ∈ s.dead :=
  match hstep with
  | .retB _ _ _ hlive hdead _ _ => ⟨hlive, hdead⟩

/-- A `C`-return pins the exclusion set nonempty. -/
private theorem retC_inv {s : SpecState P.n} {id : Fin P.n}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s (.retG r id .C) μ) :
    s.dead.Nonempty :=
  match hstep with
  | .retC _ _ hd _ _ _ _ => Finset.card_pos.mp hd

/-- **The guard pair of a value-bearing return.** Whatever its grade, a return
that hands out `v` fires from a state where `v` is alive and `!v` is dead. -/
theorem retG_value_guards {s : SpecState P.n} {id : Fin P.n} {o : GbcaOut}
    {v : Bool} {μ : PMF (SpecState P.n)}
    (hstep : Step P r s (.retG r id o) μ) (ho : outValue o = some v) :
    v ∉ s.dead ∧ (!v) ∈ s.dead := by
  cases o with
  | A w =>
    obtain rfl : w = v := by simpa using ho
    exact retA_inv hstep
  | B w =>
    obtain rfl : w = v := by simpa using ho
    exact retB_inv hstep
  | C => exact absurd ho (by simp)

/-! ### Binding and graded agreement along a run -/

/-- Two value-bearing returns of one run agree on the bit (`k₁ ≤ k₂` case). -/
private theorem retG_value_agree_le {e : AlterSeq (SpecState P.n) (Lab P.n)}
    (he : is_exec e (specInst P r)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {id₁ id₂ : Fin P.n} {o₁ o₂ : GbcaOut} {v₁ v₂ : Bool}
    {μ₁ μ₂ : PMF (SpecState P.n)}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep₁ : Step P r s₁ (.retG r id₁ o₁) μ₁)
    (hstep₂ : Step P r s₂ (.retG r id₂ o₂) μ₂)
    (ho₁ : outValue o₁ = some v₁) (ho₂ : outValue o₂ = some v₂) : v₁ = v₂ := by
  obtain ⟨-, hdead₁⟩ := retG_value_guards hstep₁ ho₁
  obtain ⟨hlive₂, -⟩ := retG_value_guards hstep₂ ho₂
  have hcarry : (!v₁) ∈ s₂.dead := dead_mem_stable he hk hst₁ hst₂ hdead₁
  have hne : v₂ ≠ !v₁ := fun h => hlive₂ (h ▸ hcarry)
  revert hne
  cases v₁ <;> cases v₂ <;> simp

/-- **Binding / graded agreement.** Any two value-bearing returns occurring
along one execution of the round-`r` specification instance hand out the same
bit, whatever their grades and whichever processes they answer. The whole
argument is the guard pair plus monotonicity: the first return pins `!v₁` into
`dead`, `dead` only grows, and the second return refuses a dead bit. -/
theorem retG_value_agree {e : AlterSeq (SpecState P.n) (Lab P.n)}
    (he : is_exec e (specInst P r)) {k₁ k₂ : ℕ}
    {s₁ s₂ : SpecState P.n} {id₁ id₂ : Fin P.n} {o₁ o₂ : GbcaOut} {v₁ v₂ : Bool}
    {μ₁ μ₂ : PMF (SpecState P.n)}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep₁ : Step P r s₁ (.retG r id₁ o₁) μ₁)
    (hstep₂ : Step P r s₂ (.retG r id₂ o₂) μ₂)
    (ho₁ : outValue o₁ = some v₁) (ho₂ : outValue o₂ = some v₂) : v₁ = v₂ := by
  rcases le_total k₁ k₂ with h | h
  · exact retG_value_agree_le he h hst₁ hst₂ hstep₁ hstep₂ ho₁ ho₂
  · exact (retG_value_agree_le he h hst₂ hst₁ hstep₂ hstep₁ ho₂ ho₁).symm

/-- **The Graded Binding witness**, as the complement of the bit the return
kills. A `C`-return leaves the exclusion set nonempty in every later state of
the execution: the bit it kills is a bit no extension of the run can ever hand
out, so the surviving complement is the clause's witness. -/
theorem retC_dead_nonempty {e : AlterSeq (SpecState P.n) (Lab P.n)}
    (he : is_exec e (specInst P r)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {id : Fin P.n} {μ : PMF (SpecState P.n)}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep : Step P r s₁ (.retG r id .C) μ) : s₂.dead.Nonempty := by
  obtain ⟨b, hb⟩ := retC_inv hstep
  exact ⟨b, dead_mem_stable he hk hst₁ hst₂ hb⟩

/-! ### The trace-level statement -/

/-- **Binding (trace form).** Any two round-`r` graded returns appearing in the
trace that hand out a bit hand out the same bit. -/
def BindingTrace (P : Params) (r : ℕ) (t : Seq (Lab P.n)) : Prop :=
  ∀ (id₁ id₂ : Fin P.n) (o₁ o₂ : GbcaOut) (v₁ v₂ : Bool),
    Lab.retG r id₁ o₁ ∈ t → Lab.retG r id₂ o₂ ∈ t →
    outValue o₁ = some v₁ → outValue o₂ = some v₂ → v₁ = v₂

/-- **Binding of the GBCA specification instance**: every trace in the support
of every achievable trace distribution of `GBCA.specInst P r` satisfies
`BindingTrace`. -/
theorem specInst_binding (P : Params) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (specInst P r), ∀ t, D t ≠ 0 →
      BindingTrace P r t := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne
  rw [← h_D t] at h_ne
  obtain ⟨e, h_exec, h_char⟩ :=
    exists_exec_of_traceProb_ne_zero pe h_init t h_ne
  intro id₁ id₂ o₁ o₂ v₁ v₂ h₁ h₂ ho₁ ho₂
  obtain ⟨-, k₁, s₁', hg₁⟩ := (h_char _).mp h₁
  obtain ⟨-, k₂, s₂', hg₂⟩ := (h_char _).mp h₂
  obtain ⟨s₁, μ₁, hst₁, hstep₁, -⟩ := h_exec.1 k₁ _ _ hg₁
  obtain ⟨s₂, μ₂, hst₂, hstep₂, -⟩ := h_exec.1 k₂ _ _ hg₂
  exact retG_value_agree h_exec hst₁ hst₂ hstep₁ hstep₂ ho₁ ho₂

/-! ### Validity: the trace-level hypothesis and conclusion -/

/-- **Unanimous honest input `v`** (trace form): every round-`r` call of the
trace carries `v`, unless its caller is corrupted somewhere along the trace.
Corruption is `SpecSafety`'s trace-level notion (`NeverCorrupted`, the fold
`failSet` of D1-`corrupt` over the `fail` labels), not the bare presence of a
`fail` label: a `fail` the budget refuses corrupts nobody. -/
def UnanimousInput (P : Params) (r : ℕ) (v : Bool) (t : Seq (Lab P.n)) : Prop :=
  ∀ (id : Fin P.n) (b : Bool), Lab.callG r id b ∈ t →
    b = v ∨ ¬ NeverCorrupted P t id

/-- **Validity, safety half** (trace form): every round-`r` return of the trace
hands out `v`. Returner-unconditional, and it excludes `C` outright, `C`
handing out nothing. -/
def ValidityTrace (P : Params) (r : ℕ) (v : Bool) (t : Seq (Lab P.n)) : Prop :=
  ∀ (id : Fin P.n) (o : GbcaOut), Lab.retG r id o ∈ t → outValue o = some v

/-! ### The bookkeeping invariant -/

/-- `corrupt` acts on `F` exactly as the bare-set fold step `corruptF`. -/
theorem corrupt_F (s : SpecState P.n) (id : Fin P.n) :
    (s.corrupt P id).F = corruptF P id s.F := by
  unfold SpecState.corrupt corruptF; split <;> rfl

/-- The history-aware bookkeeping invariant: every pending input is attributed
to a `callG` event of the label history, and the corrupted set is exactly the
fold of D1-`corrupt` over that history. Both conjuncts are read off the rules:
`call` is written only by the `callG`-labelled rule, `F` only by `fail`. -/
structure CallInv (P : Params) (r : ℕ) (pre : List (Lab P.n))
    (s : SpecState P.n) : Prop where
  /-- Every pending input has a `callG` event behind it. -/
  call_src : ∀ id b, s.call id = some b → Lab.callG r id b ∈ pre
  /-- The corrupted set is the fold of the history's `fail` labels. -/
  F_eq : s.F = failSetL P pre

theorem CallInv.initial (P : Params) (r : ℕ) :
    CallInv P r [] (SpecState.initial P.n) where
  call_src := fun _ _ h => absurd h (by simp [SpecState.initial])
  F_eq := rfl

/-- **Bookkeeping-invariant preservation.** -/
theorem CallInv.step {pre : List (Lab P.n)} {s : SpecState P.n} {l : Lab P.n}
    {μ : PMF (SpecState P.n)} {s' : SpecState P.n}
    (hI : CallInv P r pre s) (hstep : Step P r s l μ) (hs' : s' ∈ μ.support) :
    CallInv P r (pre ++ [l]) s' := by
  have mono : ∀ {l' : Lab P.n}, l' ∈ pre → l' ∈ pre ++ [l] :=
    fun h => List.mem_append_left _ h
  cases hstep with
  | call id b h =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨?_, ?_⟩
    · intro id' b' h_in
      replace h_in : Function.update s.call id (some b) id' = some b' := h_in
      by_cases h_eq : id' = id
      · subst h_eq
        rw [Function.update_self] at h_in
        obtain rfl := Option.some.inj h_in
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · rw [Function.update_of_ne h_eq] at h_in
        exact mono (hI.call_src id' b' h_in)
    · rw [failSetL_append]
      exact hI.F_eq
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨?_, ?_⟩
    · intro id' b' h_in
      rw [corrupt_call] at h_in
      exact mono (hI.call_src id' b' h_in)
    · rw [failSetL_append, corrupt_F, hI.F_eq]
      rfl
  | _ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    exact ⟨fun id' b' h_in => mono (hI.call_src id' b' h_in), by
      rw [failSetL_append]; exact hI.F_eq⟩

/-! ### The budget bound on support for the dissenting bit -/

/-- **The D15 count at the dissenting bit is unreachable.** Under unanimous
input `v`, every id the count `f + 1 ≤ #{id | call id = some (!v) ∨ id ∈ F}`
could draw on is corrupted at some stage of the trace: a caller of `!v` by the
unanimity hypothesis, an `F`-member because `F` is the trace-level fold. The
stages form a chain, so the whole set sits inside a single `failSet P t K`,
which the budget caps at `f`. -/
theorem supp_le_of_unanimous {t : Seq (Lab P.n)} {v : Bool} {s : SpecState P.n}
    {j : ℕ} (hun : UnanimousInput P r v t)
    (hcall : ∀ id b, s.call id = some b → Lab.callG r id b ∈ t)
    (hF : s.F = failSet P t j) :
    (Finset.univ.filter (fun id => s.call id = some (!v) ∨ id ∈ s.F)).card
      ≤ P.f := by
  classical
  have hall : ∀ id ∈ Finset.univ.filter
      (fun id => s.call id = some (!v) ∨ id ∈ s.F), ∃ k, id ∈ failSet P t k := by
    intro id hid
    rcases (Finset.mem_filter.mp hid).2 with hc | hm
    · rcases hun id (!v) (hcall id (!v) hc) with heq | hnc
      · exact absurd heq (by cases v <;> simp)
      · unfold NeverCorrupted at hnc
        obtain ⟨k, hk⟩ := not_forall.mp hnc
        exact ⟨k, not_not.mp hk⟩
    · exact ⟨j, hF ▸ hm⟩
  obtain ⟨K, hK⟩ := exists_uniform_stage t _ hall
  exact le_trans (Finset.card_le_card (fun id hid => hK id hid))
    (failSet_card_le t K)

/-! ### The state-to-trace bridge -/

/-- **The bridge.** At every state of a genuine execution whose label list is
`labs` and whose trace is the external filter of `labs`, every pending input
has its `callG` event in the trace, and the corrupted set is the trace-level
fold at some stage. Both come from `CallInv` on the history `labs.take k`,
which the filter carries to the trace: it keeps every `fail` label, so the
fold is unchanged, and prefixes stay prefixes. -/
theorem trace_bridge {e : AlterSeq (SpecState P.n) (Lab P.n)}
    {labs : List (Lab P.n)} {t : Seq (Lab P.n)} {p : Lab P.n → Bool}
    (he : is_exec e (specInst P r))
    (h_map : e.trans.map Prod.fst = Seq.ofList labs)
    (hpfail : ∀ id : Fin P.n, p (.fail id) = true)
    (hpcall : ∀ (r' : ℕ) (id : Fin P.n) (b : Bool), p (.callG r' id b) = true)
    (h_t : Seq.ofList (labs.filter p) = t)
    {k : ℕ} {s : SpecState P.n} (hst : e.stateAt k = some s) :
    (∀ id b, s.call id = some b → Lab.callG r id b ∈ t) ∧
      ∃ j, s.F = failSet P t j := by
  have hI := is_exec_induction_labels (sys := specInst P r) (CallInv P r)
    (CallInv.initial P r) (fun pre s l μ s' hI hstep hs' => hI.step hstep hs')
    he k s hst
  rw [AlterSeq.labelsUpTo_eq_take h_map k] at hI
  obtain ⟨m, hm⟩ : ∃ m, ((labs.take k).filter p).length = m := ⟨_, rfl⟩
  refine ⟨fun id b h => ?_, ⟨m, ?_⟩⟩
  · rw [← h_t, Seq_mem_ofList, List.mem_filter]
    exact ⟨List.mem_of_mem_take (hI.call_src id b h), hpcall r id b⟩
  · rw [hI.F_eq, ← failSetL_filter hpfail (labs.take k),
      take_filter_eq_take p labs hm, ← h_t, failSet_ofList]

/-! ### The surviving bit stays alive -/

/-- **Under unanimous input `v`, the bit `v` is alive at every state.** The
only rule that could kill it is `bindUnset v`, whose D15 guard counts `f + 1`
supporters of `!v` — refuted by `supp_le_of_unanimous` at the very state where
the rule would fire. -/
theorem dead_notMem_of_unanimous {e : AlterSeq (SpecState P.n) (Lab P.n)}
    {t : Seq (Lab P.n)} {v : Bool} (he : is_exec e (specInst P r))
    (hbr : ∀ (k : ℕ) (s : SpecState P.n), e.stateAt k = some s →
      (∀ id b, s.call id = some b → Lab.callG r id b ∈ t) ∧
        ∃ j, s.F = failSet P t j)
    (hun : UnanimousInput P r v t) :
    ∀ k s, e.stateAt k = some s → v ∉ s.dead := by
  intro k
  induction k with
  | zero =>
    intro s hs
    obtain rfl : e.init = s := Option.some.inj hs
    rw [← he.2]
    simp [specInst, SpecState.initial]
  | succ k ih =>
    intro s hs
    obtain ⟨⟨l, s''⟩, h_get, h_snd⟩ : ∃ q : Lab P.n × SpecState P.n,
        e.trans.get? k = some q ∧ q.2 = s := by
      cases hg : e.trans.get? k with
      | none =>
        rw [show e.stateAt (k + 1) = (e.trans.get? k).map Prod.snd from rfl,
          hg] at hs
        exact absurd hs (by simp)
      | some q =>
        rw [show e.stateAt (k + 1) = (e.trans.get? k).map Prod.snd from rfl,
          hg] at hs
        exact ⟨q, rfl, Option.some.inj hs⟩
    obtain ⟨s₀, μ, h_state, h_step, h_supp⟩ := he.1 k l s'' h_get
    have hprev : v ∉ s₀.dead := ih s₀ h_state
    obtain ⟨hcall, j, hF⟩ := hbr k s₀ h_state
    subst h_snd
    cases h_step with
    | bindUnset b hq hw hd0 =>
      rw [PMF.mem_support_pure_iff] at h_supp
      subst h_supp
      have hbv : b ≠ v := by
        intro hb
        subst hb
        have := supp_le_of_unanimous hun hcall hF
        omega
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hbv h.symm, hprev⟩
    | fail id =>
      rw [PMF.mem_support_pure_iff] at h_supp
      subst h_supp
      rw [corrupt_dead]
      exact hprev
    | _ =>
      rw [PMF.mem_support_pure_iff] at h_supp
      subst h_supp
      exact hprev

/-! ### The return refutation -/

/-- Both D15 counts of a `C`-return: `f + 1` support at each bit. -/
private theorem retC_supp {s : SpecState P.n} {id : Fin P.n}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s (.retG r id .C) μ) (c : Bool) :
    P.f + 1 ≤
      (Finset.univ.filter (fun id' => s.call id' = some c ∨ id' ∈ s.F)).card :=
  match hstep with
  | .retC _ _ _ hwT hwF _ _ => by
    cases c with
    | false => exact hwF
    | true => exact hwT

/-- **Every return of a state where `v` is alive hands out `v`.** A
value-bearing return needs the other bit dead, and `v` is not; a `C`-return
needs `f + 1` support at both bits, and the dissenting one is capped by the
budget. -/
theorem retG_value_of_unanimous {t : Seq (Lab P.n)} {v : Bool}
    {s : SpecState P.n} {id : Fin P.n} {o : GbcaOut} {μ : PMF (SpecState P.n)}
    (hun : UnanimousInput P r v t)
    (hcall : ∀ id b, s.call id = some b → Lab.callG r id b ∈ t)
    (hF : ∃ j, s.F = failSet P t j) (hlive : v ∉ s.dead)
    (hstep : Step P r s (.retG r id o) μ) : outValue o = some v := by
  have key : ∀ w : Bool, (!w) ∈ s.dead → w = v := by
    intro w hdead
    by_contra hne
    have hflip : (!w) = v := by cases w <;> cases v <;> simp_all
    exact hlive (hflip ▸ hdead)
  cases o with
  | A w =>
    rw [key w (retG_value_guards hstep (outValue_A w)).2]
    rfl
  | B w =>
    rw [key w (retG_value_guards hstep (outValue_B w)).2]
    rfl
  | C =>
    exfalso
    obtain ⟨j, hFj⟩ := hF
    have h1 := retC_supp hstep (!v)
    have h2 := supp_le_of_unanimous hun hcall hFj
    omega

/-- Pulling a trace label back to an event of the witness execution. -/
private theorem event_of_mem_trace {e : AlterSeq (SpecState P.n) (Lab P.n)}
    {labs : List (Lab P.n)} {t : Seq (Lab P.n)} {p : Lab P.n → Bool}
    {l : Lab P.n} (h_map : e.trans.map Prod.fst = Seq.ofList labs)
    (h_t : Seq.ofList (labs.filter p) = t) (h_mem : l ∈ t) :
    ∃ k s', e.trans.get? k = some (l, s') := by
  rw [← h_t, Seq_mem_ofList, List.mem_filter] at h_mem
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h_mem.1
  have hget : (e.trans.get? k).map Prod.fst = labs[k]? := by
    rw [← Seq.map_get?, h_map, Seq.ofList_get?]
  rw [hk] at hget
  cases hg : e.trans.get? k with
  | none => rw [hg] at hget; exact absurd hget (by simp)
  | some q =>
    rw [hg] at hget
    simp only [Option.map_some, Option.some.injEq] at hget
    exact ⟨k, q.2, by rw [hg, ← hget]⟩

/-- **Validity (safety half) of the GBCA specification instance**: on every
trace in the support of every achievable trace distribution of
`GBCA.specInst P r`, unanimous honest input `v` forces every round-`r` return
to hand out `v`. The instance cannot invent the other bit, and cannot fall
back on `C`. -/
theorem specInst_validity (P : Params) (r : ℕ) (v : Bool) :
    ∀ D ∈ achievableTraceDists (specInst P r), ∀ t, D t ≠ 0 →
      UnanimousInput P r v t → ValidityTrace P r v t := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne hun
  rw [← h_D t] at h_ne
  obtain ⟨e, labs, h_exec, h_map, h_t⟩ :=
    exists_exec_of_traceProb_ne_zero_ord pe h_init t h_ne
  rw [Seq.ofList_filter] at h_t
  -- generalise the external-label filter to an opaque Boolean predicate
  obtain ⟨p, hpfail, hpcall, h_t⟩ : ∃ p : Lab P.n → Bool,
      (∀ id : Fin P.n, p (.fail id) = true) ∧
      (∀ (r' : ℕ) (id : Fin P.n) (b : Bool), p (.callG r' id b) = true) ∧
      Seq.ofList (labs.filter p) = t :=
    ⟨_, fun id => by simp, fun r' id b => by simp, h_t⟩
  have hbr : ∀ (k : ℕ) (s : SpecState P.n), e.stateAt k = some s →
      (∀ id b, s.call id = some b → Lab.callG r id b ∈ t) ∧
        ∃ j, s.F = failSet P t j :=
    fun k s hst => trace_bridge h_exec h_map hpfail hpcall h_t hst
  have halive := dead_notMem_of_unanimous h_exec hbr hun
  intro id o h_mem
  obtain ⟨k, s', h_get⟩ := event_of_mem_trace h_map h_t h_mem
  obtain ⟨s, μ, h_state, h_step, -⟩ := h_exec.1 k _ _ h_get
  obtain ⟨hcall, hF⟩ := hbr k s h_state
  exact retG_value_of_unanimous hun hcall hF (halive k s h_state) h_step

/-- **No `C`-return under unanimous honest input.** The `C`-return's D15
guards ask `f + 1` support at *both* bits; the dissenting one is capped by the
corruption budget. -/
theorem specInst_no_retC (P : Params) (r : ℕ) (v : Bool) :
    ∀ D ∈ achievableTraceDists (specInst P r), ∀ t, D t ≠ 0 →
      UnanimousInput P r v t → ∀ id : Fin P.n, Lab.retG r id .C ∉ t := by
  intro D hD t h_ne hun id h_mem
  have h := specInst_validity P r v D hD t h_ne hun id .C h_mem
  simp at h

/-! ### Mechanical axiom firewall

No headline may acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.GBCA.retG_value_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms retG_value_agree

/-- info: 'PLTS.ABA.GBCA.specInst_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specInst_binding

/-- info: 'PLTS.ABA.GBCA.dead_card_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dead_card_le_one

/-- info: 'PLTS.ABA.GBCA.specInst_validity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specInst_validity

/-- info: 'PLTS.ABA.GBCA.specInst_no_retC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specInst_no_retC

end GBCA
end ABA
end PLTS
