/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCASpec
import Leslie2Protocols.Framework.TraceSupport

/-!
# Binding and graded agreement of the GBCA specification instance

Binding is the promise a Graded Binding Crusader Agreement instance makes about
its *future*: there is a bit the instance will never hand out, in this run or in
any extension of it. On the specification state that promise is a field rather
than a theorem. `SpecState.dead : Finset Bool` is the set of bits the instance
can no longer hand out; the value-bearing returns refuse a dead bit and demand
that the other bit be dead, and the `C`-return demands that some bit be dead.

Everything below rests on one fact: `dead` only grows. The single writer is the
internal `bindUnset`, which inserts, and `corrupt` does not touch the field —
so `Step.dead_mono` holds rule by rule, and `is_exec_stable` lifts it to whole
executions (`dead_mem_stable`, `dead_subset_of_le`). Binding is therefore
structural: a bit killed at any point of a run is killed at every later point,
and a guard reading `∉ dead` can never be re-enabled.

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
* `retC_dead_nonempty` — the **Graded Binding witness**. After a `C`-return,
  `dead` is nonempty in every later state of the execution. A member of `dead`
  is a bit no non-faulty party can be handed at grade `≥ 1` in any extension,
  which is ABDY22's Graded Binding clause; the witness is produced at the
  `C`-return and survives because `dead` never shrinks.

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

@[simp] theorem corrupt_dead (P : Params) (s : SpecState P.n) (id : Fin P.n) :
    (s.corrupt P id).dead = s.dead := by
  unfold SpecState.corrupt; split <;> rfl

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

/-- **The exclusion set is monotone along a run.** -/
theorem dead_subset_of_le {e : AlterSeq (SpecState P.n) (Lab P.n)}
    (he : is_exec e (specInst P r)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂) :
    s₁.dead ⊆ s₂.dead :=
  fun _ hb => dead_mem_stable he hk hst₁ hst₂ hb

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

/-- **The Graded Binding witness.** A `C`-return leaves the exclusion set
nonempty in every later state of the execution: the bit it kills is a bit no
extension of the run can ever hand out. -/
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

/-! ### Mechanical axiom firewall

Neither headline may acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.GBCA.retG_value_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms retG_value_agree

/-- info: 'PLTS.ABA.GBCA.specInst_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specInst_binding

end GBCA
end ABA
end PLTS
