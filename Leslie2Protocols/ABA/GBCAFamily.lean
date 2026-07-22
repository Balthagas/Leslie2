/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCASim
import Leslie2Protocols.Framework.FamilySim

/-!
# The GBCA family refinement

The per-instance GBCA refinement (`GBCA.implRefines`, `ABA/GBCASim.lean`) lifts
to the ℕ-indexed instance families via the congruence
`ForwardSimulation.family` (`Framework/FamilySim.lean`):

* `GBCA.implFailAct` / `GBCA.implFamily` — the implementation-side broadcast
  transform and family, mirroring `GBCA.failAct` / `GBCA.specFamily`;
* `GBCA.instRel_corrupt` — broadcast compatibility of the simulation relation:
  the two `corrupt` functions share the guard `id ∉ F ∧ |F| < f`, and `instRel`
  aligns the `F`s, so a synchronized corruption preserves the relation. This is
  proved directly (not through `implRefines`, whose `fail` case only yields an
  existential match);
* `GBCA.familyRefines` — the headline: the implementation family
  probabilistically forward-simulates the specification family along the Dirac
  lift of the pointwise instance relation, by `ForwardSimulation.toProbabilistic`
  on the lifted forward simulation (both families are LTS).
-/

namespace PLTS
namespace ABA
namespace GBCA

variable {P : Params}

/-- The broadcast transform of the GBCA implementation family: corruption on
`fail id`, identity on every other label (the concrete counterpart of
`GBCA.failAct`). -/
def implFailAct (P : Params) : Lab P.n → ImplState P.n → ImplState P.n
  | .fail id, s => s.corrupt P id
  | _, s => s

/-- The ℕ-indexed family of GBCA implementation instances. -/
noncomputable def implFamily (P : Params) :
    System (ℕ → ImplState P.n) (Lab P.n) :=
  System.family (implInst P) Lab.gbcaRound Lab.isFail (implFailAct P)

/-- The GBCA implementation family is an LTS. -/
theorem implFamily_isLTS (P : Params) : (implFamily P).IsLTS :=
  System.family_isLTS (implInst_isLTS P) _ _ _

/-! ### Broadcast compatibility of the simulation relation -/

private theorem specCorrupt_call (t : SpecState P.n) (id : Fin P.n) :
    (t.corrupt P id).call = t.call := by
  unfold SpecState.corrupt; split <;> rfl

private theorem specCorrupt_ret (t : SpecState P.n) (id : Fin P.n) :
    (t.corrupt P id).ret = t.ret := by
  unfold SpecState.corrupt; split <;> rfl

private theorem specCorrupt_bind (t : SpecState P.n) (id : Fin P.n) :
    (t.corrupt P id).bind = t.bind := by
  unfold SpecState.corrupt; split <;> rfl

private theorem specCorrupt_grade (t : SpecState P.n) (id : Fin P.n) :
    (t.corrupt P id).grade = t.grade := by
  unfold SpecState.corrupt; split <;> rfl

/-- The two `corrupt` functions stay in lockstep on aligned corrupted sets. -/
private theorem corrupt_F_lockstep {t : SpecState P.n} {s : ImplState P.n}
    (hF : t.F = s.F) (id : Fin P.n) :
    (t.corrupt P id).F = (s.corrupt P id).F := by
  unfold SpecState.corrupt ImplState.corrupt
  by_cases hc : id ∉ s.F ∧ s.F.card < P.f
  · rw [if_pos (by rw [hF]; exact hc), if_pos hc]
    simp [hF]
  · rw [if_neg (by rw [hF]; exact hc), if_neg hc]
    exact hF

/-- **Broadcast compatibility**: `instRel` is preserved by the synchronized
corruption of both sides. The two `corrupt`s share the guard
`id ∉ F ∧ |F| < f` and `instRel` aligns the `F`s, so the `if`-conditions
agree; every other field is untouched by corruption. -/
theorem instRel_corrupt (P : Params) (r : ℕ) (id : Fin P.n)
    {x : ImplState P.n} {y : SpecState P.n} (h : instRel P r x y) :
    instRel P r (x.corrupt P id) (y.corrupt P id) := by
  have hR : InstRel P x y := h
  exact
    { inv := hR.inv.step (ImplStep.fail (r := r) x id)
        (by rw [PMF.mem_support_pure_iff])
      call_eq := fun k => by
        rw [specCorrupt_call, ImplState.corrupt_proc]
        exact hR.call_eq k
      ret_eq := fun k => by
        rw [specCorrupt_ret, ImplState.corrupt_proc]
        exact hR.ret_eq k
      bind_eq := by
        rw [specCorrupt_bind, ImplState.corrupt_bound]
        exact hR.bind_eq
      grade_eq := by
        rw [specCorrupt_grade, ImplState.corrupt_grade]
        exact hR.grade_eq
      F_eq := corrupt_F_lockstep hR.F_eq id }

/-- `instRel` is compatible with the family broadcast transforms: the `hglob`
hypothesis of `ForwardSimulation.family` for the GBCA families (only `fail`
labels are global). -/
theorem instRel_failAct (P : Params) :
    ∀ l : Lab P.n, Lab.isFail l → ∀ (r : ℕ) (x : ImplState P.n)
      (y : SpecState P.n), instRel P r x y →
      instRel P r (implFailAct P l x) (failAct P l y) := by
  intro l hl r x y h
  cases l
  case fail id => exact instRel_corrupt P r id h
  all_goals exact hl.elim

/-! ### The family refinement -/

/-- **The GBCA family refinement**: the ℕ-indexed implementation family
probabilistically forward-simulates the specification family along the Dirac
lift of the pointwise instance relation. -/
theorem familyRefines (P : Params) :
    ProbabilisticForwardSimulation (implFamily P) (specFamily P)
      (diracRel fun s t => ∀ r, instRel P r (s r) (t r)) :=
  ForwardSimulation.toProbabilistic (implFamily_isLTS P) (specFamily_isLTS P)
    (fun r => instRel_init P r)
    (ForwardSimulation.family Lab.gbcaRound Lab.isFail (implFailAct P)
      (failAct P) (implRefines P) (instRel_failAct P))

end GBCA
end ABA
end PLTS
