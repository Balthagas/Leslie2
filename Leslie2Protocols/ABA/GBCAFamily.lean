/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCASim
import Leslie2Protocols.Framework.FamilySim

/-!
# Broadcast compatibility of the GBCA instance refinement

`GBCA.instRel`, the per-instance relation of `GBCA.implRefines`
(`ABA/GBCASim.lean`), is preserved by the synchronized corruption of both
sides: the two `corrupt` functions share the guard `id ∉ F ∧ |F| < f` and
`instRel` aligns the `F`s, so a `fail` broadcast leaves every instance related.
This is the broadcast ingredient a family lifting of the refinement consumes,
and it is proved directly rather than through `implRefines`, whose `fail` case
only yields an existential match. Its consumer is the round subsystem's family
lifting (`ABA/GBCASub.lean`).

`Framework/FamilySim.lean` is imported here for the downstream tree: the family
congruence `ForwardSimulation.family` reaches `ABA/GBCASub.lean` and
`ABA/LayeredSpec.lean` along this file.
-/

namespace PLTS
namespace ABA
namespace GBCA

variable {P : Params}

/-! ### Broadcast compatibility of the simulation relation

The spec-side corruption projections (`corrupt_call`/`corrupt_ret`/`corrupt_dead`/
`corrupt_grade`) come from `GBCASpec.lean`. -/

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
        rw [corrupt_call, ImplState.corrupt_proc]
        exact hR.call_eq k
      ret_eq := fun k => by
        rw [corrupt_ret, ImplState.corrupt_proc]
        exact hR.ret_eq k
      F_eq := corrupt_F_lockstep hR.F_eq id
      dead_cert := fun b hb => by
        rw [corrupt_dead] at hb
        exact DeadCert.mono
          (fun i j m hm => by rw [ImplState.corrupt_recv]; exact hm)
          (fun j w hw => by rw [ImplState.corrupt_proc]; exact hw)
          (ImplState.corrupt_F_subset x id)
          (hR.dead_cert b hb)
      gradeA_ev := fun hg => by
        rw [corrupt_grade] at hg
        obtain ⟨v, i, hi⟩ := hR.gradeA_ev hg
        exact ⟨v, i, by rw [ImplState.corrupt_recvCount]; exact hi⟩
      gradeC_ev := fun hg => by
        rw [corrupt_grade] at hg
        obtain ⟨i, hi⟩ := hR.gradeC_ev hg
        exact ⟨i, by rw [ImplState.corrupt_recvCount]; exact hi⟩ }

end GBCA
end ABA
end PLTS
