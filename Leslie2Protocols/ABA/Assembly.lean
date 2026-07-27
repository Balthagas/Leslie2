/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.CoreProc
import Leslie2Protocols.ABA.GBCAProc
import Leslie2Protocols.ABA.Main

/-!
# The assembled hybrid

The hybrid of `Hybrid.lean` with every implemented layer replaced by its
per-process presentation. `ABA.hybridPerProc` is a composition of one automaton
per process per layer: the ABA coordinator is `ABA.perProcCore`, each round of
GBCA is `GBCA.perProcInst`, and the only box that is not a process is the
coin oracle `WCC.specFamily`, which stays at specification level.

Two definitions carry the per-process presentation up to the family level:

* `ABA.perProcFailAct` — the corruption broadcast on a tuple of per-process
  nodes, applied to every node's own copy of the corrupted set;
* `ABA.perProcGBCAFamily` — the ℕ-indexed family of per-process GBCA
  instances, the per-process counterpart of `GBCA.implFamily`.

The equality of achievable trace distributions (`ABA.hybridPerProc_atd`) is
assembled from the layers' own equivalences by the process-algebraic
congruences alone, one layer at a time:

* the two per-instance GBCA matchings (`GBCA.perProcRefines`,
  `GBCA.implRefinesPerProc`) lift to the families through
  `ForwardSimulation.family`, whose broadcast hypothesis is
  `GBCA.unpack_corrupt`; both families are LTS, so
  `ForwardSimulation.toProbabilistic` turns each into a probabilistic forward
  simulation;
* the two core matchings (`ABA.perProcCore_sim`, `ABA.core_sim`) are already
  between LTS and pass through the same bridge;
* each of the four simulations is then transported into the composition by the
  precongruences for `parallel` and `abstract`, and soundness turns it into a
  trace-distribution inclusion. The four inclusions chain by transitivity of
  `⊆`, so no transitivity of simulations is involved.

The coin oracle is never simulated: it is the fixed context of every
precongruence step, which is what lets the argument go through even though it
is the one component that is not an LTS.

Safety transfers verbatim: `ABA.hybridPerProc_safe` is `ABA.main` read along
the trace-distribution equality.
-/

namespace PLTS
namespace ABA

/-! ### The mirror of `parallel_right`

`ProbabilisticForwardSimulation.parallel_right` (Result 3) refines the component
that sits on the *left* of a `System.parallel`. The mirror statement — the
context on the left, the refined component on the right — is that result
conjugated with the coordinate exchange, itself a strong functional matching in
both directions (`System.parallel_swap_step`). Only the trace-distribution
inclusion is recorded: it is all the assembly consumes, and it spares the
statement the two conjugations of the composite relation. -/

section ParallelLeft

variable {State_C State_A State_B Label : Type} [Silent Label]
  {sys_C : System State_C Label} {sys_A : System State_A Label}
  {R : State_C → PMF State_A → Prop}

/-- Coordinate exchange as a probabilistic forward simulation. -/
private theorem swapSim (sys₁ : System State_C Label) (sys₂ : System State_B Label) :
    ProbabilisticForwardSimulation (sys₁.parallel sys₂) (sys₂.parallel sys₁)
      (fun s ν => ν = PMF.pure (Prod.swap s)) :=
  ProbabilisticForwardSimulation.ofStrongFunctional Prod.swap rfl
    (System.parallel_swap_step sys₁ sys₂)

/-- **Precongruence with the context on the left**, in trace-distribution form:
refining the second component of a parallel composition under an abstraction can
only shrink the set of achievable trace distributions. -/
theorem atd_parallel_left (sim : ProbabilisticForwardSimulation sys_C sys_A R)
    (sys_B : System State_B Label) (L : Set Label) :
    achievableTraceDists ((sys_B.parallel sys_C).abstract L) ⊆
      achievableTraceDists ((sys_B.parallel sys_A).abstract L) :=
  Set.Subset.trans ((swapSim sys_B sys_C).abstract L).achievableTraceDists_subset
    (Set.Subset.trans ((sim.parallel_right sys_B).abstract L).achievableTraceDists_subset
      ((swapSim sys_A sys_B).abstract L).achievableTraceDists_subset)

end ParallelLeft

/-! ### The per-process GBCA family -/

/-- The corruption broadcast of the per-process GBCA presentation: every node
applies the transform to its own copy of the corrupted set, which is what keeps
the copies equal (the per-process counterpart of `GBCA.implFailAct`). -/
def perProcFailAct (P : Params) :
    Lab P.n → (∀ _ : Fin P.n, GBCA.ProcNode P.n) → (∀ _ : Fin P.n, GBCA.ProcNode P.n)
  | .fail id, p => fun j => GBCA.ProcNode.corrupt P id (p j)
  | _, p => p

/-- The ℕ-indexed family of per-process GBCA instances. -/
noncomputable def perProcGBCAFamily (P : Params) :
    System (ℕ → ∀ _ : Fin P.n, GBCA.ProcNode P.n) (Lab P.n) :=
  System.family (fun r => GBCA.perProcInst P r) Lab.gbcaRound Lab.isFail (perProcFailAct P)

/-- The per-process GBCA family is an LTS. -/
theorem perProcGBCAFamily_isLTS (P : Params) : (perProcGBCAFamily P).IsLTS :=
  System.family_isLTS (GBCA.perProcInst_isLTS P) _ _ _

/-- The packing map is compatible with the two families' broadcast transforms:
the `hglob` hypothesis of `ForwardSimulation.family`, which is
`GBCA.unpack_corrupt` on the only global label. -/
theorem unpack_failAct (P : Params) :
    ∀ l : Lab P.n, Lab.isFail l → ∀ (p : ∀ _ : Fin P.n, GBCA.ProcNode P.n)
      (q : GBCA.ImplState P.n), p = GBCA.unpack q →
      perProcFailAct P l p = GBCA.unpack (GBCA.implFailAct P l q) := by
  rintro l hl p q rfl
  cases l
  case fail id => exact (GBCA.unpack_corrupt P q id).symm
  all_goals exact hl.elim

/-- **The per-process GBCA family refines the monolithic one.** The per-instance
matching `GBCA.perProcRefines` lifted round by round: the family relation is the
graph of the pointwise packing map `fun t r => GBCA.unpack (t r)`, silent and
owned labels are matched instance by instance, and the corruption broadcast by
`ABA.unpack_failAct`. Both families are LTS, so the lifted matching is a
probabilistic forward simulation. -/
theorem perProcGBCAFamily_refines (P : Params) :
    ProbabilisticForwardSimulation (perProcGBCAFamily P) (GBCA.implFamily P)
      (diracRel fun p q => ∀ r, p r = GBCA.unpack (q r)) :=
  ForwardSimulation.toProbabilistic (perProcGBCAFamily_isLTS P) (GBCA.implFamily_isLTS P)
    (fun _ => rfl)
    (ForwardSimulation.family Lab.gbcaRound Lab.isFail (perProcFailAct P) (GBCA.implFailAct P)
      (GBCA.perProcRefines P) (fun l hl _ => unpack_failAct P l hl))

/-- **The monolithic GBCA family refines the per-process one**, along the same
relation read the other way round: `GBCA.implRefinesPerProc` lifted by the same
congruence, with the same broadcast compatibility. -/
theorem implGBCAFamily_refines (P : Params) :
    ProbabilisticForwardSimulation (GBCA.implFamily P) (perProcGBCAFamily P)
      (diracRel fun q p => ∀ r, p r = GBCA.unpack (q r)) :=
  ForwardSimulation.toProbabilistic (GBCA.implFamily_isLTS P) (perProcGBCAFamily_isLTS P)
    (fun _ => rfl)
    (ForwardSimulation.family Lab.gbcaRound Lab.isFail (GBCA.implFailAct P) (perProcFailAct P)
      (GBCA.implRefinesPerProc P) (fun l hl _ q p h => unpack_failAct P l hl p q h))

/-! ### The core layer -/

/-- The per-process core refines `ABA.core` — the probabilistic reading of
`ABA.perProcCore_sim`, both systems being LTS. -/
theorem perProcCore_refines (P : Params) :
    ProbabilisticForwardSimulation (perProcCore P) (core P) (diracRel (CoreRel P)) :=
  ForwardSimulation.toProbabilistic (perProcCore_isLTS P) (core_isLTS P)
    (coreRel_init P) (perProcCore_sim P)

/-- `ABA.core` refines the per-process core — the probabilistic reading of
`ABA.core_sim`. -/
theorem core_refines_perProc (P : Params) :
    ProbabilisticForwardSimulation (core P) (perProcCore P)
      (diracRel fun s q => CoreRel P q s) :=
  ForwardSimulation.toProbabilistic (core_isLTS P) (perProcCore_isLTS P)
    (coreRel_init P) (core_sim P)

/-! ### The assembled hybrid -/

/-- The per-process composition context: the per-process ABA coordinator
alongside the spec-level WCC family (the per-process counterpart of
`ABA.context`). -/
noncomputable def perProcContext (P : Params) :
    System ((∀ _ : Fin P.n, CoreNode P.n) × (ℕ → WCC.SpecState P.n)) (Lab P.n) :=
  (perProcCore P).parallel (WCC.specFamily P)

/-- **The assembled hybrid**: every implemented layer a composition of
per-process automata, the coin oracle the one centralized box. -/
noncomputable def hybridPerProc (P : Params) :
    System ((ℕ → ∀ _ : Fin P.n, GBCA.ProcNode P.n) ×
      ((∀ _ : Fin P.n, CoreNode P.n) × (ℕ → WCC.SpecState P.n))) (Lab P.n) :=
  ((perProcGBCAFamily P).parallel (perProcContext P)).abstract (Lab.hiddenAPI P.n)

/-- **The assembly corollary.** The assembled hybrid and the hybrid of
`Hybrid.lean` achieve exactly the same trace distributions: writing each
implemented layer as one automaton per process, communicating only over that
layer's own network labels, neither adds nor removes observable behaviour. The
four inclusions are the two layers' equivalences transported by the
precongruences and chained by transitivity of `⊆`. -/
theorem hybridPerProc_atd (P : Params) :
    achievableTraceDists (hybridPerProc P) = achievableTraceDists (hybridImpl P) := by
  -- The intermediate system: GBCA monolithic again, the core still per-process.
  have h1 : achievableTraceDists (hybridPerProc P) ⊆
      achievableTraceDists
        (((GBCA.implFamily P).parallel (perProcContext P)).abstract (Lab.hiddenAPI P.n)) :=
    (((perProcGBCAFamily_refines P).parallel_right
      (perProcContext P)).abstract (Lab.hiddenAPI P.n)).achievableTraceDists_subset
  have h2 : achievableTraceDists
        (((GBCA.implFamily P).parallel (perProcContext P)).abstract (Lab.hiddenAPI P.n)) ⊆
      achievableTraceDists (hybridImpl P) :=
    atd_parallel_left ((perProcCore_refines P).parallel_right (WCC.specFamily P))
      (GBCA.implFamily P) (Lab.hiddenAPI P.n)
  have h3 : achievableTraceDists (hybridImpl P) ⊆
      achievableTraceDists
        (((GBCA.implFamily P).parallel (perProcContext P)).abstract (Lab.hiddenAPI P.n)) :=
    atd_parallel_left ((core_refines_perProc P).parallel_right (WCC.specFamily P))
      (GBCA.implFamily P) (Lab.hiddenAPI P.n)
  have h4 : achievableTraceDists
        (((GBCA.implFamily P).parallel (perProcContext P)).abstract (Lab.hiddenAPI P.n)) ⊆
      achievableTraceDists (hybridPerProc P) :=
    (((implGBCAFamily_refines P).parallel_right
      (perProcContext P)).abstract (Lab.hiddenAPI P.n)).achievableTraceDists_subset
  exact Set.Subset.antisymm (Set.Subset.trans h1 h2) (Set.Subset.trans h3 h4)

/-- **Safety of the assembled hybrid** — `ABA.main` read along the
trace-distribution equality: every positive-probability trace of the fully
per-process composition satisfies Validity and Agreement. The scope of the
claim is that of `ABA.main`: safety only, with WCC held at specification
level. -/
theorem hybridPerProc_safe (P : Params) :
    ∀ D ∈ achievableTraceDists (hybridPerProc P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace t := by
  rw [hybridPerProc_atd]
  exact main P

/-! ### Mechanical axiom firewall

The assembly must never acquire a `sorryAx` dependence; both headline theorems
are pinned to the clean axiom list. -/

/-- info: 'PLTS.ABA.hybridPerProc_atd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hybridPerProc_atd

/-- info: 'PLTS.ABA.hybridPerProc_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hybridPerProc_safe

end ABA
end PLTS
