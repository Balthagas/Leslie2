/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Simulation.Trace
import MyMathlibProject.Simulation.Equivalences
import MyMathlibProject.Construction.DistTrace
import MyMathlibProject.Expansion.TraceProb

/-!
# Trace soundness of weak and forward probabilistic simulation

`StrongProbabilisticSimulation.achievableTraceDists_subset` (in `SimulationTrace`)
gives trace soundness for *strong* simulation. This file derives the same for
*weak* and *forward* probabilistic simulation, now that both the weak-closure and
distribution-monad constructions are known to preserve trace distributions
(`weakClosure_traceProb_eq`, `dist_traceProb_eq`).

Each is a short corollary: a weak (resp. forward) simulation of `sys_C` by
`sys_A` is *the same data* as a strong simulation of `sys_C` by `sys_A^w` (resp.
`𝒟(sys_A^w)`) — see `weakProbabilisticSimulation_iff_strong_weakClosure` and
`probabilisticForwardSimulation_iff_strong_dist_weakClosure` — and those
constructions have the same achievable trace distributions as `sys_A`.
-/

open Stream'

namespace PLTS

variable {State_C State_A Label : Type} [Silent Label]

/-- **Weak probabilistic simulation preserves achievable trace distributions**
(soundness): if `sys_C` is weakly simulated by `sys_A`, then every trace
distribution achievable by `sys_C` is achievable by `sys_A`. -/
theorem WeakProbabilisticSimulation.achievableTraceDists_subset
    {sys_C : System State_C Label} {sys_A : System State_A Label}
    {R : State_C → State_A → Prop}
    (sim : WeakProbabilisticSimulation sys_C sys_A R) :
    achievableTraceDists sys_C ⊆ achievableTraceDists sys_A := by
  -- A weak simulation is a strong simulation into `sys_A^w`, and `·^w` preserves traces.
  rw [weakClosure_traceProb_eq sys_A]
  exact ((weakProbabilisticSimulation_iff_strong_weakClosure sys_C sys_A R).mp
    sim).achievableTraceDists_subset

/-- **Probabilistic forward simulation preserves achievable trace distributions**
(soundness): if `sys_C` is forward-simulated by `sys_A`, then every trace
distribution achievable by `sys_C` is achievable by `sys_A`. -/
theorem ProbabilisticForwardSimulation.achievableTraceDists_subset
    {sys_C : System State_C Label} {sys_A : System State_A Label}
    {R : State_C → PMF State_A → Prop}
    (sim : ProbabilisticForwardSimulation sys_C sys_A R) :
    achievableTraceDists sys_C ⊆ achievableTraceDists sys_A := by
  -- A forward simulation is a strong simulation into `𝒟(sys_A^w)`; both `·^w` and `𝒟(·)`
  -- preserve traces.
  rw [weakClosure_traceProb_eq sys_A, dist_traceProb_eq (sys_A^w)]
  exact ((probabilisticForwardSimulation_iff_strong_dist_weakClosure sys_C sys_A R).mp
    sim).achievableTraceDists_subset

end PLTS
