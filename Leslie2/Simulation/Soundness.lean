/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Simulation.Trace
import Leslie2.Simulation.Equivalences
import Leslie2.WeakClosure.TraceProb

/-!
# Trace soundness of strong and weak probabilistic simulation

The two non-headline soundness results:

* `StrongProbabilisticSimulation.achievableTraceDists_subset` — strong simulation preserves
  achievable trace distributions, a corollary of the coupling lift
  `simProd_achievableTraceDists_superset` (in `Simulation/Trace.lean`) pushed forward along the
  second projection.
* `WeakProbabilisticSimulation.achievableTraceDists_subset` — the same for *weak* simulation, since
  a weak simulation of `sys_C` by `sys_A` is the same data as a strong simulation of `sys_C` by
  `sys_A^w`, and `·^w` preserves traces (`weakClosure_traceProb_eq`).

The headline `ProbabilisticForwardSimulation.achievableTraceDists_subset` (which builds on strong
soundness through the distribution-monad lift) lives with the other main results in `Results.lean`.
-/

open Stream'

namespace PLTS

variable {State_C State_A Label : Type} [Silent Label]

/-- **Strong simulation preserves achievable trace distributions** (soundness). -/
theorem StrongProbabilisticSimulation.achievableTraceDists_subset
    {sys_C : System State_C Label} {sys_A : System State_A Label}
    {R : State_C → State_A → Prop}
    (sim : StrongProbabilisticSimulation sys_C sys_A R) :
    achievableTraceDists sys_C ⊆ achievableTraceDists sys_A :=
  (simProd_achievableTraceDists_superset sim).trans
    (achievableTraceDists_map Prod.snd rfl (fun _ _ _ h => h.2.1))

/-- **Weak probabilistic simulation preserves achievable trace distributions** (soundness): if
`sys_C` is weakly simulated by `sys_A`, then every trace distribution achievable by `sys_C` is
achievable by `sys_A`. -/
theorem WeakProbabilisticSimulation.achievableTraceDists_subset
    {sys_C : System State_C Label} {sys_A : System State_A Label}
    {R : State_C → State_A → Prop}
    (sim : WeakProbabilisticSimulation sys_C sys_A R) :
    achievableTraceDists sys_C ⊆ achievableTraceDists sys_A := by
  -- A weak simulation is a strong simulation into `sys_A^w`, and `·^w` preserves traces.
  rw [weakClosure_traceProb_eq sys_A]
  exact ((weakProbabilisticSimulation_iff_strong_weakClosure sys_C sys_A R).mp
    sim).achievableTraceDists_subset

end PLTS
