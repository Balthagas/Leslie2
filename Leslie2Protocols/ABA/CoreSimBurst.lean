/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.CoreSimRel
import Leslie2.Weak.WeakTransition

/-!
# Abstract-twin burst machinery

Pure `ABA.spec`-side weak-τ lemmas, with no composed-side/`Inv`/`Abs`
reasoning: given an abstract `SpecState`, these package the internal
`SpecStep` rules (`Spec.lean`) into the `weakTau`/`weakStep` chains
(`WeakTransition.lean`) that the simulation rows (`CoreSim.lean`) consume.
Every lemma here is standalone and never mentions `Inv`/`Abs`/the concrete
`(g, c, w)` state.

* `decide_step`: `SpecStep.decide` as a one-step `weakTau` burst, the τ-tail
  that leads the first visible return.
* `weakStep_of_burst_then_step`: a `weakTau` burst followed by a genuine
  visible step is a `weakStep`.
-/

namespace PLTS
namespace ABA

variable {P : Params}

/-! ### The decide burst -/

/-- `SpecStep.decide` as a `weakTau` burst. The rule is Dirac, so the burst is
a single step: `val` takes `b` and the mode returns to `Mode.idle`. -/
theorem decide_step {a : SpecState P.n} {b : Bool} (hv : a.val = none)
    (hs : SuppOK P a b) (hm : a.mode ≠ .dead) :
    weakTau (spec P) (PMF.pure a)
      (PMF.pure { a with val := some b, mode := .idle }) :=
  weakTau_of_step rfl (SpecStep.decide a b hv hs hm)

/-! ### Convenience: closing a burst with a visible step -/

/-- A `weakTau` burst followed by a genuine (possibly visible) single step is a `weakStep`: the
burst is the leading τ-closure, the step is the middle hyper-step (`hyperStep_pure_of_step`), and
the trailing τ-closure is the trivial reflexivity at the final state. -/
theorem weakStep_of_burst_then_step {a a' a'' : SpecState P.n} {l : Lab P.n}
    (hburst : weakTau (spec P) (PMF.pure a) (PMF.pure a'))
    (hstep : SpecStep P a' l (PMF.pure a'')) :
    weakStep (spec P) (PMF.pure a) l (PMF.pure a'') :=
  ⟨PMF.pure a', PMF.pure a'', hburst, hyperStep_pure_of_step hstep, weakTau_refl _ _⟩

end ABA
end PLTS
