/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.ExpandSched

/-!
# Trace-distribution preservation of the weak closure (the hard direction)

This file assembles the unfolding-algorithm fidelity results into
`weakClosure_traceProb_superset`: every trace distribution achievable by `sys^w`
is achievable by `sys`. It is the downstream home of the theorem (and the
resulting equality `weakClosure_traceProb_eq`), since the proof needs the
unfolding machinery (`Expand`/`ExpandTrace`/`ExpandProbOf`/`ExpandSched`), which
imports `WeakConstruction` where the easy direction lives.

The core is `traceProb_expandSched_eq`: running the concrete scheduler
`expandSched ws` on `sys` reproduces the trace distribution of `ws` on `sys^w`.
-/

open Stream'

namespace PLTS

variable {State Label : Type} [Silent Label] {sys : System State Label}

/-! ### Overview

**The unfolding scheduler reproduces the trace distribution.** For every
finite trace `τ`, the concrete execution `⟨pure init, expandSched ws⟩` on `sys`
and the abstract execution `⟨pure init, ws⟩` on `sys^w` assign `τ` the same
probability.

PROOF (config-level, `τ ≠ []`; `τ = []` is `1 = 1`). The two fidelities reduce
each side to a `reachProb` sum over configurations:

* **abstract** = `∑ reachProb c` over **entry** configs
  `ABS(τ) := { c | c.e'.trans = nil ∧ IsTight c.we ∧ trace c.we = τ }`
  (via `probOf_eq_reachProb_we` + reindexing the tight-`we` `traceProb` sum);
* **concrete** = `∑ reachProb c` over **arrival** configs
  `CON(τ) := { c | c.e'.trans ≠ nil ∧ IsTight (concat c) ∧ trace (concat c) = τ }`
  (via `probOf_eq_reachArr` + reindexing the tight-`e` `traceProb` sum).

These are the *same external weak step* measured one moment apart: a `CON` config
is at the arrival just after the external label `l` is emitted (segment
`e' = preτ·l`, before the post-τ run), and the corresponding `ABS` config is
after that weak step fully commits (`e' = nil`, post-τ done). The only thing
between them is the post-τ run plus the OUTER commit, which changes `last(e)` but
not the external trace. The masses are equal — an **equality**, not just `≤` —
because the witness's post-τ halts almost surely (`Realises` clause (a),
`∑ haltMass = 1`); there is no divergence within a single witness run. So
`ABS(τ) = CON(τ)` by a post-τ `reachProb` flow-conservation (the
`reachDep_sum_le` style, but over the post-τ sojourn and with equality). -/

/-! ### Base-case helpers (`τ = []`): a tight, empty-trace execution has no transitions -/

open Classical in
/-- A tight label list with empty external trace is itself empty: if filtering out the
internal labels of `labs` yields `[]` and `labs` does not end internally, then `labs = []`. -/
private theorem traceTightLabs_nil_imp (labs : List Label)
    (h : sys.traceTightLabs Seq.nil labs) : labs = [] := by
  obtain ⟨hfilter, hlast⟩ := h
  rcases List.eq_nil_or_concat labs with h0 | ⟨ys, y, rfl⟩
  · exact h0
  · exfalso
    rw [List.concat_eq_append] at hfilter hlast
    have hgl : (ys ++ [y]).getLast? = some y := by simp
    have hyne : ¬ y = Silent.τ := hlast y hgl
    have hofl : (Seq.ofList (ys ++ [y]) : Seq Label)
        = (Seq.ofList ys).append (Seq.cons y Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    rw [hofl,
        Stream'.Seq.filter_append (fun l => ¬ (l = Silent.τ)) (Seq.ofList ys)
          (Seq.cons y Seq.nil) (Stream'.Seq.terminates_ofList ys),
        Stream'.Seq.filter_cons_pos (p := fun l => ¬ (l = Silent.τ)) y Seq.nil hyne] at hfilter
    exact Stream'.Seq.cons_ne_nil (append_eq_nil hfilter).2

/-- A terminating, trace-tight execution with empty external trace has no transitions. -/
private theorem trans_nil_of_trace_nil_tight (e : AlterSeq State Label)
    (h : e.trans.Terminates) (htr : sys.trace e = Seq.nil) (htight : sys.IsTight e) :
    e.trans = Seq.nil := by
  have htt : sys.traceTightLabs Seq.nil ((e.trans.toList h).map Prod.fst) :=
    (sys.tight_iff Seq.nil e h).mp ⟨htr, htight⟩
  have hlabs_nil : (e.trans.toList h).map Prod.fst = [] := traceTightLabs_nil_imp _ htt
  have htoList_nil : e.trans.toList h = [] := List.map_eq_nil_iff.mp hlabs_nil
  have hofl := Stream'.Seq.ofList_toList e.trans h
  rw [htoList_nil, Stream'.Seq.ofList_nil] at hofl
  exact hofl.symm

/-! ### The two config families and the generic sigma-reindexings -/

/-- **Abstract reindex.** A dependent sum over (tight `we`-execution `e`, entry config `c`
with `c.we = e`) regroups to a single sum over the entry configs `c` (which determine `e`). -/
private theorem tsum_reindex_we (ws : Scheduler sys^w) (Q : AlterSeq State Label → Prop) :
    (∑' e : {e : AlterSeq State Label // Q e},
        ∑' c : {c : Config sys // c.we = e.1 ∧ c.e'.trans = Seq.nil}, reachProb ws c.1)
      = ∑' c : {c : Config sys // c.e'.trans = Seq.nil ∧ Q c.we}, reachProb ws c.1 := by
  rw [← ENNReal.tsum_sigma (fun (e : {e : AlterSeq State Label // Q e})
      (c : {c : Config sys // c.we = e.1 ∧ c.e'.trans = Seq.nil}) => reachProb ws c.1)]
  exact Equiv.tsum_eq
    (({ toFun := fun p => ⟨p.2.1, ⟨p.2.2.2, by rw [p.2.2.1]; exact p.1.2⟩⟩
        invFun := fun c => ⟨⟨c.1.we, c.2.2⟩, ⟨c.1, rfl, c.2.1⟩⟩
        left_inv := by
          rintro ⟨⟨e, he⟩, ⟨c, hwe, he'⟩⟩; obtain rfl : c.we = e := hwe; rfl
        right_inv := fun c => rfl } :
      (Σ e : {e : AlterSeq State Label // Q e},
          {c : Config sys // c.we = e.1 ∧ c.e'.trans = Seq.nil})
        ≃ {c : Config sys // c.e'.trans = Seq.nil ∧ Q c.we}))
    (fun c => reachProb ws c.1)

/-- **Concrete reindex.** A dependent sum over (tight trajectory `e`, arrival config `c`
with `c.concat = e`) regroups to a single sum over the arrival configs `c`. -/
private theorem tsum_reindex_concat (ws : Scheduler sys^w) (Q : AlterSeq State Label → Prop) :
    (∑' e : {e : AlterSeq State Label // Q e},
        ∑' c : {c : Config sys // c.concat = e.1 ∧ c.e'.trans ≠ Seq.nil}, reachProb ws c.1)
      = ∑' c : {c : Config sys // c.e'.trans ≠ Seq.nil ∧ Q c.concat}, reachProb ws c.1 := by
  rw [← ENNReal.tsum_sigma (fun (e : {e : AlterSeq State Label // Q e})
      (c : {c : Config sys // c.concat = e.1 ∧ c.e'.trans ≠ Seq.nil}) => reachProb ws c.1)]
  exact Equiv.tsum_eq
    (({ toFun := fun p => ⟨p.2.1, ⟨p.2.2.2, by rw [p.2.2.1]; exact p.1.2⟩⟩
        invFun := fun c => ⟨⟨c.1.concat, c.2.2⟩, ⟨c.1, rfl, c.2.1⟩⟩
        left_inv := by
          rintro ⟨⟨e, he⟩, ⟨c, hcc, he'⟩⟩; obtain rfl : c.concat = e := hcc; rfl
        right_inv := fun c => rfl } :
      (Σ e : {e : AlterSeq State Label // Q e},
          {c : Config sys // c.concat = e.1 ∧ c.e'.trans ≠ Seq.nil})
        ≃ {c : Config sys // c.e'.trans ≠ Seq.nil ∧ Q c.concat}))
    (fun c => reachProb ws c.1)

/-! ### (1) abstract reduction, (2) concrete reduction, (3) post-τ conservation -/

/-- **(1) Abstract reduction.** The abstract trace probability is the total `reachProb` over
the **entry** configs (`e'` reset to `nil`) whose committed `we` is tight with trace `τ`. -/
private theorem traceProb_abstract_eq_abs (ws : Scheduler sys^w) (τ : Seq Label) :
    sys^w.traceProb ⟨PMF.pure sys.init, ws⟩ τ
      = ∑' c : {c : Config sys // c.e'.trans = Seq.nil ∧ c.we.trans.Terminates ∧
          sys.trace c.we = τ ∧ sys.IsTight c.we}, reachProb ws c.1 := by
  have h1 : sys^w.traceProb ⟨PMF.pure sys.init, ws⟩ τ
      = ∑' e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e},
          ∑' c : {c : Config sys // c.we = e.1 ∧ c.e'.trans = Seq.nil}, reachProb ws c.1 := by
    change (∑' e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e},
        (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).probOf e.1 e.2.1) = _
    exact tsum_congr (fun e => probOf_eq_reachProb_we ws e.1 e.2.1)
  rw [h1]
  exact tsum_reindex_we ws (fun e => e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e)

/-- **(2) Concrete reduction (`τ ≠ []`).** The concrete trace probability is the total
`reachProb` over the **arrival** configs (`e'` a nonempty segment) whose `concat` is tight
with trace `τ`. For `τ ≠ []` every such trajectory is off the root, so `reachArr` takes the
arrival-sum branch. -/
private theorem traceProb_concrete_eq_con (ws : Scheduler sys^w) (τ : Seq Label)
    (hτ : τ ≠ Seq.nil) :
    sys.traceProb ⟨PMF.pure sys.init, expandSched ws⟩ τ
      = ∑' c : {c : Config sys // c.e'.trans ≠ Seq.nil ∧ (Config.concat c).trans.Terminates ∧
          sys.trace (Config.concat c) = τ ∧ sys.IsTight (Config.concat c)}, reachProb ws c.1 := by
  have h1 : sys.traceProb ⟨PMF.pure sys.init, expandSched ws⟩ τ
      = ∑' e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e},
          ∑' c : {c : Config sys // c.concat = e.1 ∧ c.e'.trans ≠ Seq.nil}, reachProb ws c.1 := by
    change (∑' e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e},
        (⟨PMF.pure sys.init, expandSched ws⟩ : ProbabilisticExecution sys).probOf e.1 e.2.1) = _
    refine tsum_congr (fun e => ?_)
    have hne : e.1 ≠ ⟨sys.init, Seq.nil⟩ := by
      intro hroot
      apply hτ
      rw [← e.2.2.1, hroot, sys.trace_init]
    rw [probOf_eq_reachArr ws e.1 e.2.1, reachArr, if_neg hne]
  rw [h1]
  exact tsum_reindex_concat ws (fun e => e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e)

/-- **Witness emit lemma.** A scheduler `σ` realising the external weak step
`x ⤳[l] μ` (`l ≠ τ`) assigns the single-external-label trace `[l]` probability `1`.
`≤ 1` is the generic Kraft bound; `≥ 1` is witness almost-sure halting: every
halting run has trace `[l]` (`Realises` (c)), so the total halting mass `1`
(`Realises` (a)) is concentrated on trace `[l]` and bounded by
`traceProb [l]` (`haltMass_trace_le_traceProb`). -/
theorem witness_traceProb_emit {x : State} {l : Label} {μ : PMF State}
    {σ : Scheduler sys} (hR : Realises σ x l μ) (hl : ¬ l = Silent.τ) :
    sys.traceProb ⟨PMF.pure x, σ⟩ (Seq.cons l Seq.nil) = 1 := by
  classical
  refine le_antisymm (sys.traceProb_le_one _ _) ?_
  have hsum1 : (∑' e : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = Seq.cons l Seq.nil},
      (⟨PMF.pure x, σ⟩ : ProbabilisticExecution sys).probOf e.1 e.2.1 * σ.next e.1 none) = 1 := by
    rw [← hR.1]
    refine Function.Injective.tsum_eq
      (g := fun e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ sys.trace e = Seq.cons l Seq.nil} =>
        (⟨e.1, e.2.1⟩ : {e : AlterSeq State Label // e.trans.Terminates}))
      (f := fun e => σ.haltMass (PMF.pure x) e) ?_ ?_
    · intro a b hab
      apply Subtype.ext
      exact congrArg (Subtype.val :
        {e : AlterSeq State Label // e.trans.Terminates} → AlterSeq State Label) hab
    · intro j hj
      rw [Function.mem_support] at hj
      have htr := hR.2.2 j hj
      rw [if_neg hl] at htr
      exact ⟨⟨j.1, j.2, htr⟩, rfl⟩
  rw [← hsum1]
  exact (⟨PMF.pure x, σ⟩ : ProbabilisticExecution sys).haltMass_trace_le_traceProb
    (Seq.cons l Seq.nil)

/-- **(3) THE HARD CRUX — the unfolding-fidelity bridge (`τ ≠ []`).** The total `reachProb`
over the entry configs (ABS) equals the total over the arrival configs (CON). This identity is
logically equivalent to the whole `traceProb_expandSched_eq` (each side is, by `(1)`/`(2)`, the
abstract/concrete `traceProb`), so it carries the entire analytic weight of the unfolding fidelity.

LIMIT-FREE ROUTE (the intended proof; **supersedes** the abandoned per-level telescoping whose
residual was a limit `RA (pE exec) N → 0`). Decompose `τ = τ' ⌢ [l]` with `l` external (forced by
`IsTight`). Both sides factor through a COMMON base
  `base := ∑_{L' (filter = τ'), μ} predSum L' · ws.next ⟨init, ofList L'⟩ (some (l, μ))`,
`predSum L' := ∑_{entry c, we = ⟨init, ofList L'⟩, e'.trans = nil} reachProb c`:

* **ABS = base.** An ABS config is the OUTER target of an about-to-commit `c₀`
  (`c₀.wt = some (l, μ)`, `c₀.t = none`, `c₀.e'` the full witness segment, `c₀.we` of trace `τ'`).
  `reachProb_we_step` (which already folds in `seg_pushforward` / `Realises` (b)) telescopes
  `predSum (L' ++ [(l, x)]) = predSum L' · kernel_w ⟨init, ofList L'⟩ (l, x)`; summing the commit
  target `x` collapses `∑_x kernel_w (l, x) = ∑_μ ws.next (some (l, μ))` (PMF normalisation,
  `∑_x μ x = 1`). Reindexing ABS by `(L', x)` then gives `∑ ABS = base`.

* **CON = base · reachLmass.** A CON config sits at the l-emission point (`c.e' = preτ·l`,
  `c.wt = some (l, μ)`, `c.t = some (post-τ draw)`). `seg_inner_recursion` + `seg_entry_draw`
  factor it as `predSum L' · ws.next (some (l, μ)) · reachLmass`, where
  `reachLmass := ∑_{e' : tight, trace e' = [l]} probOf ⟨pure (lastOf c.e), schedOf sys · l μ⟩ e'`
  is the total witness probability of being AT an l-emission point. So `∑ CON = base · reachLmass`.

* **reachLmass = 1 (the only genuinely-new, LIMIT-FREE input).** `≤ 1` is the Kraft antichain
  bound (`probOf_antichain`): tight executions of equal trace are prefix-free (a clean
  `traceTightLabs`-level lemma: `traceTightLabs τ a → traceTightLabs τ b → a <+: b → a = b`).
  `≥ 1` is witness almost-sure halting: every halting run of the witness has trace `[l]`
  (`schedOf_realises` / `Realises` (c), `l ≠ τ`), so it passes through a unique l-emission prefix
  `e'`; the halt-mass-below-`e'` is `≤ probOf e'` (relative `probOf` / `pathWeight` factorisation
  `+ pathWeight_halt_le_one`), and `∑_{e'} probOf e' ≥ ∑_{halt f} haltMass f = 1` (`Realises` (a),
  `∑' e, σ.haltMass (pure x) e = 1`). No limit, no `iSup` interchange.

`abs_eq_con` then follows from `base · 1 = base · 1`.

RESIDUAL — single remaining `sorry` of the file. The genuinely-novel analytic input,
`reachLmass = traceProb(witness)[l] = 1`, is now **proven** (`witness_traceProb_emit`
above), resting on the generic Kraft infrastructure added to `TraceProbBound`
(`traceProb_le_one`, `haltMass_trace_le_traceProb`, `probOf_append_ofList`,
`pathWeight_halt_tsum_le_one`, `splitTight`/`splitTight_spec`). What remains is the
purely *combinatorial* config-bookkeeping that wires the two factorisations into
`abs_eq_con`, i.e. proving the two shape equalities

* **ABS = base**: telescoping the entry-config sum over `τ = τ' ⌢ [l]` via
  `reachProb_we_step` + `base_sum` (the outer commit weight `∑_x kernel_w (l,x)` collapsing
  to `∑_μ ws.next (some (l, μ))`);
* **CON = base · reachLmass**: factoring the arrival-config sum via
  `reachProb_seg` (`seg_inner_recursion` + `seg_entry_draw`), whose per-config witness
  factor sums to `reachLmass`, then applying `witness_traceProb_emit` to collapse
  `reachLmass = 1`.

Both reductions only compose existing `ExpandProbOf` machinery
(`reachProb_we_step`, `reachProb_seg`, `predSum_partition`, `base_sum`,
`seg_entry_draw`, `entryCfg_step_inner`) with the now-available `reachLmass = 1`;
no further analytic lemma is needed. -/
private theorem abs_eq_con (ws : Scheduler sys^w) (τ : Seq Label) (hτ : τ ≠ Seq.nil) :
    (∑' c : {c : Config sys // c.e'.trans = Seq.nil ∧ c.we.trans.Terminates ∧
        sys.trace c.we = τ ∧ sys.IsTight c.we}, reachProb ws c.1)
      = ∑' c : {c : Config sys // c.e'.trans ≠ Seq.nil ∧ (Config.concat c).trans.Terminates ∧
          sys.trace (Config.concat c) = τ ∧ sys.IsTight (Config.concat c)}, reachProb ws c.1 := by
  -- RESIDUAL: ABS = base = base · reachLmass = CON, with `reachLmass = 1` now PROVEN
  -- (`witness_traceProb_emit`). What remains is the config-bookkeeping assembly (ABS = base via
  -- `reachProb_we_step`/`base_sum`; CON = base · reachLmass via `reachProb_seg`). See docstring.
  sorry

/-! ### (4) base case `τ = []` -/

/-- **(4) Base case.** Both sides assign the empty trace probability `1`: the only tight,
empty-trace executions have no transitions, on which `probOf` reduces to the initial mass,
identical for the concrete and abstract executions (both start at `PMF.pure sys.init`). -/
private theorem traceProb_nil_eq (ws : Scheduler sys^w) :
    sys.traceProb ⟨PMF.pure sys.init, expandSched ws⟩ Seq.nil
      = sys^w.traceProb ⟨PMF.pure sys.init, ws⟩ Seq.nil := by
  change (∑' e : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = Seq.nil ∧ sys.IsTight e},
      (⟨PMF.pure sys.init, expandSched ws⟩ : ProbabilisticExecution sys).probOf e.1 e.2.1)
    = ∑' e : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = Seq.nil ∧ sys.IsTight e},
      (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).probOf e.1 e.2.1
  refine tsum_congr (fun e => ?_)
  obtain ⟨e, he⟩ := e
  obtain ⟨ei, et⟩ := e
  have htn : et = Seq.nil := trans_nil_of_trace_nil_tight ⟨ei, et⟩ he.1 he.2.1 he.2.2
  subst htn
  rw [ProbabilisticExecution.probOf_congr
        (⟨PMF.pure sys.init, expandSched ws⟩ : ProbabilisticExecution sys)
        ⟨ei, Seq.nil⟩ ⟨ei, Seq.nil⟩ rfl he.1 Stream'.Seq.terminates_nil,
      ProbabilisticExecution.probOf_congr
        (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w)
        ⟨ei, Seq.nil⟩ ⟨ei, Seq.nil⟩ rfl he.1 Stream'.Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil, ProbabilisticExecution.probOf_nil]
  rfl

/-! ### (5) assembly -/

theorem traceProb_expandSched_eq (ws : Scheduler sys^w) (τ : Seq Label) :
    sys.traceProb ⟨PMF.pure sys.init, expandSched ws⟩ τ
      = sys^w.traceProb ⟨PMF.pure sys.init, ws⟩ τ := by
  by_cases hτ : τ = Seq.nil
  · subst hτ; exact traceProb_nil_eq ws
  · rw [traceProb_concrete_eq_con ws τ hτ, ← abs_eq_con ws τ hτ,
        ← traceProb_abstract_eq_abs ws τ]

/-- **Hard direction of `weakClosure_traceProb_eq`**: every trace distribution
achievable by `sys^w` is achievable by `sys`. The witness reuses the given
`sys^w`-scheduler `ws` unfolded into the concrete scheduler `expandSched ws`;
`traceProb_expandSched_eq` says the trace distribution is preserved. -/
theorem weakClosure_traceProb_superset (sys : System State Label) :
    achievableTraceDists sys^w ⊆ achievableTraceDists sys := by
  rintro D ⟨pe', hinit, htrace⟩
  refine ⟨⟨PMF.pure sys.init, expandSched pe'.scheduler⟩, rfl, fun τ => ?_⟩
  have hrw : (⟨PMF.pure sys.init, pe'.scheduler⟩ : ProbabilisticExecution sys^w) = pe' := by
    rw [show (PMF.pure sys.init : PMF State) = pe'.initState from hinit.symm]
  rw [traceProb_expandSched_eq pe'.scheduler τ, hrw, htrace τ]

/-- **Weak-closure construction preserves trace distributions.** -/
theorem weakClosure_traceProb_eq (sys : System State Label) :
    achievableTraceDists sys = achievableTraceDists sys^w :=
  Set.Subset.antisymm
    (weakClosure_traceProb_subset sys)
    (weakClosure_traceProb_superset sys)

end PLTS
