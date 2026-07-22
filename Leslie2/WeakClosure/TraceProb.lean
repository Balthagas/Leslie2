/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.WeakClosure.Scheduler
import Leslie2.Weak.Bounds

/-!
# Trace-distribution preservation of the weak closure (the hard direction)

This file assembles the unfolding-algorithm fidelity results into
`weakClosure_traceProb_superset`: every trace distribution achievable by `sys^w`
is achievable by `sys`. It is the downstream home of the theorem (and the
resulting equality `weakClosure_traceProb_eq`), since the proof needs the
unfolding machinery (`Expand`/`ExpandTrace`/`ExpandProbOf`/`ExpandSched`), which
imports `WeakClosure/WeakClosure.lean` where the easy direction lives.

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

/- **(3) THE HARD CRUX — the unfolding-fidelity bridge (`τ ≠ []`).** The total `reachProb`
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

Both shape equalities are **proven**:

* **ABS = base** (`abs_eq_baseSum`): telescoping the entry-config sum over `τ = τ' ⌢ [l]` via
  `reachProb_we_step` + `base_sum` (the outer commit weight `∑_x kernel_w (l,x)` collapsing
  to `∑_μ ws.next (some (l, μ))`);
* **CON = base** (`con_eq_baseSum`): reindexing the arrival-config sum (`con_bij`) onto tuples
  `(L', E, μ, seg, t)` and summing them out per entry list `L'` (`con_perL`) — `con_seg_collapse`
  collapses each `(E, μ)` segment sum to the witness `traceProb [l] = 1` (`witness_traceProb_emit`)
  and `predSum_partition` rebuilds `predSum L'` over `E`. The active-label identification
  `trace seg = [l]` per config comes from `witness_seg_trace` (a tight nonempty positive-probability
  witness segment emits exactly `[l]`, via the halt-below identity `probOf_eq_haltBelow`). -/
/-- The **common base** of the ABS = CON identity (for `τ = τ' ⌢ [l]`, `l` external). Indexed by
the abstract weak-step lists `L'` whose committed execution `⟨init, ofList L'⟩` has external trace
`τ'`: the entry-`L'` reach `predSum L'` times the total `ws`-mass of drawing the final external
weak step `(l, ·)` at `⟨init, ofList L'⟩`. Both ABS (telescoped by `reachProb_we_step`) and CON
(factored by `reachProb_seg` with the witness `reachLmass = 1`) reduce to this. -/
private noncomputable def baseSum (ws : Scheduler sys^w) (τ' : Seq Label) (l : Label) : ENNReal :=
  ∑' L' : {L : List (Label × State) // sys.trace ⟨sys.init, Seq.ofList L⟩ = τ'},
    (∑' c : {c : Config sys // c.we = ⟨sys.init, Seq.ofList L'.1⟩ ∧ c.e'.trans = Seq.nil},
        reachProb ws c.1)
      * (∑' μ : PMF State, ws.next ⟨sys.init, Seq.ofList L'.1⟩ (some (l, μ)))

open Classical in
/-- A terminating, trace-tight execution with nonempty external trace `τ` forces `τ` to end with
an external label: `τ = τ' ⌢ [l]`, `l ≠ τ`. (The last transition of a tight nonempty execution is
external — `traceTightLabs`'s second clause — and that label survives the trace filter as its
last element.) -/
private theorem exists_split_of_tight (τ : Seq Label) (e : AlterSeq State Label)
    (hfin : e.trans.Terminates) (htr : sys.trace e = τ) (htight : sys.IsTight e)
    (hτ : τ ≠ Seq.nil) :
    ∃ (τ' : Seq Label) (l : Label),
      ¬ l = Silent.τ ∧ τ = τ'.append (Seq.cons l Seq.nil) := by
  have htt : sys.traceTightLabs τ ((e.trans.toList hfin).map Prod.fst) :=
    (sys.tight_iff τ e hfin).mp ⟨htr, htight⟩
  obtain ⟨hfilter, hlastext⟩ := htt
  rcases List.eq_nil_or_concat ((e.trans.toList hfin).map Prod.fst) with h0 | ⟨pre, l, hlabseq⟩
  · exfalso; apply hτ
    rw [← hfilter, h0, Stream'.Seq.ofList_nil, Stream'.Seq.filter_nil]
  · rw [List.concat_eq_append] at hlabseq
    have hgl : (pre ++ [l]).getLast? = some l := by simp
    have hl_ext : ¬ l = Silent.τ := hlastext l (by rw [hlabseq]; exact hgl)
    refine ⟨(Seq.ofList pre).filter (fun a => ¬ a = Silent.τ), l, hl_ext, ?_⟩
    rw [← hfilter, hlabseq, Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons,
      Stream'.Seq.ofList_nil,
      Stream'.Seq.filter_append (fun a => ¬ a = Silent.τ) (Seq.ofList pre) _
        (Stream'.Seq.terminates_ofList pre),
      Stream'.Seq.filter_cons_pos (p := fun a => ¬ a = Silent.τ) l Seq.nil hl_ext,
      Stream'.Seq.filter_nil]

/-- The external trace of `⟨init, ofList L'⟩` is the τ-filter of its label list. -/
private theorem trace_ofList_eq_filter (L' : List (Label × State)) :
    sys.trace ⟨sys.init, Seq.ofList L'⟩
      = (Seq.ofList (L'.map Prod.fst)).filter (fun a => ¬ a = Silent.τ) := by
  rw [← Seq.map_ofList_pub Prod.fst L',
    Stream'.Seq.filter_map Prod.fst (fun a => ¬ a = Silent.τ) (Seq.ofList L')]
  rfl

/-- Appending one external transition `(l, x)` to `⟨init, ofList L'⟩` appends `l` to its trace. -/
private theorem trace_ofList_append_ext (L' : List (Label × State)) (l : Label) (x : State)
    (hl : ¬ l = Silent.τ) :
    sys.trace ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩
      = (sys.trace ⟨sys.init, Seq.ofList L'⟩).append (Seq.cons l Seq.nil) := by
  rw [trace_ofList_eq_filter, trace_ofList_eq_filter]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil,
    Stream'.Seq.filter_append (fun a => ¬ a = Silent.τ) _ _ (Stream'.Seq.terminates_ofList _),
    Stream'.Seq.filter_cons_pos (p := fun a => ¬ a = Silent.τ) l Seq.nil hl,
    Stream'.Seq.filter_nil]

/-- The appended execution `⟨init, ofList (L' ++ [(l, x)])⟩` (where `⟨init, ofList L'⟩` has trace
`τ'` and `l` is external) is terminating, has trace `τ' ⌢ [l]`, and is tight. -/
private theorem target_Q (τ' : Seq Label) (l : Label) (hl : ¬ l = Silent.τ)
    (L' : List (Label × State)) (x : State)
    (hL' : sys.trace ⟨sys.init, Seq.ofList L'⟩ = τ') :
    (⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ : AlterSeq State Label).trans.Terminates ∧
      sys.trace ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ = τ'.append (Seq.cons l Seq.nil) ∧
      sys.IsTight ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ := by
  have hfin : (⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ : AlterSeq State Label).trans.Terminates :=
    Stream'.Seq.terminates_ofList _
  have htr : sys.trace ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩
      = τ'.append (Seq.cons l Seq.nil) := by rw [trace_ofList_append_ext L' l x hl, hL']
  refine ⟨hfin, htr, ?_⟩
  have htt : sys.traceTightLabs (τ'.append (Seq.cons l Seq.nil))
      (((⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ : AlterSeq State Label).trans.toList hfin).map
        Prod.fst) := by
    rw [show (⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ : AlterSeq State Label).trans.toList hfin
          = L' ++ [(l, x)] from Stream'.Seq.toList_ofList _]
    refine ⟨?_, ?_⟩
    · simp only [List.map_append, List.map_cons, List.map_nil]
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil,
        Stream'.Seq.filter_append (fun a => ¬ a = Silent.τ) _ _ (Stream'.Seq.terminates_ofList _),
        Stream'.Seq.filter_cons_pos (p := fun a => ¬ a = Silent.τ) l Seq.nil hl,
        Stream'.Seq.filter_nil, ← trace_ofList_eq_filter, hL']
    · intro l₀ hl₀
      have hlast : ((L' ++ [(l, x)]).map Prod.fst).getLast? = some l := by simp
      rw [hlast] at hl₀
      obtain rfl := Option.some_inj.mp hl₀
      exact hl
  exact ((sys.tight_iff _ _ hfin).mpr htt).2

/-- **Per-prefix collapse (ABS side).** Summing `probOf_w ⟨init, ofList (L' ++ [(l, x)])⟩` over the
final state `x` telescopes (via `reachProb_we_step`) to the entry-`L'` reach times the total
`ws`-mass of drawing the final external weak step `(l, ·)`. -/
private theorem abs_perL (ws : Scheduler sys^w) (l : Label) (L' : List (Label × State)) :
    (∑' x : State, (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).probOf
        ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ (Stream'.Seq.terminates_ofList _))
      = (∑' c : {c : Config sys // c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil},
          reachProb ws c.1)
        * ∑' μ : PMF State, ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) := by
  have hstep : ∀ x : State, (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).probOf
        ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ (Stream'.Seq.terminates_ofList _)
      = (∑' c : {c : Config sys // c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil},
          reachProb ws c.1)
        * (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).kernel
            ⟨sys.init, Seq.ofList L'⟩ (l, x) :=
    fun x => by rw [aux ws (L' ++ [(l, x)]), reachProb_we_step ws L' l x]
  rw [tsum_congr hstep, ENNReal.tsum_mul_left]
  congr 1
  calc (∑' x : State, (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).kernel
          ⟨sys.init, Seq.ofList L'⟩ (l, x))
      = ∑' x : State, ∑' μ : PMF State,
          ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) * μ x := rfl
    _ = ∑' μ : PMF State, ∑' x : State,
          ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) * μ x := ENNReal.tsum_comm
    _ = ∑' μ : PMF State,
          ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) * ∑' x : State, μ x :=
        tsum_congr (fun μ => by rw [ENNReal.tsum_mul_left])
    _ = ∑' μ : PMF State, ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) :=
        tsum_congr (fun μ => by rw [PMF.tsum_coe, mul_one])

open Classical in
/-- **Bijection (ABS side).** The total `probOf_w` over tight, trace-`τ' ⌢ [l]` abstract executions
equals the sum over pairs `(L', x)` — with `⟨init, ofList L'⟩` of trace `τ'` — of `probOf_w` of the
one-external-step extension `⟨init, ofList (L' ++ [(l, x)])⟩`. -/
private theorem abs_bij (ws : Scheduler sys^w) (τ' : Seq Label) (l : Label)
    (hl : ¬ l = Silent.τ) :
    (∑' e : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = τ'.append (Seq.cons l Seq.nil) ∧ sys.IsTight e},
        (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).probOf e.1 e.2.1)
      = ∑' p : {L : List (Label × State) // sys.trace ⟨sys.init, Seq.ofList L⟩ = τ'} × State,
          (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).probOf
            ⟨sys.init, Seq.ofList (p.1.1 ++ [(l, p.2)])⟩ (Stream'.Seq.terminates_ofList _) := by
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun p => ⟨⟨sys.init, Seq.ofList (p.1.1.1 ++ [(l, p.1.2)])⟩,
        target_Q τ' l hl p.1.1.1 p.1.2 p.1.1.2⟩) ?_ ?_ ?_
  · -- injective on `support g`
    intro a b hab
    have hlist : a.1.1.1 ++ [(l, a.1.2)] = b.1.1.1 ++ [(l, b.1.2)] :=
      Stream'.Seq.ofList_injective (congrArg AlterSeq.trans (congrArg Subtype.val hab))
    have hL : a.1.1.1 = b.1.1.1 := by
      have h := congrArg List.dropLast hlist
      rwa [List.dropLast_concat, List.dropLast_concat] at h
    have hx : a.1.2 = b.1.2 := by
      have h := congrArg List.getLast? hlist
      rw [List.getLast?_concat, List.getLast?_concat] at h
      exact (Prod.mk.inj (Option.some_inj.mp h)).2
    exact Subtype.ext (Prod.ext (Subtype.ext hL) hx)
  · -- `support f ⊆ range i`
    intro e he
    have hpos : (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).probOf e.1 e.2.1 ≠ 0 := he
    have hinit : e.1.init = sys.init := by
      by_contra hne
      exact hpos (by rw [ProbabilisticExecution.probOf_init_factor ws (PMF.pure sys.init) e.1 e.2.1,
        PMF.pure_apply_of_ne _ _ hne, zero_mul])
    have he1trans : (⟨sys.init, e.1.trans⟩ : AlterSeq State Label) = e.1 := by rw [← hinit]
    set M := e.1.trans.toList e.2.1 with hMdef
    have hMtrans : e.1.trans = Seq.ofList M := (Stream'.Seq.ofList_toList e.1.trans e.2.1).symm
    have hMne : M ≠ [] := by
      intro h0
      have htn : sys.trace e.1 = Seq.nil := by
        have he0 : e.1.trans = Seq.nil := by rw [hMtrans, h0, Stream'.Seq.ofList_nil]
        change (e.1.trans.filter (fun p => ¬ p.1 = Silent.τ)).map Prod.fst = Seq.nil
        rw [he0, Stream'.Seq.filter_nil, Stream'.Seq.map_nil]
      exact append_cons_ne_nil τ' l Seq.nil (e.2.2.1.symm.trans htn)
    rcases List.eq_nil_or_concat M with h0 | ⟨M'', last, hMeq⟩
    · exact absurd h0 hMne
    · rw [List.concat_eq_append] at hMeq
      obtain ⟨lₘ, x⟩ := last
      obtain ⟨-, hlastext⟩ :=
        (sys.tight_iff (τ'.append (Seq.cons l Seq.nil)) e.1 e.2.1).mp ⟨e.2.2.1, e.2.2.2⟩
      have hlₘ : ¬ lₘ = Silent.τ := hlastext lₘ (by rw [← hMdef, hMeq]; simp)
      have htrace_split : (sys.trace ⟨sys.init, Seq.ofList M''⟩).append (Seq.cons lₘ Seq.nil)
          = τ'.append (Seq.cons l Seq.nil) := by
        rw [← trace_ofList_append_ext M'' lₘ x hlₘ, ← hMeq, ← hMtrans, he1trans]; exact e.2.2.1
      have hAterm : (sys.trace ⟨sys.init, Seq.ofList M''⟩).Terminates := by
        rw [trace_ofList_eq_filter]
        exact Stream'.Seq.terminates_filter _ _ (Stream'.Seq.terminates_ofList _)
      have hτ'term : τ'.Terminates := by
        have hbig : ((sys.trace ⟨sys.init, Seq.ofList M''⟩).append
            (Seq.cons lₘ Seq.nil)).Terminates :=
          ⟨_, Stream'.Seq.terminatedAt_append_find hAterm
            (show (Seq.cons lₘ Seq.nil).TerminatedAt 1 from rfl)⟩
        rw [htrace_split] at hbig
        exact terminates_of_append_terminates hbig
      have hlₘl : lₘ = l :=
        Stream'.Seq.append_singleton_inj_right _ _ hAterm hτ'term lₘ l htrace_split
      have htrM'' : sys.trace ⟨sys.init, Seq.ofList M''⟩ = τ' :=
        Stream'.Seq.append_singleton_inj_left _ _ hAterm hτ'term lₘ l htrace_split
      have htarget : (⟨sys.init, Seq.ofList (M'' ++ [(l, x)])⟩ : AlterSeq State Label) = e.1 := by
        have h0 : (⟨sys.init, Seq.ofList (M'' ++ [(lₘ, x)])⟩ : AlterSeq State Label) = e.1 := by
          rw [← hMeq, ← hMtrans]; exact he1trans
        rwa [hlₘl] at h0
      refine ⟨⟨(⟨M'', htrM''⟩, x), ?_⟩, Subtype.ext htarget⟩
      change (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).probOf
          ⟨sys.init, Seq.ofList (M'' ++ [(l, x)])⟩ (Stream'.Seq.terminates_ofList _) ≠ 0
      rw [ProbabilisticExecution.probOf_congr
        (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w)
        ⟨sys.init, Seq.ofList (M'' ++ [(l, x)])⟩ e.1 htarget
        (Stream'.Seq.terminates_ofList _) e.2.1]
      exact hpos
  · -- `hfg`
    intro p; rfl

/-- **ABS = base.** Telescoping the entry-config sum over `τ = τ' ⌢ [l]` via `reachProb_we_step`. -/
private theorem abs_eq_baseSum (ws : Scheduler sys^w) (τ' : Seq Label) (l : Label)
    (hl : ¬ l = Silent.τ) :
    (∑' c : {c : Config sys // c.e'.trans = Seq.nil ∧ c.we.trans.Terminates ∧
        sys.trace c.we = τ'.append (Seq.cons l Seq.nil) ∧ sys.IsTight c.we}, reachProb ws c.1)
      = baseSum ws τ' l := by
  rw [← tsum_reindex_we ws
      (fun e => e.trans.Terminates ∧ sys.trace e = τ'.append (Seq.cons l Seq.nil) ∧ sys.IsTight e)]
  refine Eq.trans (tsum_congr (fun e => (probOf_eq_reachProb_we ws e.1 e.2.1).symm)) ?_
  rw [abs_bij ws τ' l hl, ENNReal.tsum_prod']
  exact tsum_congr (fun L' => abs_perL ws l L'.1)

/-- **Per-config factor (CON side).** Marginalising the inner draw `t` of a configuration `c`
with committed `we = ⟨init, ofList L'⟩`, active weak step `(l, μ)`, witness `schedOf (last e) l μ`,
and completed segment `c.e'`, factors as the entry-`L'` reach over `c.e`, times the `ws`-mass of
drawing `(l, μ)`, times the witness `probOf` of the segment `c.e'`. (`seg_inner_recursion` summed
over `t` collapses the trailing `s.next`; `seg_entry_draw` supplies the entry marginal.) -/
private theorem con_factor (ws : Scheduler sys^w) (L' : List (Label × State)) (l : Label)
    (μ : PMF State) (c : Config sys) (he'fin : c.e'.trans.Terminates)
    (hwe : c.we = ⟨sys.init, Seq.ofList L'⟩) (hwt : c.wt = some (l, μ))
    (hs : c.s = schedOf sys (lastOf c.e) l μ) (hinit : c.e'.init = lastOf c.e) :
    (∑' t : Option (Label × PMF State), reachProb ws {c with t := t})
      = (∑' c' : {c' : Config sys //
            c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = c.e},
          reachProb ws c'.1)
        * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ))
        * (⟨PMF.pure (lastOf c.e), schedOf sys (lastOf c.e) l μ⟩
            : ProbabilisticExecution sys).probOf c.e' he'fin := by
  have hsi : ∀ t : Option (Label × PMF State), reachProb ws {c with t := t}
      = ((∑' t' : Option (Label × PMF State),
            reachProb ws {c with e' := ⟨lastOf c.e, Seq.nil⟩, t := t'})
          * (⟨PMF.pure (lastOf c.e), c.s⟩ : ProbabilisticExecution sys).probOf c.e' he'fin)
        * c.s.next c.e' t := fun t =>
    seg_inner_recursion ws l μ (c.e'.trans.toList he'fin) {c with t := t} he'fin
      hwt hinit (Stream'.Seq.ofList_toList c.e'.trans he'fin).symm
  rw [tsum_congr hsi, ENNReal.tsum_mul_left, (c.s.next c.e').tsum_coe, mul_one,
    seg_entry_draw ws L' l μ c hwe hwt hs, hs]

open Classical in
/-- **Witness halting continuation.** A terminating run `e'` produced with positive probability
by a scheduler `σ` realising the weak step `x ⤳[l] μ` extends to a *halting* continuation `g = e'⌢t`
whose trace is the weak step's external trace (`[]` for `l = τ`, `[l]` otherwise, `Realises` (c)).
Hence `sys.trace e'` is a prefix of that trace. Under almost-sure halting (`Realises` (a)),
`probOf e' ≠ 0` forces the halt mass `haltBelow e'` to be positive (`probOf_eq_haltBelow`). -/
private theorem witness_halt_cont {x : State} {l : Label} {μ : PMF State} {σ : Scheduler sys}
    (hR : Realises σ x l μ) (e' : AlterSeq State Label) (h' : e'.trans.Terminates)
    (hpos : (⟨PMF.pure x, σ⟩ : ProbabilisticExecution sys).probOf e' h' ≠ 0) :
    ∃ W : Seq Label,
      (sys.trace e').append W = if l = Silent.τ then Seq.nil else Seq.cons l Seq.nil := by
  set pe : ProbabilisticExecution sys := ⟨PMF.pure x, σ⟩ with hpe
  have hAS : (∑' g : {g : AlterSeq State Label // g.trans.Terminates},
      pe.probOf g.1 g.2 * pe.scheduler.next g.1 none) = 1 := hR.1
  rw [pe.probOf_eq_haltBelow hAS e' h'] at hpos
  unfold ProbabilisticExecution.haltBelow at hpos
  have hex : ∃ t : List (Label × State),
      pe.probOf ⟨e'.init, e'.trans.append (Seq.ofList t)⟩ (append_ofList_terminates h' t)
        * pe.scheduler.next ⟨e'.init, e'.trans.append (Seq.ofList t)⟩ none ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hpos (ENNReal.tsum_eq_zero.mpr hc)
  obtain ⟨t, ht⟩ := hex
  rw [mul_ne_zero_iff] at ht
  have hgterm : (e'.trans.append (Seq.ofList t)).Terminates := append_ofList_terminates h' t
  have hhalt : σ.haltMass (PMF.pure x)
      ⟨⟨e'.init, e'.trans.append (Seq.ofList t)⟩, hgterm⟩ ≠ 0 := by
    unfold Scheduler.haltMass
    exact mul_ne_zero ht.1 ht.2
  have htr_g : sys.trace (⟨e'.init, e'.trans.append (Seq.ofList t)⟩ : AlterSeq State Label)
      = if l = Silent.τ then Seq.nil else Seq.cons l Seq.nil :=
    trace_of_halt hR ⟨⟨e'.init, e'.trans.append (Seq.ofList t)⟩, hgterm⟩ hhalt
  rw [trace_append e'.init e'.trans (Seq.ofList t) h'] at htr_g
  exact ⟨sys.trace ⟨e'.init, Seq.ofList t⟩, htr_g⟩

omit [Silent Label] in
/-- A nonempty prefix of the singleton sequence `[l]` is `[l]`. -/
private theorem nonempty_prefix_singleton {l : Label} (A W : Seq Label)
    (hAW : A.append W = Seq.cons l Seq.nil) (hAne : A ≠ Seq.nil) : A = Seq.cons l Seq.nil := by
  cases A using Stream'.Seq.recOn with
  | nil => exact absurd rfl hAne
  | cons a s' =>
    rw [Stream'.Seq.cons_append] at hAW
    obtain ⟨ha, hs'⟩ := Stream'.Seq.cons_eq_cons.mp hAW
    rw [ha, (append_eq_nil hs').1]

/-- **Witness segment trace.** A tight, terminating, nonempty segment `e'` produced with positive
probability by a scheduler `σ` realising the external weak step `x ⤳[l] μ` (`l ≠ τ`) has trace
exactly `[l]`. Its trace is a prefix of `[l]` (`witness_halt_cont`); being nonempty (a tight
nonempty exec has a nonempty trace) pins it to `[l]`. -/
private theorem witness_tight_trace {x : State} {l : Label} {μ : PMF State} {σ : Scheduler sys}
    (hR : Realises σ x l μ) (hl : ¬ l = Silent.τ)
    (e' : AlterSeq State Label) (h' : e'.trans.Terminates) (_hinit : e'.init = x)
    (hne : e'.trans ≠ Seq.nil) (htight : sys.IsTight e')
    (hpos : (⟨PMF.pure x, σ⟩ : ProbabilisticExecution sys).probOf e' h' ≠ 0) :
    sys.trace e' = Seq.cons l Seq.nil := by
  obtain ⟨W, hW⟩ := witness_halt_cont hR e' h' hpos
  rw [if_neg hl] at hW
  refine nonempty_prefix_singleton _ W hW ?_
  intro hAnil
  exact hne (trans_nil_of_trace_nil_tight e' h' hAnil htight)

/-- **Witness segment trace + externality.** For a tight, terminating, nonempty positive-probability
segment `e'` of a `Realises` witness, the emitted label `l` is external and `sys.trace e' = [l]`.
The externality is forced by tightness: were `l = τ`, the halting continuation would have empty
trace, so `e'` (a nonempty prefix) would too, contradicting tight-nonempty ⇒ nonempty trace. -/
private theorem witness_seg_trace {x : State} {l : Label} {μ : PMF State} {σ : Scheduler sys}
    (hR : Realises σ x l μ)
    (e' : AlterSeq State Label) (h' : e'.trans.Terminates) (hinit : e'.init = x)
    (hne : e'.trans ≠ Seq.nil) (htight : sys.IsTight e')
    (hpos : (⟨PMF.pure x, σ⟩ : ProbabilisticExecution sys).probOf e' h' ≠ 0) :
    sys.trace e' = Seq.cons l Seq.nil ∧ ¬ l = Silent.τ := by
  have hAne : sys.trace e' ≠ Seq.nil := fun hAnil =>
    hne (trans_nil_of_trace_nil_tight e' h' hAnil htight)
  have hl : ¬ l = Silent.τ := by
    intro hτ
    obtain ⟨W, hW⟩ := witness_halt_cont hR e' h' hpos
    rw [if_pos hτ] at hW
    exact hAne (append_eq_nil hW).1
  exact ⟨witness_tight_trace hR hl e' h' hinit hne htight hpos, hl⟩

/-- A nonzero guarded weight `if P then a else 0` forces its guard `P` (local copy). -/
private theorem of_ite_ne_zero {P : Prop} [Decidable P] {a : ENNReal}
    (h : (if P then a else 0) ≠ 0) : P := by
  by_contra hP; rw [if_neg hP] at h; exact h rfl

open Classical in
/-- **Config-shape invariant for the CON reindexing.** Every reachable configuration has its
committed abstract execution `we` rooted at `sys.init`, and either an empty in-progress segment
(`e'.trans = nil`) or an active weak step (`wt = some p`). -/
private theorem reachAfter_con_facts (ws : Scheduler sys^w) :
    ∀ (n : ℕ) (c : Config sys), reachAfter ws n c ≠ 0 →
      c.we.init = sys.init ∧ c.we.trans.Terminates ∧
        (c.e'.trans = Seq.nil ∨ ∃ p, c.wt = some p) := by
  intro n
  induction n with
  | zero =>
    intro c hreach
    by_cases hcond : (c.we = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
        c.e = ⟨sys.init, Seq.nil⟩ ∧ c.e' = ⟨sys.init, Seq.nil⟩ ∧
        (∀ p, c.wt = some p → c.s = schedOf sys sys.init p.1 p.2) ∧
        (c.wt = none → c.s = Scheduler.halt sys))
    · exact ⟨by rw [hcond.1], by rw [hcond.1]; exact Stream'.Seq.terminates_nil,
        Or.inl (by rw [hcond.2.2.1])⟩
    · simp only [reachAfter] at hreach; rw [if_neg hcond] at hreach; exact absurd rfl hreach
  | succ n ih =>
    intro c hreach
    rw [reachAfter] at hreach
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, reachAfter ws n c₀ * step ws c₀ c ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hreach (ENNReal.tsum_eq_zero.mpr hcon)
    rw [mul_ne_zero_iff] at hc₀
    obtain ⟨hreach₀, hstep⟩ := hc₀
    obtain ⟨hinit₀, hwefin₀, -⟩ := ih c₀ hreach₀
    obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
    cases wt₀ with
    | none => simp only [step] at hstep; exact absurd rfl hstep
    | some wtp =>
      obtain ⟨lw, μw⟩ := wtp
      cases t₀ with
      | none =>
        simp only [step] at hstep
        obtain ⟨hce, hcwe, hce', -, -⟩ := of_ite_ne_zero hstep
        refine ⟨by rw [hcwe]; exact hinit₀, ?_, Or.inl (by rw [hce'])⟩
        rw [hcwe]
        exact ⟨_, Stream'.Seq.terminatedAt_append_find hwefin₀
          (show (Seq.cons (lw, _) Seq.nil).TerminatedAt 1 from rfl)⟩
      | some tp =>
        obtain ⟨l', μ'⟩ := tp
        simp only [step] at hstep
        obtain ⟨hcwe, -, hcwt, -, -, -⟩ := of_ite_ne_zero hstep
        exact ⟨by rw [hcwe]; exact hinit₀, by rw [hcwe]; exact hwefin₀,
          Or.inr ⟨(lw, μw), hcwt⟩⟩

/-- Reachable form of `reachAfter_con_facts`. -/
private theorem reachProb_con_facts (ws : Scheduler sys^w) (c : Config sys)
    (h : reachProb ws c ≠ 0) :
    c.we.init = sys.init ∧ c.we.trans.Terminates ∧
      (c.e'.trans = Seq.nil ∨ ∃ p, c.wt = some p) := by
  rw [reachProb] at h
  obtain ⟨n, hn⟩ : ∃ n, reachAfter ws n c ≠ 0 := by
    by_contra hcon; push Not at hcon; exact h (ENNReal.tsum_eq_zero.mpr hcon)
  exact reachAfter_con_facts ws n c hn

/-- The τ-filter of an execution's label list is its external trace (init-independent form of
`trace_ofList_eq_filter`). Supplies the first `traceTightLabs` clause. -/
private theorem filter_toList_eq_trace (e : AlterSeq State Label) (h : e.trans.Terminates) :
    (Seq.ofList ((e.trans.toList h).map Prod.fst)).filter (fun a => ¬ a = Silent.τ)
      = sys.trace e := by
  rw [← Seq.map_ofList_pub Prod.fst (e.trans.toList h), Stream'.Seq.ofList_toList e.trans h,
    Stream'.Seq.filter_map Prod.fst (fun a => ¬ a = Silent.τ) e.trans]
  rfl

open Classical in
/-- **Tightness ⇔ last label external.** A terminating execution is tight exactly when its label
list is empty or ends with an external label. -/
private theorem isTight_iff_lastExt (e : AlterSeq State Label) (h : e.trans.Terminates) :
    sys.IsTight e ↔
      ∀ lst, ((e.trans.toList h).map Prod.fst).getLast? = some lst → ¬ lst = Silent.τ := by
  constructor
  · intro ht
    exact ((sys.tight_iff (sys.trace e) e h).mp ⟨rfl, ht⟩).2
  · intro hlast
    exact ((sys.tight_iff (sys.trace e) e h).mpr ⟨filter_toList_eq_trace e h, hlast⟩).2

open Classical in
/-- **Tightness of the concatenation ⇔ tightness of the (nonempty) segment.** Tightness depends
only on the last transition, which — for a nonempty segment `B` — is the last transition of the
concatenation `A ⌢ B`. -/
private theorem isTight_concat_iff (A B : Seq (Label × State)) (i j : State)
    (hA : A.Terminates) (hB : B.Terminates) (hBne : B ≠ Seq.nil)
    (happ : (A.append B).Terminates) :
    sys.IsTight (⟨i, A.append B⟩ : AlterSeq State Label)
      ↔ sys.IsTight (⟨j, B⟩ : AlterSeq State Label) := by
  have hBtoL_ne : B.toList hB ≠ [] := by
    intro h0
    exact hBne (by rw [← Stream'.Seq.ofList_toList B hB, h0, Stream'.Seq.ofList_nil])
  have hBmap_ne : (B.toList hB).map Prod.fst ≠ [] := by
    intro h0; exact hBtoL_ne (List.map_eq_nil_iff.mp h0)
  rw [isTight_iff_lastExt ⟨i, A.append B⟩ happ, isTight_iff_lastExt ⟨j, B⟩ hB]
  have hfull : ((⟨i, A.append B⟩ : AlterSeq State Label).trans.toList happ).map Prod.fst
      = (A.toList hA).map Prod.fst ++ (B.toList hB).map Prod.fst := by
    change ((A.append B).toList happ).map Prod.fst = _
    rw [Stream'.Seq.toList_append A B hA hB happ, List.map_append]
  rw [hfull, show ((⟨j, B⟩ : AlterSeq State Label).trans.toList hB).map Prod.fst
        = (B.toList hB).map Prod.fst from rfl,
    List.getLast?_append_of_ne_nil _ hBmap_ne]

open Classical in
/-- **Unconditional per-config factor for the CON reindex.** Marginalising the inner draw `t` of the
canonical arrival config `canonCfg L' l E μ seg` factors as the entry-`L'` reach over `E`, times
`ws`'s mass on `(l, μ)`, times the witness `probOf` of the segment `seg` — with no side condition on
`seg.init` (when `seg.init ≠ lastOf E` both sides vanish). -/
private theorem con_factor_canon (ws : Scheduler sys^w) (L' : List (Label × State)) (l : Label)
    (μ : PMF State) (E seg : AlterSeq State Label) (hseg : seg.trans.Terminates) :
    (∑' t : Option (Label × PMF State), reachProb ws {canonCfg sys L' l E μ seg with t := t})
      = (∑' c : {c : Config sys //
            c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E}, reachProb ws c.1)
        * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ))
        * (⟨PMF.pure (lastOf E), schedOf sys (lastOf E) l μ⟩
            : ProbabilisticExecution sys).probOf seg hseg := by
  by_cases hinit : seg.init = lastOf E
  · exact con_factor ws L' l μ (canonCfg sys L' l E μ seg) hseg rfl rfl rfl hinit
  · have hL : (∑' t : Option (Label × PMF State),
        reachProb ws {canonCfg sys L' l E μ seg with t := t}) = 0 := by
      refine ENNReal.tsum_eq_zero.mpr (fun t => ?_)
      by_contra h0
      exact hinit (reachProb_inv ws _ h0).2.2.1
    have hR0 : (⟨PMF.pure (lastOf E), schedOf sys (lastOf E) l μ⟩
        : ProbabilisticExecution sys).probOf seg hseg = 0 := by
      refine nonpos_iff_eq_zero.mp
        (le_trans (ProbabilisticExecution.probOf_le_init _ seg hseg) (le_of_eq ?_))
      change (PMF.pure (lastOf E)) seg.init = 0
      rw [PMF.pure_apply, if_neg hinit]
    rw [hL, hR0, mul_zero]

open Classical in
/-- **Segment collapse (CON side).** At a fixed `(L', E, μ)`, summing `con_factor_canon` over every
tight, terminating, trace-`[l]` segment collapses to the entry-`L'` reach over `E` times `ws`'s
`(l, μ)`-mass. The segment sum is the witness `traceProb ⟨pure (lastOf E), schedOf …⟩ [l]`, which is
`1` when the weak step `lastOf E ⤳[l] μ` is valid (`witness_traceProb_emit`); otherwise the
prefactor vanishes (`ws.valid` on `⟨init, ofList L'⟩`, whose endpoint is `lastOf E`). -/
private theorem con_seg_collapse (ws : Scheduler sys^w) (L' : List (Label × State)) (l : Label)
    (hl : ¬ l = Silent.τ) (μ : PMF State) (E : AlterSeq State Label) :
    (∑' seg : {seg : AlterSeq State Label //
        seg.trans.Terminates ∧ sys.trace seg = Seq.cons l Seq.nil ∧ sys.IsTight seg},
        ∑' t : Option (Label × PMF State),
          reachProb ws {canonCfg sys L' l E μ seg.1 with t := t})
      = (∑' c : {c : Config sys //
            c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E}, reachProb ws c.1)
        * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) := by
  have hseg_sum : (∑' seg : {seg : AlterSeq State Label //
      seg.trans.Terminates ∧ sys.trace seg = Seq.cons l Seq.nil ∧ sys.IsTight seg},
      (⟨PMF.pure (lastOf E), schedOf sys (lastOf E) l μ⟩
          : ProbabilisticExecution sys).probOf seg.1 seg.2.1)
      = sys.traceProb ⟨PMF.pure (lastOf E), schedOf sys (lastOf E) l μ⟩ (Seq.cons l Seq.nil) := rfl
  refine Eq.trans (tsum_congr (fun seg => con_factor_canon ws L' l μ E seg.1 seg.2.1)) ?_
  rw [ENNReal.tsum_mul_left, hseg_sum]
  set Q := (∑' c : {c : Config sys //
      c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E}, reachProb ws c.1) with hQ
  by_cases hstep : sys^w.step (lastOf E) l μ
  · rw [witness_traceProb_emit (schedOf_realises hstep) hl, mul_one]
  · have hz : Q * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) = 0 := by
      by_contra hne
      obtain ⟨hP0, hnext0⟩ := mul_ne_zero_iff.mp hne
      apply hstep
      have hfinL : (Seq.ofList L' : Seq (Label × State)).Terminates :=
        Stream'.Seq.terminates_ofList L'
      have hstate : (⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label).stateAt (Nat.find hfinL)
          = some (lastOf (⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label)) := by
        rw [lastOf_eq_endState _ hfinL]; exact AlterSeq.stateAt_find_eq_endState _ hfinL
      have hweak : sys^w.step (lastOf (⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label)) l μ :=
        ws.valid ⟨sys.init, Seq.ofList L'⟩ (Nat.find hfinL)
          (lastOf ⟨sys.init, Seq.ofList L'⟩) (Nat.find_spec hfinL) hstate l μ
          (PMF.mem_support_iff _ _ |>.mpr hnext0)
      have hlastEq : lastOf (⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label) = lastOf E := by
        obtain ⟨c', hc'⟩ : ∃ c' : {c : Config sys //
            c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E},
            reachProb ws c'.1 ≠ 0 := by
          by_contra hcon; push Not at hcon
          exact hP0 (by rw [hQ]; exact ENNReal.tsum_eq_zero.mpr hcon)
        have hend := reachProb_endpoint ws c'.1 hc'
        rw [c'.2.1, c'.2.2.2] at hend; exact hend
      rwa [hlastEq] at hweak
    rw [hz, zero_mul]

/-- The full invariant holds at every reachable configuration. -/
private theorem reachProb_Inv (ws : Scheduler sys^w) (c : Config sys) (h : reachProb ws c ≠ 0) :
    Inv c := by
  rw [reachProb] at h
  obtain ⟨n, hn⟩ : ∃ n, reachAfter ws n c ≠ 0 := by
    by_contra hcon; push Not at hcon; exact h (ENNReal.tsum_eq_zero.mpr hcon)
  exact reachAfter_Inv ws n c hn

omit [Silent Label] in
/-- A terminating append has a terminating left part. -/
private theorem terminates_of_append_left {α : Type*} (A B : Seq α)
    (h : (A.append B).Terminates) : A.Terminates := by
  by_contra hA
  obtain ⟨N, hN⟩ := h
  have hAk : ∀ k, ¬ A.TerminatedAt k := fun k hk => hA ⟨k, hk⟩
  exact hAk N ((Stream'.Seq.get?_append_before_length (hAk N)).symm.trans hN)

open Classical in
/-- **CON extraction.** A reachable arrival config `c` (`e'` a nonempty segment, `concat c` tight
with trace `τ' ⌢ [l]`) is the canonical config `canonCfg L' l c.e μw c.e'` for some entry list `L'`
of trace `τ'` and weak-step target `μw`; its segment `c.e'` is tight, terminating, and has trace
`[l]`. The active label equals `l` because the tight nonempty segment emits exactly `[l]`
(`witness_seg_trace`) and appending it to `trace c.e = trace c.we` recovers `τ' ⌢ [l]`. -/
private theorem con_config_shape (ws : Scheduler sys^w) (τ' : Seq Label) (l : Label)
    (c : Config sys) (hne : c.e'.trans ≠ Seq.nil)
    (htr : sys.trace (Config.concat c) = τ'.append (Seq.cons l Seq.nil))
    (htight : sys.IsTight (Config.concat c)) (hrp : reachProb ws c ≠ 0) :
    ∃ (L' : List (Label × State)) (μw : PMF State),
      c = {canonCfg sys L' l c.e μw c.e' with t := c.t} ∧
      sys.trace ⟨sys.init, Seq.ofList L'⟩ = τ' ∧
      c.e'.trans.Terminates ∧ sys.trace c.e' = Seq.cons l Seq.nil ∧ sys.IsTight c.e' := by
  have hInv := reachProb_Inv ws c hrp
  obtain ⟨hweinit, hwefin, hwtOr⟩ := reachProb_con_facts ws c hrp
  obtain ⟨⟨lw, μw⟩, hwt⟩ : ∃ p, c.wt = some p := hwtOr.resolve_left hne
  obtain ⟨hstepw, hsched, hprob⟩ := hInv.seg lw μw hwt
  have hReal : Realises (schedOf sys (lastOf c.e) lw μw) (lastOf c.e) lw μw :=
    schedOf_realises hstepw
  have hprob' : (⟨PMF.pure (lastOf c.e), schedOf sys (lastOf c.e) lw μw⟩
      : ProbabilisticExecution sys).probOf c.e' hInv.e'_fin ≠ 0 := hsched ▸ hprob
  have happ_fin : (c.e.trans.append c.e'.trans).Terminates :=
    ⟨_, Stream'.Seq.terminatedAt_append_find hInv.e_fin hInv.e'_fin.choose_spec⟩
  have he'tight : sys.IsTight c.e' :=
    (isTight_concat_iff c.e.trans c.e'.trans c.e.init c.e'.init hInv.e_fin hInv.e'_fin hne
      happ_fin).mp htight
  obtain ⟨htrace_seg, _⟩ :=
    witness_seg_trace hReal c.e' hInv.e'_fin hInv.e'_init hne he'tight hprob'
  -- Trace split: `trace concat = trace c.e ⌢ trace c.e' = trace c.e ⌢ [lw] = τ' ⌢ [l]`.
  have hsplit : sys.trace (Config.concat c) = (sys.trace c.e).append (sys.trace c.e') :=
    trace_append c.e.init c.e.trans c.e'.trans hInv.e_fin
  have heq : (sys.trace c.e).append (Seq.cons lw Seq.nil) = τ'.append (Seq.cons l Seq.nil) := by
    rw [← htrace_seg, ← hsplit]; exact htr
  have hte : (sys.trace c.e).Terminates := by
    rw [← filter_toList_eq_trace c.e hInv.e_fin]
    exact Stream'.Seq.terminates_filter _ _ (Stream'.Seq.terminates_ofList _)
  have hτ'term : τ'.Terminates := by
    refine terminates_of_append_left τ' (Seq.cons l Seq.nil) ?_
    rw [← heq]
    exact ⟨_, Stream'.Seq.terminatedAt_append_find hte
      (show (Seq.cons lw Seq.nil).TerminatedAt 1 from rfl)⟩
  have hlweq : lw = l :=
    Stream'.Seq.append_singleton_inj_right (sys.trace c.e) τ' hte hτ'term lw l heq
  have htrace_e : sys.trace c.e = τ' :=
    Stream'.Seq.append_singleton_inj_left (sys.trace c.e) τ' hte hτ'term lw l heq
  rw [hlweq] at hwt hsched htrace_seg
  obtain ⟨L', hwe_eq⟩ : ∃ L', c.we = ⟨sys.init, Seq.ofList L'⟩ :=
    ⟨c.we.trans.toList hwefin, by rw [Stream'.Seq.ofList_toList c.we.trans hwefin, ← hweinit]⟩
  refine ⟨L', μw, ?_, ?_, hInv.e'_fin, htrace_seg, he'tight⟩
  · calc c = ⟨c.we, c.e, c.wt, c.s, c.e', c.t⟩ := rfl
      _ = ⟨⟨sys.init, Seq.ofList L'⟩, c.e, some (l, μw),
            schedOf sys (lastOf c.e) l μw, c.e', c.t⟩ := by rw [hwe_eq, hwt, hsched]
      _ = {canonCfg sys L' l c.e μw c.e' with t := c.t} := rfl
  · rw [← hwe_eq, reachProb_trace_eq ws c hrp]; exact htrace_e

open Classical in
/-- **CON construction.** The canonical config `canonCfg L' l E μ seg` (with any inner draw `t`) is
a valid CON arrival config for the trace `τ' ⌢ [l]`, provided its entry list `L'` has trace `τ'` and
its segment `seg` is tight, terminating, with trace `[l]`. -/
private theorem canonCfg_con (ws : Scheduler sys^w) (τ' : Seq Label) (l : Label)
    (L' : List (Label × State)) (E seg : AlterSeq State Label) (μ : PMF State)
    (t : Option (Label × PMF State))
    (hL' : sys.trace ⟨sys.init, Seq.ofList L'⟩ = τ')
    (hsegT : seg.trans.Terminates) (hsegtr : sys.trace seg = Seq.cons l Seq.nil)
    (hsegtight : sys.IsTight seg)
    (hrp : reachProb ws { canonCfg sys L' l E μ seg with t := t } ≠ 0) :
    { canonCfg sys L' l E μ seg with t := t }.e'.trans ≠ Seq.nil ∧
      (Config.concat {canonCfg sys L' l E μ seg with t := t}).trans.Terminates ∧
      sys.trace (Config.concat {canonCfg sys L' l E μ seg with t := t})
        = τ'.append (Seq.cons l Seq.nil) ∧
      sys.IsTight (Config.concat {canonCfg sys L' l E μ seg with t := t}) := by
  set cc := ({canonCfg sys L' l E μ seg with t := t} : Config sys) with hcc
  have hccE : cc.e = E := rfl
  have hccSeg : cc.e' = seg := rfl
  have hEfin : cc.e.trans.Terminates := (reachProb_inv ws cc hrp).1
  have hsegne : seg.trans ≠ Seq.nil := by
    intro h0
    have h1 : sys.trace seg = Seq.cons l Seq.nil := hsegtr
    simp only [System.trace, h0, Stream'.Seq.filter_nil, Stream'.Seq.map_nil] at h1
    exact Stream'.Seq.cons_ne_nil h1.symm
  have hcatfin : (Config.concat cc).trans.Terminates :=
    ⟨_, Stream'.Seq.terminatedAt_append_find hEfin hsegT.choose_spec⟩
  have htraceE : sys.trace cc.e = τ' := by
    rw [← reachProb_trace_eq ws cc hrp]; exact hL'
  have htracecat : sys.trace (Config.concat cc) = τ'.append (Seq.cons l Seq.nil) := by
    rw [show sys.trace (Config.concat cc) = (sys.trace cc.e).append (sys.trace cc.e') from
        trace_append cc.e.init cc.e.trans cc.e'.trans hEfin,
      show sys.trace cc.e' = Seq.cons l Seq.nil from hsegtr, htraceE]
  have htightcat : sys.IsTight (Config.concat cc) :=
    (isTight_concat_iff cc.e.trans cc.e'.trans cc.e.init cc.e'.init hEfin hsegT hsegne
      hcatfin).mpr hsegtight
  exact ⟨hsegne, hcatfin, htracecat, htightcat⟩

open Classical in
/-- **CON reindexing.** The arrival-config sum reindexes bijectively onto tuples
`(L', E, μ, seg, t)` — entry list `L'` (trace `τ'`), committed concrete prefix `E`, weak-step target
`μ`, tight trace-`[l]` segment `seg`, inner draw `t` — via the canonical config
`canonCfg L' l E μ seg` (`con_config_shape` extracts the tuple from a reachable arrival config;
`canonCfg_con` builds a CON config from a tuple). -/
private theorem con_bij (ws : Scheduler sys^w) (τ' : Seq Label) (l : Label) :
    (∑' c : {c : Config sys // c.e'.trans ≠ Seq.nil ∧ (Config.concat c).trans.Terminates ∧
        sys.trace (Config.concat c) = τ'.append (Seq.cons l Seq.nil) ∧
        sys.IsTight (Config.concat c)}, reachProb ws c.1)
      = ∑' q : {L : List (Label × State) // sys.trace ⟨sys.init, Seq.ofList L⟩ = τ'}
          × AlterSeq State Label × PMF State
          × {seg : AlterSeq State Label //
              seg.trans.Terminates ∧ sys.trace seg = Seq.cons l Seq.nil ∧ sys.IsTight seg}
          × Option (Label × PMF State),
          reachProb ws {canonCfg sys q.1.1 l q.2.1 q.2.2.1 q.2.2.2.1.1 with t := q.2.2.2.2} := by
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun q => ⟨{canonCfg sys q.1.1.1 l q.1.2.1 q.1.2.2.1 q.1.2.2.2.1.1
        with t := q.1.2.2.2.2},
      canonCfg_con ws τ' l q.1.1.1 q.1.2.1 q.1.2.2.2.1.1 q.1.2.2.1 q.1.2.2.2.2
        q.1.1.2 q.1.2.2.2.1.2.1 q.1.2.2.2.1.2.2.1 q.1.2.2.2.1.2.2.2 q.2⟩) ?_ ?_ ?_
  · -- injective on support
    rintro ⟨⟨⟨L'a, hL'a⟩, Ea, μa, ⟨sega, hsega⟩, ta⟩, hqa⟩
      ⟨⟨⟨L'b, hL'b⟩, Eb, μb, ⟨segb, hsegb⟩, tb⟩, hqb⟩ hab
    have hcfg := Subtype.ext_iff.mp hab
    have hL'eq : L'a = L'b :=
      Stream'.Seq.ofList_injective (congrArg AlterSeq.trans (congrArg Config.we hcfg))
    have hEeq : Ea = Eb := congrArg Config.e hcfg
    have hμeq : μa = μb :=
      (Prod.mk.inj (Option.some.inj (congrArg Config.wt hcfg))).2
    have hsegeq : sega = segb := congrArg Config.e' hcfg
    have hteq : ta = tb := congrArg Config.t hcfg
    subst hL'eq; subst hEeq; subst hμeq; subst hsegeq; subst hteq; rfl
  · -- support ⊆ range
    intro a ha
    obtain ⟨L', μw, hceq, hL', hsegT, hsegtr, hsegtight⟩ :=
      con_config_shape ws τ' l a.1 a.2.1 a.2.2.2.1 a.2.2.2.2 ha
    have hq : reachProb ws {canonCfg sys L' l a.1.e μw a.1.e' with t := a.1.t} ≠ 0 := by
      rw [← hceq]; exact ha
    exact ⟨⟨⟨⟨L', hL'⟩, a.1.e, μw, ⟨a.1.e', hsegT, hsegtr, hsegtight⟩, a.1.t⟩, hq⟩,
      Subtype.ext hceq.symm⟩
  · -- values agree
    rintro ⟨⟨⟨L', hL'⟩, E, μ, ⟨seg, hseg⟩, t⟩, hq⟩; rfl

open Classical in
/-- **Per-entry collapse (CON side).** Fixing the entry list `L'` (trace `τ'`), summing over the
committed prefix `E`, weak-step target `μ`, tight trace-`[l]` segment, and inner draw `t` factors as
the entry-`L'` reach times the total `(l, ·)`-mass: `con_seg_collapse` collapses each `(E, μ)`
segment sum, and `predSum_partition` rebuilds `predSum L'` over `E`. -/
private theorem con_perL (ws : Scheduler sys^w) (τ' : Seq Label) (l : Label) (hl : ¬ l = Silent.τ)
    (L' : {L : List (Label × State) // sys.trace ⟨sys.init, Seq.ofList L⟩ = τ'}) :
    (∑' rest : AlterSeq State Label × PMF State
        × {seg : AlterSeq State Label //
            seg.trans.Terminates ∧ sys.trace seg = Seq.cons l Seq.nil ∧ sys.IsTight seg}
        × Option (Label × PMF State),
        reachProb ws {canonCfg sys L'.1 l rest.1 rest.2.1 rest.2.2.1.1 with t := rest.2.2.2})
      = (∑' c : {c : Config sys //
            c.we = ⟨sys.init, Seq.ofList L'.1⟩ ∧ c.e'.trans = Seq.nil}, reachProb ws c.1)
        * ∑' μ : PMF State, ws.next ⟨sys.init, Seq.ofList L'.1⟩ (some (l, μ)) := by
  rw [ENNReal.tsum_prod']
  have hinner : ∀ E : AlterSeq State Label,
      (∑' r : PMF State × {seg : AlterSeq State Label // seg.trans.Terminates ∧
            sys.trace seg = Seq.cons l Seq.nil ∧ sys.IsTight seg} × Option (Label × PMF State),
          reachProb ws {canonCfg sys L'.1 l E r.1 r.2.1.1 with t := r.2.2})
        = ∑' μ : PMF State,
            (∑' c : {c : Config sys // c.we = ⟨sys.init, Seq.ofList L'.1⟩ ∧
                c.e'.trans = Seq.nil ∧ c.e = E}, reachProb ws c.1)
              * ws.next ⟨sys.init, Seq.ofList L'.1⟩ (some (l, μ)) := by
    intro E
    rw [ENNReal.tsum_prod']
    refine tsum_congr (fun μ => ?_)
    rw [ENNReal.tsum_prod']
    exact con_seg_collapse ws L'.1 l hl μ E
  rw [tsum_congr hinner, ENNReal.tsum_comm,
    tsum_congr (fun μ => by rw [ENNReal.tsum_mul_right, predSum_partition ws L'.1]),
    ENNReal.tsum_mul_left]

/-- **CON = base.** The arrival-config sum reindexes (`con_bij`) onto tuples `(L', E, μ, seg, t)`;
summing out `(E, μ, seg, t)` per entry list `L'` (`con_perL`) rebuilds the common base `baseSum`. -/
private theorem con_eq_baseSum (ws : Scheduler sys^w) (τ' : Seq Label) (l : Label)
    (hl : ¬ l = Silent.τ) :
    (∑' c : {c : Config sys // c.e'.trans ≠ Seq.nil ∧ (Config.concat c).trans.Terminates ∧
        sys.trace (Config.concat c) = τ'.append (Seq.cons l Seq.nil) ∧
        sys.IsTight (Config.concat c)}, reachProb ws c.1)
      = baseSum ws τ' l := by
  rw [con_bij ws τ' l, ENNReal.tsum_prod']
  unfold baseSum
  exact tsum_congr (fun L' => con_perL ws τ' l hl L')

private theorem abs_eq_con (ws : Scheduler sys^w) (τ : Seq Label) (hτ : τ ≠ Seq.nil) :
    (∑' c : {c : Config sys // c.e'.trans = Seq.nil ∧ c.we.trans.Terminates ∧
        sys.trace c.we = τ ∧ sys.IsTight c.we}, reachProb ws c.1)
      = ∑' c : {c : Config sys // c.e'.trans ≠ Seq.nil ∧ (Config.concat c).trans.Terminates ∧
          sys.trace (Config.concat c) = τ ∧ sys.IsTight (Config.concat c)}, reachProb ws c.1 := by
  by_cases hsplit : ∃ (τ' : Seq Label) (l : Label),
      ¬ l = Silent.τ ∧ τ = τ'.append (Seq.cons l Seq.nil)
  · obtain ⟨τ', l, hl, hτeq⟩ := hsplit
    subst hτeq
    rw [abs_eq_baseSum ws τ' l hl, con_eq_baseSum ws τ' l hl]
  · -- No external-final decomposition of `τ`: both sides are empty sums (`0`).
    have hA : (∑' c : {c : Config sys // c.e'.trans = Seq.nil ∧ c.we.trans.Terminates ∧
          sys.trace c.we = τ ∧ sys.IsTight c.we}, reachProb ws c.1) = 0 :=
      ENNReal.tsum_eq_zero.mpr (fun c =>
        (hsplit (exists_split_of_tight τ c.1.we c.2.2.1 c.2.2.2.1 c.2.2.2.2 hτ)).elim)
    have hC : (∑' c : {c : Config sys // c.e'.trans ≠ Seq.nil ∧
          (Config.concat c).trans.Terminates ∧ sys.trace (Config.concat c) = τ ∧
          sys.IsTight (Config.concat c)}, reachProb ws c.1) = 0 :=
      ENNReal.tsum_eq_zero.mpr (fun c =>
        (hsplit (exists_split_of_tight τ (Config.concat c.1) c.2.2.1 c.2.2.2.1 c.2.2.2.2 hτ)).elim)
    rw [hA, hC]

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
