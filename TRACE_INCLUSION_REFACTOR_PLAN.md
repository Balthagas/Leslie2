# Trace-inclusion refactor plan: returning to plan §2

Generated 2026-06-04. Companion to `TRACE_INCLUSION_PLAN.txt`.

## 1. Divergences found

| # | Location | Plan says | Code does | Severity |
|---|----------|-----------|-----------|----------|
| **D1** | `Simulation.lean:2506` (`weakClosure`) | `sys_A^w.step s l μ ↔ weakStep sys_A (PMF.pure s) l μ` (plan §2 line 273) | `∃ μ_A ω, s ∈ μ_A.support ∧ μ ∈ ω.support ∧ (weakTau μ_A (ω.bind id) ∨ weakStep μ_A l (ω.bind id))` (self-flagged) | **Structural — weakens theorem** |
| **D2** | `Simulation.lean:2833` (`blockEmission_general`) | `PMF.map (fun s_A => (l_C, PMF.pure s_A)) (γ.bind (fun (_, μ) => μ))` — emits Dirac at sampled `s_A` (plan §2 line 334-340) | `ω.map (fun μ_A_next => (lμ.1, μ_A_next))` — emits the full `μ_A_next : PMF State_A` from `ω`'s support (self-flagged) | **Structural — coupled with D1** |
| **D3** | `Simulation.lean:6683` (`traceInclusion` signature) | Plan §1 (lines 229-241) states the theorem with 5 hypotheses; no `h_internal`. | Adds `(h_internal : ∀ l, sys_C.internal l ↔ sys_A.internal l)`. | **Structural — strengthens hypothesis** |
| **D4** | Stale checklist | Plan §10 lines 1424-1454 mark `joint_marginalises_to_pe_C/A` and `traceInclusion` as `[ ]`. | All proven. | Cosmetic / doc lag. |
| **D5** | Plan sub-lemma naming | Plan §10 lines 1430, 1441 lists `joint_mass_path_append_singleton` and `joint_mass_path_eq_m_kernel_aggregate` as separate sub-lemmas. | Inlined; alternative route via `joint_mass_path_aug` + `chain_weight`. | Cosmetic — equivalent content. |

D1 and D2 are the **load-bearing** divergences: D1 alone would be a definition mismatch; together with D2 they cascade into pe_A's kernel formula and every downstream sub-lemma (§3.2, §9.3) that touches pe_A's emission.

D3 is real and probably mathematically necessary, but it should be raised explicitly with the user (plan author).

D4–D5 are documentation hygiene.

## 2. Refactor goals

**Primary**: Bring `weakClosure` and `blockEmission_general` to the plan's exact form. The theorem statement must read

```
∃ pe_A : PMFProbabilisticExecution (sys_A^w), ∀ τ, sys_C.traceProb pe_C τ = (sys_A^w).traceProbPMF pe_A τ
```

with `sys_A^w.step s l μ := weakStep sys_A (PMF.pure s) l μ` and `pe_A.scheduler` emitting `PMF.pure s_A` shapes.

**Secondary**: Either justify or remove `h_internal`. Update the plan's §10 checklist.

## 3. Why the deviation cascaded (root cause)

The validity field of a `PMFProbabilisticExecution sys` requires: for every history `e`, every prefix index `n`, every emitted `(l, μ)`, `sys.step (e.endState) l μ` holds. For pe_A over `sys_A^w` strict, this is

```
weakStep sys_A (PMF.pure (e.endState)) l μ
```

— a τ-closure → labeled hyperStep → τ-closure chain *starting from a Dirac on the single state `e.endState`*.

Sim's `stepWitness` delivers `weakStep sys_A μ_A l (ω.bind id)` where `μ_A` is the matching-state's *distributional* witness (not a Dirac), and `(ω.bind id)` is the post-step distribution (not necessarily a Dirac either).

To bridge: from sim's distributional weakStep, project down to a Dirac → Dirac weakStep at the specific pair `(e.endState, s_A)` for each `s_A` in the post-state distribution's support. Plan §6 (the "single trajectory" decomposition) sketches this.

The code's author bypassed this projection by relaxing both ends:
- relaxed `weakClosure` (D1) to accept distributional sources and `ω`-membership destinations,
- and emitted the distributional `μ_A_next` directly (D2) so the validity proof can hand sim's witness straight in.

This works as a Lean proof but it isn't the theorem the plan promises.

## 4. The trajectory-level bridge — what we need to prove

Define (this is the missing infrastructure):

**Lemma WS-Pure-Pure**: Given
- a matching state `m` with `m.has_valid_R`,
- `s_A_endState ∈ m.current_μ_A.support` (the current abstract endpoint from the history's last position),
- `pe_C.scheduler.next m.e_C = some d`,
- `(l_C, μ_C) ∈ d.support`,
- `s_A_next ∈ (sim.stepWitness (m.current_R _) (pe_C_step_witness ... l_C μ_C _)).bind id . support`,

then

```
weakStep sys_A (PMF.pure s_A_endState) l_C (PMF.pure s_A_next).
```

**Proof sketch**: `m.current_R : R m.current_s_C m.current_μ_A` and the simulation relation R between concrete states and abstract distributions has a "support-projection" property: for each `s_A ∈ μ_A.support`, R relates `s_C` to a Dirac at `s_A` via a τ-closure (i.e., `weakTau sys_A (PMF.pure s_A) μ_A`). This is the τ-closure-of-supports lemma.

Specifically:
1. `m.current_μ_A`'s support contains `s_A_endState`. The Dirac `PMF.pure s_A_endState` τ-closes to `m.current_μ_A` (since `s_A_endState` is a single element of `m.current_μ_A`'s support — but **this requires sim's R to preserve that property, which is not built-in**).
2. Once we have `weakTau (PMF.pure s_A_endState) m.current_μ_A`, sim's `stepWitness_weakStep` gives `weakStep m.current_μ_A l_C ((sim.stepWitness …).bind id)`, providing the labeled middle step (with the τ-closure preceding it).
3. The post-step distribution `(sim.stepWitness …).bind id` contains `s_A_next` in its support; we need another τ-closure to project to `PMF.pure s_A_next`. This is the "support → Dirac" τ-closure, which is **NOT generally true** for an arbitrary sys_A.

So **Lemma WS-Pure-Pure does not hold in general**. The plan's strict `weakClosure` is too strong without an additional structural assumption on sys_A.

This is a real problem. Possibilities:

**Option A**: Add an axiom or structural hypothesis on sys_A enforcing "Diracs τ-close into supports and vice versa" — e.g., `∀ μ_A s_A, s_A ∈ μ_A.support → weakTau sys_A (PMF.pure s_A) μ_A ∧ weakTau sys_A μ_A (PMF.pure s_A)`. Then WS-Pure-Pure holds and pe_A's emission can produce Diracs.

**Option B**: Match the plan literally on `weakClosure` but allow non-Dirac emissions — i.e., keep D2 and only fix D1. The validity then becomes: for each emitted `(l, μ_A_next)`, `weakStep sys_A (PMF.pure s_A_endState) l μ_A_next`. This needs `weakTau (PMF.pure s_A_endState) m.current_μ_A`, then `weakStep m.current_μ_A l (ω.bind id)`, then `weakTau (ω.bind id) μ_A_next`. The first τ-closure is the Dirac-into-support one (still requires the support→Dirac assumption); the last is `ω.bind id` τ-closing to one of its support members `μ_A_next`. Wait — `ω.bind id` is a `PMF State_A`, but `μ_A_next : PMF State_A` is *not* a state of `ω.bind id` — it's a `PMF`-valued element of `ω.support`. Type mismatch. Option B doesn't fit.

**Option C**: Re-interpret the plan's Dirac formula via a different decomposition that is provable from sim alone. Re-read plan §6 carefully (lines 1546-1635 mention σ_pre/σ_post and "label-purity") — the plan may have an intermediate "flattening construction" in mind that synthesizes the Dirac → Dirac chain.

I believe the **honest answer** is Option A with an additional structural assumption added to `ProbabilisticForwardSimulation` or to `traceInclusion`'s hypotheses. We should consult the plan author before fixing.

## 5. Step-by-step refactor (assuming Option A)

**Stage 0 — alignment (BEFORE any code change):**

0.1. Update `TRACE_INCLUSION_PLAN.txt`:
- Refresh §10 checklist (D4): move `joint_marginalises_to_pe_C`, `joint_marginalises_to_pe_A`, `traceInclusion` from `[ ]` to `[✓]`.
- Add a §10 sub-bullet acknowledging `joint_mass_path_append_singleton` and `joint_mass_path_eq_m_kernel_aggregate` were replaced by `joint_mass_path_aug` + `chain_weight` and adapt the wording (D5).
- Add the new structural assumption (e.g., "Dirac-τ-closure" property of sys_A) to the plan's hypothesis list.
- Document `h_internal` (D3) explicitly in the plan, OR delete it after confirming with the author that sys_C.internal = sys_A.internal is intended to be derivable from R.

0.2. Get sign-off on Option A vs. B vs. C from the plan author **before touching code**.

**Stage 1 — definition change (smallest possible diff):**

1.1. Replace `weakClosure` body (`Simulation.lean:2506-2512`) with
```lean
def weakClosure (sys_A : LabelledSystem State_A Label) :
    LabelledSystem State_A Label where
  init := sys_A.init
  step s l μ := weakStep sys_A (PMF.pure s) l μ
  internal := sys_A.internal
```
1.2. Delete the deviation comment (lines 2495-2505).

1.3. **Expected immediate breakage**: `pe_A_of_simulation.valid` (`Simulation.lean:3386-3410`) — the existing `refine ⟨m.current_μ_A, ..., Or.inl/Or.inr⟩` pattern no longer typechecks. Replace with a single `weakStep` witness construction (no Or, no ω, no μ_A).

**Stage 2 — emission shape (D2):**

2.1. Replace `blockEmission_general` body (`Simulation.lean:2833-2852`) with the plan's form:
```lean
noncomputable def blockEmission_general ... : PMF (Label × PMF State_A) :=
  d.bind (fun lμ =>
    if h_supp : (lμ.1, lμ.2) ∈ d.support then
      let ω := sim.stepWitness (m.current_R h_valid) ...
      PMF.map (fun s_A => (lμ.1, PMF.pure s_A)) (ω.bind id)
    else
      PMF.pure (lμ.1, PMF.pure sys_A.init))
```

2.2. `blockEmission_general_apply_eq` (`Simulation.lean:2857+`) — re-derive the flat tsum form. Now `blockEmission_general m d h_d_eq h_valid (l, μ)` is nonzero only when `μ = PMF.pure s_A` for some `s_A`. Express `blockEmission_general m d _ _ (l, PMF.pure s_A) = ∑' μ_C, d (l, μ_C) * (ω.bind id) s_A` (when in support).

2.3. **Expected cascade**: every downstream sub-lemma referring to `blockEmission_general` updates. Specifically:
- `blockEmission_general_emission_marginal_at_d` and `_emission_marginal` (~line 3973): the marginal over `μ` for `μ s_A` becomes a marginal over Dirac states.
- `pe_A_kernel_via_m_kernel` — the kernel formula's RHS structure remains, but its derivation walks through the new emission shape.
- `m_dist_posterior_predictive_with_mass` and `m_dist_posterior_predictive` — the per_state_kernel identification still holds; only the intermediate algebra changes.

**Stage 3 — re-prove validity:**

3.1. Add the Dirac-τ-closure structural assumption. Two locations to choose from:
- (a) Add a field to `ProbabilisticForwardSimulation` requiring sys_A satisfies it.
- (b) Add a hypothesis `(h_dirac_tau : ∀ μ s_A, s_A ∈ μ.support → weakTau sys_A (PMF.pure s_A) μ ∧ weakTau sys_A μ (PMF.pure s_A))` to `pe_A_of_simulation` and `traceInclusion`.

Prefer (a) — it sits next to other simulation assumptions and only one user needs to discharge it. Update plan §2 accordingly.

3.2. Prove `WS-Pure-Pure` (Section 4 above) as a standalone private lemma.

3.3. Rewrite `pe_A_of_simulation.valid` (`Simulation.lean:3386-3410`) using WS-Pure-Pure: given history's endState s, emitted `(l, PMF.pure s_A_next)`, construct `weakStep sys_A (PMF.pure s) l (PMF.pure s_A_next)`.

**Stage 4 — joint-kernel sanity check:**

4.1. `joint_kernel` (`Simulation.lean:3527`) takes `(m, l, s_C, s_A)` and is defined as

```
∑' μ_C, d(l, μ_C) * (if h_supp then ∑' μ_A_next : PMF State_A, γ(s_C, μ_A_next) * μ_A_next s_A else 0)
```

This formulation already integrates over `μ_A_next` and then samples `s_A` from it — *matches the plan-style emission*. So `joint_kernel`'s definition needs **no change**.

4.2. Re-verify that `pe_A_kernel_via_m_kernel`'s proof still goes through. The pe_A.kernel formula (under PMF.pure emissions) becomes
```
pe_A.kernel history_A (l, s_A) = ∑' m, m_kernel(m) * ∑' μ_C, d(l, μ_C) * (ω.bind id) s_A
```
which expands to the same per_state_kernel multiplied through. Algebra is equivalent.

**Stage 5 — h_internal (D3):**

5.1. Search the plan and convince myself (and the user) whether `sys_C.internal = sys_A.internal` is implicit or whether the plan author intends a different formulation.

5.2. Two outcomes:
- (a) Confirmed implicit: enforce equality at the type level (a coercion or field) so the hypothesis is automatic and the theorem signature matches the plan.
- (b) Genuinely missing: leave `h_internal` in, and add a §1 note to the plan acknowledging it.

**Stage 6 — verification:**

6.1. `lake build MyMathlibProject.Simulation` is green with only the pre-existing 1541 sorry.

6.2. Inspect the theorem statement of `traceInclusion` and confirm it reads exactly the plan's form (modulo h_internal per §5).

6.3. Re-run the audit (the agent in this conversation) against the new state. Expected: no remaining D1/D2/D3 divergences.

## 6. Procedural safeguards (to prevent recurrence)

The original mistake: the code's author silently relaxed `weakClosure` to make a downstream proof tractable, with only a docstring comment as a record. Future development should require:

**S1 — Plan-anchor docstrings.** Every named declaration that has a corresponding plan section must include the plan reference in its docstring (e.g., `**Plan §2.** ... -/`). Diff PR template should require listing the relevant plan sections.

**S2 — Deviation manifest.** Any deviation from the plan must be recorded in a single top-of-file `/-! ## Plan deviations -/` section (currently scattered through docstrings). Each entry: plan citation, code citation, justification, sign-off status. This is the "deviation manifest" — a single grep target.

**S3 — CI faithfulness check (lightweight).** A script (Python or grep-based) that:
- Lists every `\lean{X}` claim in `blueprint/src/content.tex` and verifies X exists in the code.
- Lists every named theorem in §10 of `TRACE_INCLUSION_PLAN.txt` and verifies the code has a declaration with the same name and a matching statement (signature normalized — return type only, ignoring hypothesis ordering).
- For declarations marked `[✓]` in the plan, asserts the code has them. For `[ ]`, asserts there's still a sorry or that the plan is updated.

This is a one-off ~100 line script that runs in CI alongside `lake build`. It would have caught D4 immediately and surfaced D1/D2/D3 if their docstrings or signatures had diverged from the plan citations.

**S4 — Definition-frozen list.** A `frozen_definitions.txt` listing names whose definitions are NOT allowed to change without an explicit annotation. `weakClosure`, `blockEmission_general`, `joint_kernel`, `joint_mass_path`, `MatchingState`, `fromAbstractPrefix`, the headline theorem statements. PR review checks any changes to these against the plan.

**S5 — Sub-agent prompting.** When delegating Lean proof work to sub-agents, the prompt must include
- the plan-cited definitions of any names the agent will touch,
- an explicit "no relaxing definitions" instruction,
- a verification step at the end: re-check that the proven theorem's statement matches the plan.

S5 is the most practical lesson from this session — the §9.5 sub-agent never checked whether its assumptions about `sys_A^w` agreed with the plan, because the surrounding code already contained the relaxation.

## 7. Effort estimate

- Stage 0 (alignment): 0.5 day, but blocking on plan author input.
- Stage 1 (weakClosure swap): 0.5 day.
- Stage 2 (blockEmission_general): 1 day; cascades 2-3 sub-lemma rederivations.
- Stage 3 (validity + WS-Pure-Pure + Dirac-τ-closure assumption): 1-2 days. This is the load-bearing technical work.
- Stage 4 (joint kernel sanity): 0.5 day (mostly re-running and confirming).
- Stage 5 (h_internal): 0.5 day if (a), 0 if (b).
- Stage 6 (verification): 0.5 day.

Total: **4-5 days** of focused work assuming Option A.

## 8. What I need from you

- Decision on Option A vs. B vs. C (Section 4).
- Decision on h_internal (Section 5.5 — D3).
- Confirmation that `joint_mass_path_append_singleton` / `joint_mass_path_eq_m_kernel_aggregate` may stay inlined (D5).
- Approval before I touch any code.
