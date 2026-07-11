# leslie2 — Probabilistic Labelled Transition Systems in Lean 4

A Lean 4 + Mathlib formalization of **probabilistic labelled transition systems
(PLTS)** and the **trace-distribution soundness of probabilistic simulations**.
PLTS are the foundational model for reasoning about randomized programs and
protocols; the headline results say that if one system *simulates* another, then
every observable-trace distribution of the concrete system is reproducible by the
abstract one.

> **Naming note.** The repository is called *leslie2* (GitHub, blueprint), but the
> Lake package and Lean root module are `MyMathlibProject` — the rename was never
> propagated. Every module path below is therefore `MyMathlibProject.…`.

## Main results

Everything is stated for a canonical silent label `τ` (`class Silent`), so the
internal/external partition is a property of the *label type*, not of an
individual system.

| Result | Statement | Lives in |
| --- | --- | --- |
| `StrongProbabilisticSimulation.achievableTraceDists_subset` | strong simulation ⇒ trace-distribution inclusion | `Simulation/Trace.lean` |
| `WeakProbabilisticSimulation.achievableTraceDists_subset` | weak simulation ⇒ trace-distribution inclusion | `Simulation/Soundness.lean` |
| `ProbabilisticForwardSimulation.achievableTraceDists_subset` | forward simulation ⇒ trace-distribution inclusion | `Simulation/Soundness.lean` |
| `weakClosure_traceProb_eq` | the weak closure `sys^w` preserves achievable trace distributions | `Expansion/TraceProb.lean` |
| `dist_traceProb_eq` | the distribution-monad lift `𝒟(sys)` preserves achievable trace distributions | `Construction/DistTrace.lean` |
| `achievableTraceDists_map` | a functional label-preserving simulation preserves trace distributions (reusable engine) | `Construction/TraceMap.lean` |

**How they fit together.** Strong-simulation soundness is proved directly. Weak
and forward simulation each turn out to be *the same data* as a strong simulation
into a transformed abstract system — `sys^w` (weak closure) and `𝒟(sys^w)`
(distribution-monad lift of the weak closure) respectively — via the two
equivalences in `Simulation/Equivalences.lean`. Those reductions are sound because
both transformations preserve achievable trace distributions
(`weakClosure_traceProb_eq`, `dist_traceProb_eq`). The hardest part of the whole
development is the `Expansion/` pipeline, which proves the non-trivial `sys^w ⊆
sys` trace inclusion by unfolding each abstract weak step `τ*·l·τ*` into a concrete
`sys`-path.

## Project layout

Files are grouped into thematic folders that follow the dependency order (each
layer imports only earlier ones). Within a layer, **helper** files gather lemmas
around a common theme and **result** files (marked ★) state the theorems above.

```
MyMathlibProject/
├── Util/            — generic helper lemmas, independent of PLTS
│   ├── Seq.lean         Stream'.Seq lemmas (append / filter / toList)
│   └── Pmf.lean         PMF.pure / PMF.map helpers
│
├── Model/           — the PLTS model and its trace semantics
│   ├── System.lean      System, AlterSeq (executions), ProbabilisticExecution
│   ├── Trace.lean       Silent (canonical τ), trace, IsTight, traceProb,
│   │                    achievableTraceDists
│   └── Composition.lean CSP-style parallel composition (System.parallel)
│
├── Weak/            — scheduler bind-calculus and weak transitions
│   ├── Scheduler.lean   WeakScheduler, haltMass, Scheduler.bind, bind_haltMass
│   ├── Step.lean        weakTau, hyperStep, weakStep, weakTau_trans
│   └── Bounds.lean      Kraft / antichain mass bounds, haltMass_tsum_le_one
│
├── Construction/    — constructions that build new systems from old
│   ├── EndState.lean    AlterSeq.endState helper lemmas
│   ├── TraceMap.lean    achievableTraceDists_map (functional-simulation soundness)
│   ├── DistMonad.lean   the 𝒟(sys) construction + easy trace inclusion
│   ├── DistTrace.lean   ★ dist_traceProb_eq (𝒟 preserves traces — the hard half)
│   └── WeakClosure.lean the weak closure sys^w
│
├── Expansion/       — proves the hard direction: sys^w ⊆ sys on traces
│   ├── Algorithm.lean   unfolding algorithm: configurations, reachProb, Realises
│   ├── Trace.lean       reachable configs have matching abstract/concrete traces
│   ├── ProbOf.lean      trajectory probability = configuration reaching probability
│   ├── Scheduler.lean   expandSched: the concrete scheduler realising the unfolding
│   └── TraceProb.lean   ★ weakClosure_traceProb_eq
│
└── Simulation/      — the simulation notions and their soundness
    ├── Defs.lean        PMFRel + Strong / Weak / Forward simulation structures
    ├── WeakChar.lean    weak-transition workhorse lemmas (weakTau_bind, …)
    ├── Equivalences.lean weak/forward sim = strong sim into sys^w / 𝒟(sys^w)
    ├── Trace.lean       ★ strong-simulation trace soundness
    └── Soundness.lean   ★ weak- and forward-simulation trace soundness
```

`MyMathlibProject.lean` is the root module; it simply re-exports every file above
(kept in sync by `lake exe mk_all`).

### Dependency flow

```
Util ─┐
      ├─▶ Model ─▶ Weak ─▶ Construction ─▶ Expansion ─┐
      │                         │                     ├─▶ Simulation/Soundness ★
      │                         └─▶ Simulation/{Defs,WeakChar,Equivalences,Trace ★}
```

### Helper vs. result files

- **Helper files** collect lemmas around one theme: `Util/*`, `Weak/Bounds`,
  `Construction/EndState`, `Simulation/WeakChar`, and the intermediate stages of
  `Expansion/` (`Algorithm`, `Trace`, `ProbOf`, `Scheduler`).
- **Definition files** introduce the objects: `Model/*`, `Weak/{Scheduler,Step}`,
  `Construction/{DistMonad,WeakClosure}`, `Simulation/Defs`.
- **Result files (★)** state the theorems in the table above:
  `Construction/{TraceMap,DistTrace}`, `Expansion/TraceProb`,
  `Simulation/{Trace,Soundness}`.

Two originally-monolithic files were split along their helper/result seam:
`Simulation/` was `Simulation.lean` (definitions + workhorse lemmas + equivalence
results); `Construction/{DistMonad,DistTrace}` was `DistConstruction.lean` (the
small `𝒟` construction + its ~1200-line trace-preservation proof).

## Building

The toolchain is pinned in `lean-toolchain` and the Mathlib revision in
`lakefile.toml`; the two must stay in lockstep.

```bash
lake exe cache get                        # fetch the Mathlib build cache (first time)
lake build                                # build the whole project
lake build MyMathlibProject.Model.System  # build a single module
lake exe mk_all --check                   # check the root re-exports every file (CI)
```

There is no test suite. CI (`.github/workflows/blueprint.yml`) runs the build plus
`mk_all --check`, then compiles the blueprint and API docs to GitHub Pages on every
push to `master`. Linting is intentionally off in CI (warnings show locally but do
not fail the build).

## Blueprint & conventions

The mathematical write-up is a Lean blueprint under `blueprint/src/`
(`content.tex` is the content; `web.tex` / `print.tex` are the entry points). It
cross-links to Lean declarations by their **fully-qualified name** (e.g.
`PLTS.dist_traceProb_eq`), which this reorganization leaves unchanged — every
declaration still lives in `namespace PLTS`, so only file locations moved. The
published site is at <https://Balthagas.github.io/Leslie2>.

Coding conventions (Mathlib license header, `namespace PLTS … end PLTS`, focused
diffs, non-fatal linting) are described in `CLAUDE.md`.
