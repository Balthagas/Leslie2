# leslie2 — Probabilistic Labelled Transition Systems in Lean 4

A Lean 4 + Mathlib formalization of **probabilistic labelled transition systems
(PLTS)** and the **trace-distribution soundness of probabilistic simulations**.
PLTS are the foundational model for reasoning about randomized programs and
protocols; the headline results say that if one system *simulates* another, then
every observable-trace distribution of the concrete system is reproducible by the
abstract one — and that this simulation relation is a well-behaved (transitive,
precongruent) refinement.

> **Naming.** The GitHub repository, the Lake package, and the Lean root module all
> share the name `Leslie2` (the repo folder is lowercase *leslie2*; the Lean module
> is capitalized `Leslie2`, per Lean's module-naming convention). Every core module
> path below is `Leslie2.…`; the opt-in extras live under `Leslie2Extra.…`.

## The five essential results

The project is organized around five theorems about **probabilistic forward
simulation** (everything is `namespace PLTS`, and stated for a canonical silent
label `τ` via `class Silent`, so the internal/external partition is a property of
the *label type*, not of an individual system):

All five live together in **`Leslie2/Results.lean`**; their supporting
machinery lives in the seven themed sub-folders described below.

| # | Result | Statement |
| --- | --- | --- |
| 1 | `ProbabilisticForwardSimulation.achievableTraceDists_subset` | forward simulation ⇒ trace-distribution inclusion |
| 2 | `ProbabilisticForwardSimulation.trans` | forward simulation is transitive |
| 3 | `ProbabilisticForwardSimulation.parallel_right` | precongruence for `System.parallel` |
| 4 | `ProbabilisticForwardSimulation.interleave` | precongruence for `System.interleave` |
| 5 | `ProbabilisticForwardSimulation.abstract` | precongruence for `System.abstract` |

**How they fit together.** Strong-simulation soundness is proved directly
(`StrongProbabilisticSimulation.achievableTraceDists_subset`,
`Simulation/Soundness.lean`). Weak and forward simulation each turn out to
be *the same data* as a strong simulation into a transformed abstract system —
`sys^w` (weak closure) and `𝒟(sys^w)` (distribution-monad lift of the weak
closure) respectively — via the two equivalences in
`Simulation/Equivalences.lean`. Those reductions are sound because
both transformations preserve achievable trace distributions
(`weakClosure_traceProb_eq` in `WeakClosure/TraceProb.lean`,
`dist_traceProb_eq` in `DistMonad/DistTrace.lean`; both driven by
the reusable functional-simulation engine `achievableTraceDists_map` in
`Simulation/TraceMap.lean`). The hardest part of the whole
development is the `WeakClosure/` unfolding pipeline, which proves the non-trivial
`sys^w ⊆ sys` trace inclusion by unfolding each abstract weak step `τ*·l·τ*` into a
concrete `sys`-path. Transitivity and the three precongruences (results 2–5) then
build on the simulation framework directly.

## Project layout

The project is split into **two Lake libraries**:

- **`Leslie2`** — the **core** (default `lake build` target): the five
  essential results and everything they depend on. Self-contained.
- **`Leslie2Extra`** — **opt-in exploratory work** built *on top of* the
  core (it imports the core; nothing in the core imports it). Built with
  `lake build Leslie2Extra`.

### Core — `Leslie2/`

`Results.lean` holds the five theorems alone; every other file is filed into one
of seven content-themed sub-folders (folders are purely organizational — the
import graph, not the folder, defines the dependency order).

```
Leslie2/
├── Results.lean       — the five essential theorems, alone
├── Systems/           — the PLTS model: System (executions, schedulers, probOf),
│                        Trace (Silent τ, traceProb, achievableTraceDists), EndState
├── Weak/              — weak transitions: Scheduler (bind-calculus), Step (weakTau/weakStep),
│                        WeakChar (weak-transition characterizations), Bounds + BoundsHalt (halt mass)
├── DistMonad/         — the 𝒟(sys) construction: DistMonad, and its trace-preservation proof
│                        DistTraceKernel + DistTraceBelief + DistTrace (𝒟 preserves traces ★)
├── WeakClosure/       — the weak closure sys^w: WeakClosure, and the unfolding pipeline proving
│                        sys^w ⊆ sys — Algorithm, ProbOf, Scheduler, Trace, TraceProb ★
├── Simulation/        — Defs (Strong/Weak/Forward sim + compRel), Equivalences, TraceMap (functional-
│                        sim engine ★), Trace (coupling), Transitivity (lift), Soundness (strong+weak ★)
├── ProcessAlgebra/    — Composition (parallel/interleave/abstract operators + prodPMF/piPMF algebra),
│                        Parallel / Interleave / Abstract (per-operator simulation-congruence support)
└── Other/             — generic utilities, not PLTS-specific: Seq (Stream'.Seq), Pmf (PMF helpers)
```

### Extras — `Leslie2Extra/`

```
Leslie2Extra/
├── Fairness/           — fair simulation and resolved-scheduler fairness model
│   ├── Model/           Fairness, ResolvedScheduler, ResolvedGap
│   ├── Construction/    DistFair, DistFairTrace, DistFairHalt, DistFairBarycenter, DistFairClosure
│   └── Simulation/      Defs, Descent, AbstractMarginal, ConcreteMarginal, Trace, Soundness
└── Measure/            — measure-theoretic trace semantics
    ├── Coordinates, Trajectory, Trace
    └── Examples/        Infinite / HalfInfinite / ConvergingInfinite trace examples
```

`Leslie2.lean` and `Leslie2Extra.lean` are the two root modules;
each re-exports every file in its library (kept in sync by `lake exe mk_all`).

### Dependency flow (core)

```
Other ─┐
Systems ─┼─▶ Weak ─▶ WeakClosure ─┐
         │     │                  ├─▶ Simulation ─▶ Results.lean
         │     └─▶ DistMonad ─────┤     (Defs/…/Soundness)   (the five)
         └─▶ ProcessAlgebra ──────┘
```
(Folders group by theme, not strictly by layer — e.g. `Weak/WeakChar` imports
`WeakClosure/WeakClosure`, and `Simulation/TraceMap` is used by `DistMonad/`.)

### Helper vs. result files

- **Helper files** collect lemmas around one theme: `Other/*`, `Systems/EndState`,
  `Weak/{WeakChar,BoundsHalt}`, the per-operator simulation-congruence support
  `ProcessAlgebra/{Parallel,Interleave,Abstract}`, the transitivity lift
  `Simulation/Transitivity`, and the intermediate stages of the `WeakClosure/`
  unfolding pipeline (`Algorithm`, `Trace`, `ProbOf`, `Scheduler`).
- **Definition files** introduce the objects: `Systems/{System,Trace}`,
  `Weak/{Scheduler,Step}`, `DistMonad/DistMonad`, `WeakClosure/WeakClosure`,
  `Simulation/Defs`, `ProcessAlgebra/Composition`.
- **Result files (★)** state the theorems: the five in `Results.lean`, plus the
  strong/weak soundness stepping stones (`Simulation/Soundness`) and the
  trace-preservation engines they rely on (`Simulation/TraceMap`,
  `DistMonad/DistTrace`, `WeakClosure/TraceProb`, `Simulation/Trace`).

## Building

The toolchain is pinned in `lean-toolchain` and the Mathlib revision in
`lakefile.toml`; the two must stay in lockstep.

```bash
lake exe cache get                    # fetch the Mathlib build cache (first time)
lake build                            # build the core library (default target)
lake build Leslie2Extra               # build the opt-in extras (fairness + measure)
lake build Leslie2.Systems.System     # build a single module
lake exe mk_all --check               # check each library root re-exports its files (CI)
```

There is no test suite. CI (`.github/workflows/blueprint.yml`) builds the core
plus `mk_all --check`, then builds the extras library, then compiles the blueprint
and API docs to GitHub Pages on every push to `master`. Linting is intentionally
off in CI (warnings show locally but do not fail the build).

## Blueprint & conventions

The mathematical write-up is a Lean blueprint under `blueprint/src/`, in two
editions over the same formal nodes (`nodes/`): the full one (`content.tex`,
entry points `web.tex` / `print.tex`), built by `leanblueprint pdf` /
`leanblueprint web`, and a concise one (`content-min.tex`, entry points
`web-min.tex` / `print-min.tex`), built by `bash blueprint/build-min.sh`. It
cross-links to Lean declarations by their **fully-qualified name** (e.g.
`PLTS.dist_traceProb_eq`), which this reorganization leaves unchanged — every
declaration still lives in `namespace PLTS`, so only file locations moved. The
published site is at <https://Balthagas.github.io/Leslie2>.

Coding conventions (Mathlib license header, `namespace PLTS … end PLTS`, focused
diffs, non-fatal linting) are described in `CLAUDE.md`.
