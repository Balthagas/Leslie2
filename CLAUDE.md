# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project overview

Lean 4 + Mathlib formalization project. The GitHub repo, the Lake package, and the Lean root module all share the name `Leslie2` (the repo folder is lowercase *leslie2*; the Lean module is capitalized `Leslie2` per Lean's module-naming convention). The project is split into two Lake libraries. The **core** library `Leslie2` (the sole default build target) holds the five essential results — forward-simulation trace-distribution soundness, forward-simulation transitivity, and the three precongruences — and their support, organized into content-themed sub-folders directly under `Leslie2/` — `Systems/` (the PLTS model), `Weak/` (weak transitions), `DistMonad/` (the 𝒟 construction), `WeakClosure/` (the weak closure + its unfolding pipeline), `Simulation/`, `ProcessAlgebra/` (parallel/interleave/abstract), and `Other/` (generic non-PLTS utilities) — with `Leslie2/Results.lean` holding the five theorems alone. The **extras** library `Leslie2Extra` (opt-in: `lake build Leslie2Extra`) holds exploratory work that builds on top of the core — a `Fairness/` line and a measure-theoretic `Measure/` line. Each library has its own re-export root (`Leslie2.lean`, `Leslie2Extra.lean`). See `README.md` for the full layout, the dependency layers, and where each main result lives. The PLTS core model is in `Leslie2/Systems/System.lean`.

Toolchain is pinned in `lean-toolchain` (currently `leanprover/lean4:v4.31.0-rc1`); Mathlib revision is pinned in `lakefile.toml` (currently `v4.31.0-rc1`). The toolchain is updated by editing `lean-toolchain` — do not bump it casually, since the Mathlib rev must match.

## Common commands

```bash
lake build                         # build the core library (default target)
lake build Leslie2Extra   # build the opt-in extras (fairness + measure)
lake exe cache get                 # fetch the Mathlib build cache before first build
lake build Leslie2.Systems.System  # build a single file
lake exe mk_all --check            # check that each library root re-exports all its files
                                   # (CI runs this via `mk_all-check: true`)
```

There is no test suite. CI (`.github/workflows/blueprint.yml`) runs `lake-action` with `build: true, lint: false, mk_all-check: true` (which builds the core and checks both library roots), then builds the extras library (`lake build Leslie2Extra`) to keep it green, then compiles the blueprint and doc-gen output to GitHub Pages on every push to `master`. Linting is intentionally off in CI; the lakefile sets `weak.linter.mathlibStandardSet = true` so warnings show locally but don't fail the build.

## Lakefile conventions

- `relaxedAutoImplicit = false` — implicits must be declared explicitly; bare lowercase identifiers in type signatures will not be auto-bound.
- `maxSynthPendingDepth = 3` — typeclass synthesis depth is capped low; expect to provide instances explicitly for deeper hierarchies (common with PMF / measure-theoretic code).
- `pp.unicode.fun = true` — `fun a ↦ b` is the pretty-printed form.
- Extra deps beyond Mathlib: `checkdecls` (declaration-existence check used by the blueprint) and `doc-gen4` (API docs). Both are pulled by CI but not used by `lake build` directly.

## Blueprint

The math write-up is a Lean blueprint in `blueprint/src/` (`content.tex` is the actual content; `web.tex` / `print.tex` are the web/PDF entry points; `macros/` holds the `\lean{}`/`\leanok` macros used to cross-link to Lean declarations). The Jekyll site under `home_page/` is what gets published to GitHub Pages alongside the blueprint and doc-gen output. The blueprint hyperlinks at `https://Balthagas.github.io/Leslie2`.

When adding a Lean declaration that should appear in the blueprint, mirror it with a `\begin{definition}\label{...}\lean{NamespacedName}\leanok ...\end{definition}` block in `content.tex` — `checkdecls` will fail CI if the `\lean{}` target doesn't resolve.

## Code conventions

- Mathlib license header (`Copyright ... Released under Apache 2.0 ... Authors: ...`) is expected on every `.lean` file; see e.g. `Leslie2/Systems/System.lean` for the form.
- The PLTS definitions namespace everything under `namespace PLTS` / `end PLTS`. New top-level concepts should follow the same pattern (`namespace X ... end X`), not bare definitions.
- Do **not** fix unrelated lint/style warnings unless explicitly asked — warnings are intentionally non-fatal and the user prefers focused diffs.
