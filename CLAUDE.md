# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project overview

Lean 4 + Mathlib formalization project. The GitHub repo, the Lake package, and the Lean root module all share the name `Leslie2` (the repo folder is lowercase *leslie2*; the Lean module is capitalized `Leslie2` per Lean's module-naming convention). The project is split into three Lake libraries. The **core** library `Leslie2` holds the five essential results — forward-simulation trace-distribution soundness, forward-simulation transitivity, and the three precongruences — and their support, organized into content-themed sub-folders directly under `Leslie2/` — `Systems/` (the PLTS model), `Weak/` (weak transitions), `DistMonad/` (the 𝒟 construction), `WeakClosure/` (the weak closure + its unfolding pipeline), `Simulation/`, `ProcessAlgebra/` (parallel/interleave/abstract), and `Other/` (generic non-PLTS utilities) — with `Leslie2/Results.lean` holding the five theorems alone. The **protocols** library `Leslie2Protocols` holds the ABA case study; its `Framework/` folder holds the protocol-independent combinators the case study composes with, including a fourth precongruence — for restriction along the left summand of an extended alphabet — in `Leslie2Protocols/Framework/Relabel.lean`. Both are default targets, so `lake build` covers them and the docs build documents them: the API documentation is generated one `:docs` facet per default target, and the blueprint links into those pages. The **extras** library `Leslie2Extra` (opt-in: `lake build Leslie2Extra`) holds exploratory work that builds on top of the core — a `Fairness/` line and a measure-theoretic `Measure/` line. Each library has its own re-export root (`Leslie2.lean`, `Leslie2Extra.lean`, `Leslie2Protocols.lean`). See `README.md` for the full layout, the dependency layers, and where each main result lives. The PLTS core model is in `Leslie2/Systems/System.lean`.

Toolchain is pinned in `lean-toolchain` (currently `leanprover/lean4:v4.31.0-rc1`); Mathlib revision is pinned in `lakefile.toml` (currently `v4.31.0-rc1`). The toolchain is updated by editing `lean-toolchain` — do not bump it casually, since the Mathlib rev must match.

## Common commands

```bash
lake build                         # build the default targets (core + protocols)
lake build Leslie2Extra   # build the opt-in extras (fairness + measure)
lake exe cache get                 # fetch the Mathlib build cache before first build
lake build Leslie2.Systems.System  # build a single file
lake exe mk_all --check            # check that each library root re-exports all its files
                                   # (CI runs this via `mk_all-check: true`)
```

There is no test suite. CI (`.github/workflows/blueprint.yml`) runs `lake-action` with `build: true, lint: false, mk_all-check: true` (which builds the default targets and checks the library roots), then builds the extras library (`lake build Leslie2Extra`) to keep it green, then compiles the blueprint and doc-gen output to GitHub Pages on every push to `main` or `master`. A manual run verifies everything but publishes nothing: the docs build, the Jekyll build, the Pages upload and the deployment are all gated on push events. Linting is intentionally off in CI; the lakefile sets `weak.linter.mathlibStandardSet = true` so warnings show locally but don't fail the build.

## Lakefile conventions

- `relaxedAutoImplicit = false` — implicits must be declared explicitly; bare lowercase identifiers in type signatures will not be auto-bound.
- `maxSynthPendingDepth = 3` — typeclass synthesis depth is capped low; expect to provide instances explicitly for deeper hierarchies (common with PMF / measure-theoretic code).
- `pp.unicode.fun = true` — `fun a ↦ b` is the pretty-printed form.
- Extra deps beyond Mathlib: `checkdecls` (declaration-existence check used by the blueprint) and `doc-gen4` (API docs). Both are pulled by CI but not used by `lake build` directly.

## Blueprint

The math write-up is a Lean blueprint in `blueprint/src/` (`content.tex` is the actual content, connective prose around the statement nodes it inputs from `nodes-min/`; `web.tex` / `print.tex` are the web/PDF entry points; `macros/` holds the `\lean{}`/`\leanok` macros used to cross-link to Lean declarations). The Jekyll site under `home_page/` is what gets published to GitHub Pages alongside the blueprint and doc-gen output. The blueprint hyperlinks at `https://sathiyavrs.github.io/Leslie2`.

When adding a Lean declaration that should appear in the blueprint, mirror it with a `\begin{definition}\label{...}\lean{NamespacedName}\leanok ...\end{definition}` block in a node file — `checkdecls` will fail CI if the `\lean{}` target doesn't resolve. A node added to `nodes-min/` needs its counterpart in `nodes/` and vice versa; see the full edition below.

### Blueprint commands (local loop)

The blueprint is a genuine [leanblueprint](https://github.com/PatrickMassot/leanblueprint) project; the CLI is installed via pipx. These commands build the default edition — the reference-style one, whose nodes state each object and result and point at the Lean. Run from the repo root:

```bash
leanblueprint pdf        # print edition → blueprint/print/print.pdf (latexmk/xelatex)
leanblueprint web        # web edition → blueprint/web/ (plasTeX; also writes
                         #   blueprint/web/dep_graph_document.html and blueprint/lean_decls)
leanblueprint checkdecls # verify every \lean{} target exists (needs a completed lake build)
leanblueprint serve      # serve blueprint/web/ at http://0.0.0.0:8000/
```

#### Full edition

`blueprint/src/content-full.tex` is a second, much longer edition of the same blueprint: it carries the rule inventories, the pseudocode floats and the full proof bodies (`src/nodes/`), where the default edition gives one-sentence statements pointing at the Lean (`src/nodes-min/`). The two editions share the figures (`src/figures/`) and the macros. The full edition has its own roots, `src/web-full.tex` and `src/print-full.tex`, with its own plasTeX config `src/plastex-full.cfg`. Build it with

```bash
bash blueprint/build-full.sh   # both versions of the full blueprint
                               #   → blueprint/web-full/ and blueprint/print-full/print-full.pdf
```

or by hand, from `blueprint/src`:

```bash
plastex -c plastex-full.cfg web-full.tex               # → ../web-full/
latexmk -output-directory=../print-full print-full.tex  # → ../print-full/print-full.pdf
```

Caveat: the full web build writes `blueprint/lean_decls`, the same path `leanblueprint web` writes, and the two editions harvest different declaration sets. `build-full.sh` saves and restores that file; if you run `plastex -c plastex-full.cfg` by hand, re-run `leanblueprint web` before `lake exe checkdecls blueprint/lean_decls`.

The dependency graph is drawn from a vendored copy of the plugin's page template,
`blueprint/src/dep_graph.html`, selected by `tpl=` in the `\usepackage[...]{blueprint}`
line of `web.tex` and `web-full.tex` (the blueprint package passes its options through to
the dependency-graph package). It differs from the upstream template in one block, which
substitutes each statement's title for the `\label` key the plugin would otherwise show.
A bad `tpl=` path makes the plugin fall back to its own template with only a log warning,
so `python3 scripts/check-web-build.py <build-dir>` asserts the substitution is present
and still fits the graph source; run it against both `blueprint/web` and
`blueprint/web-full`. When updating leanblueprint, re-diff the template against the
plugin's own.

The two node directories must agree on their formal frontmatter (`\label`, `\lean`, `\leanok`, `\uses`) — that is what the dependency graph and the declaration harvest are built from. `python3 scripts/check-node-sync.py` checks every pair and prints `N/N in sync`; only the bodies are allowed to differ.

Caveats: plasTeX 3.1 silently breaks on **Python 3.14** (packages fail to load, `\lean`/`\uses` fall back to default renderers, no dep graph, no `lean_decls`, no theorem badges), and `leanblueprint web` resolves `plastex` from PATH — so there must be exactly ONE pipx installation, on Python ≤ 3.13, exposing both apps: `pipx install leanblueprint --python /opt/homebrew/bin/python3.13 --include-deps` (uninstall any standalone `plastex` pipx venv first). The dependency graph needs no external `dot` binary (`pygraphviz` ships bundled Graphviz libraries). plasTeX caches the parse in `blueprint/src/web.paux` — after preamble/URL changes, `rm -rf blueprint/web blueprint/src/web.paux` before rebuilding.

## Code conventions

- Mathlib license header (`Copyright ... Released under Apache 2.0 ... Authors: ...`) is expected on every `.lean` file; see e.g. `Leslie2/Systems/System.lean` for the form.
- The PLTS definitions namespace everything under `namespace PLTS` / `end PLTS`. New top-level concepts should follow the same pattern (`namespace X ... end X`), not bare definitions.
- Do **not** fix unrelated lint/style warnings unless explicitly asked — warnings are intentionally non-fatal and the user prefers focused diffs.
