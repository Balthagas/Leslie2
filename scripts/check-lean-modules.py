#!/usr/bin/env python3
"""Check that the module paths the blueprint links to still exist.

The blueprint links into the generated API documentation with
``\\leanmodule{Path/To/Module}``, which the web macros turn into a doc-gen URL.
Nothing else verifies those paths: ``checkdecls`` reads only the harvested
``\\lean``/``\\leandecl`` declarations, and ``check-lean-prose.py`` only the
``\\mathrm{...}`` tokens, so a renamed or moved file leaves a dead link on the
published site with no build failure. This check resolves every path against the
Lean tree and fails on any that names no file.

A path may name a module file (``Leslie2/Results`` for ``Leslie2/Results.lean``)
or a library root (``Leslie2Protocols`` for ``Leslie2Protocols.lean``).

Run from the repository root::

    python3 scripts/check-lean-modules.py
"""

import re
import sys
from pathlib import Path

MODULE = re.compile(r"\\leanmodule\{([^}]*)\}")


def module_paths(src: Path) -> dict[str, list[str]]:
    """Every ``\\leanmodule{...}`` path, mapped to the files it appears in."""
    paths: dict[str, list[str]] = {}
    for path in sorted(src.rglob("*.tex")):
        for target in MODULE.findall(path.read_text(encoding="utf-8", errors="replace")):
            paths.setdefault(target.strip(), []).append(str(path))
    return paths


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    targets = module_paths(repo / "blueprint" / "src")

    missing = {t: v for t, v in targets.items() if not (repo / f"{t}.lean").is_file()}
    print(f"blueprint module links: {len(targets)}, resolved: {len(targets) - len(missing)}")

    for target, files in sorted(missing.items()):
        where = ", ".join(sorted({Path(f).name for f in files}))
        print(
            f"error: \\leanmodule{{{target}}} names no Lean file ({where}); "
            "the module was renamed, moved, or misspelled",
            file=sys.stderr,
        )
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
