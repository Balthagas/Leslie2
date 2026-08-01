#!/usr/bin/env python3
"""Check that the object names in the blueprint's prose still exist in Lean.

The blueprint sets Lean objects in prose as ``\\mathrm{name}``. Nothing else
verifies those: ``checkdecls`` reads only the harvested ``\\lean``/``\\leandecl``
declarations, so a renamed object leaves its old name behind in the prose
silently. This check collects every ``\\mathrm{...}`` token in the blueprint
sources and fails on any that is neither a declaration name in the Lean tree nor
listed below as notation.

Run from the repository root::

    python3 scripts/check-lean-prose.py
"""

import re
import sys
from pathlib import Path

# Mathematical and typographic notation: not Lean names, and not expected to be.
NOTATION = {
    # ambient types and generic parameters
    "Prop", "Label", "Extra", "System",
    # abbreviations used in the figures and the invariant tables
    "SL", "BD", "VT", "IN", "EC", "DEC", "Valid",
    # message levels of the graded-agreement ladder, and the source's own names
    "INPUT", "ECHO", "VOTE", "BIND", "SEAL", "DECIDED", "echo4", "echo5",
    # booleans, positions and generic mathematical words
    "true", "false", "id", "inl", "inr", "pre", "post", "idle", "map", "swap",
    # parameters
    "f",
    # the one label the encoding deliberately omits (deviation D4), so it names
    # nothing in Lean by design
    "guess",
}

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:def|abbrev|theorem|lemma|structure|inductive|instance|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?]*)"
)
FIELD = re.compile(r"^\s{2,}([a-z][A-Za-z0-9_']*)\s*:")
CTOR = re.compile(r"^\s*\|\s*([a-zA-Z_][A-Za-z0-9_']*)")
NAMESPACE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.']*)")
TOKEN = re.compile(r"\\mathrm\{([A-Za-z0-9_]+)\}")


def lean_names(roots: list[Path]) -> set[str]:
    """Every declaration, field, constructor and namespace basename in the tree."""
    names: set[str] = set()
    for root in roots:
        for path in root.rglob("*.lean"):
            for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
                for pattern in (DECL, FIELD, CTOR, NAMESPACE):
                    found = pattern.match(line)
                    if found:
                        names.add(found.group(1).split(".")[-1])
    return names


def prose_tokens(src: Path) -> dict[str, list[str]]:
    """Every ``\\mathrm{...}`` token, mapped to the files it appears in."""
    tokens: dict[str, list[str]] = {}
    for path in sorted(src.rglob("*.tex")):
        for token in TOKEN.findall(path.read_text(encoding="utf-8", errors="replace")):
            tokens.setdefault(token, []).append(str(path))
    return tokens


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    names = lean_names([repo / "Leslie2Protocols", repo / "Leslie2"])
    tokens = prose_tokens(repo / "blueprint" / "src")

    unknown = {t: v for t, v in tokens.items() if t not in names and t not in NOTATION}
    print(f"prose object names: {len(tokens)}, resolved: {len(tokens) - len(unknown)}")

    for token, files in sorted(unknown.items()):
        where = ", ".join(sorted({Path(f).name for f in files}))
        print(
            f"error: \\mathrm{{{token}}} names no Lean declaration ({where}); "
            "it was renamed, misspelled, or belongs in the notation list",
            file=sys.stderr,
        )
    return 1 if unknown else 0


if __name__ == "__main__":
    sys.exit(main())
