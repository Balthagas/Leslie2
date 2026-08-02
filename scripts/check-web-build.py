#!/usr/bin/env python3
"""Check that a plasTeX blueprint build kept its plugin output.

When a plasTeX plugin fails to load, the build still exits zero: the pages
render, but the Lean cross-links are gone and the dependency graph is empty.
This check turns that silent degradation into a failure. It takes the build
directory (for instance ``blueprint/web``) and asserts that the dependency
graph carries nodes and edges and that the section pages carry Lean links.
"""

import html
import re
import sys
from pathlib import Path


def graph_counts(path: Path) -> tuple[int, int]:
    """Count the nodes and edges of the dependency graph's DOT source."""
    text = html.unescape(path.read_text(encoding="utf-8", errors="replace"))
    start = text.find("digraph")
    if start == -1:
        return 0, 0
    body = text[start : text.find("</", start)]
    nodes = set(re.findall(r'"((?:def|thm|lem):[^"]+)"\s*\[', body))
    edges = set(re.findall(r'"([^"]+)"\s*->\s*"([^"]+)"', body))
    return len(nodes), len(edges)


def title_labels(path: Path) -> tuple[int, int]:
    """Count the graph's title substitutions, and how many would take effect.

    The dependency-graph plugin labels each node with its ``\\label`` key; the
    vendored template ``blueprint/src/dep_graph.html`` substitutes the statement
    titles into the graph source instead. A bad ``tpl=`` path makes the plugin
    fall back to its own template with only a log warning, and a change to the
    graph source's shape would leave the substitution matching nothing. Either
    way the build stays green and the graph silently reverts to label keys, so
    both are checked here: the titles the template emitted, and the ones whose
    node the substitution can actually find.
    """
    text = html.unescape(path.read_text(encoding="utf-8", errors="replace"))
    block = re.search(r"const nodeTitles = \{(.*?)\n\};", text, re.S)
    if not block:
        return 0, 0
    ids = re.findall(r'^\s*"([^"]+)":', block.group(1), re.M)
    matchable = sum(
        1
        for node in ids
        if re.search(rf'"{re.escape(node)}"\s*\[[^\]]*?label=', text)
    )
    return len(ids), matchable


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(f"usage: {argv[0]} <build-directory>", file=sys.stderr)
        return 2

    build = Path(argv[1])
    failures = []

    graph = build / "dep_graph_document.html"
    if not graph.is_file():
        failures.append(f"{graph} is missing")
    else:
        nodes, edges = graph_counts(graph)
        print(f"dependency graph: {nodes} nodes, {edges} edges")
        if nodes == 0 or edges == 0:
            failures.append(
                f"{graph} carries {nodes} nodes and {edges} edges; "
                "the dependency-graph or blueprint plugin did not load"
            )

        titles, matchable = title_labels(graph)
        print(f"graph node titles: {titles} emitted, {matchable} substitutable")
        if titles == 0:
            failures.append(
                f"{graph} carries no node titles; the graph template "
                "blueprint/src/dep_graph.html was not used (check tpl= in "
                "web.tex and web-full.tex)"
            )
        elif matchable != titles:
            failures.append(
                f"{graph} names {titles} node titles but only {matchable} "
                "match a node of the graph source; the substitution in "
                "blueprint/src/dep_graph.html no longer fits that source"
            )

    sections = sorted(build.glob("sect*.html"))
    if not sections:
        failures.append(f"{build} holds no section pages")
    else:
        links = sum(
            page.read_text(encoding="utf-8", errors="replace").count("lean_decl")
            for page in sections
        )
        print(f"section pages: {len(sections)}, Lean declaration links: {links}")
        if links == 0:
            failures.append(
                f"{build} holds no Lean declaration links; "
                "the blueprint plugin did not process \\lean"
            )

    for failure in failures:
        print(f"error: {failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
