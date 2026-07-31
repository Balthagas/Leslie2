#!/bin/bash
# Build the concise edition of the blueprint (web + pdf).
#
# The concise edition shares its formal nodes, figures and macros with the full
# edition and has its own roots: src/web-min.tex and src/print-min.tex over
# src/content-min.tex. Outputs land in web-min/ and print-min/.
#
# The min web build writes blueprint/lean_decls, the same path the full
# `leanblueprint web` build writes, and the concise edition harvests a subset of
# the declarations. This script saves that file and puts it back afterwards, so
# `lake exe checkdecls blueprint/lean_decls` keeps checking the full edition's
# declaration set.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
src="$here/src"

decls="$here/lean_decls"
saved=""
if [ -f "$decls" ]; then
  saved="$(mktemp -t lean_decls)"
  cp "$decls" "$saved"
fi
restore() {
  if [ -n "$saved" ]; then
    cp "$saved" "$decls"
    rm -f "$saved"
  fi
}
trap restore EXIT

cd "$src"
rm -rf "$here/web-min" web-min.paux
plastex -c plastex-min.cfg web-min.tex

rm -rf "$here/print-min"
latexmk -output-directory="$here/print-min" print-min.tex

echo
echo "web: $here/web-min/index.html"
echo "pdf: $here/print-min/print-min.pdf"
