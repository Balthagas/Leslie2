#!/bin/bash
# Build the full edition of the blueprint (web + pdf).
#
# The full edition shares its formal nodes, figures and macros with the default
# edition and has its own roots: src/web-full.tex and src/print-full.tex over
# src/content-full.tex. Outputs land in web-full/ and print-full/.
#
# The full web build writes blueprint/lean_decls, the same path the default
# `leanblueprint web` build writes, and the two editions harvest different
# declaration sets. This script saves that file and puts it back afterwards, so
# `lake exe checkdecls blueprint/lean_decls` keeps checking the default
# edition's declaration set.
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
rm -rf "$here/web-full" web-full.paux
plastex -c plastex-full.cfg web-full.tex

rm -rf "$here/print-full"
latexmk -output-directory="$here/print-full" print-full.tex

echo
echo "web: $here/web-full/index.html"
echo "pdf: $here/print-full/print-full.pdf"
