#!/usr/bin/env bash
# Build and check the Lean formalisation of "Graph Similarity Meets Optimal Transport".
#
# Usage: ./build.sh [--install-elan] [--no-cache] [--docs] [--help]
#
#   --install-elan  install the Lean toolchain manager `elan` if it is not found
#   --no-cache      do not download the prebuilt Mathlib cache (Mathlib is then compiled
#                   from source, which takes a long time)
#   --docs          regenerate the paper <-> Lean correspondence PDFs (needs python3, pdflatex)
#
# Steps:
#   1. locate (or install) elan / lake
#   2. download the prebuilt Mathlib cache (`lake exe cache get`)
#   3. build the library (`lake build`), i.e. check every proof
#   4. make sure no `sorry` or `axiom` occurs in the sources
#   5. print the axioms of the main results and check that only the standard axioms
#      propext, Classical.choice, Quot.sound are used
#   6. optionally regenerate the correspondence PDFs
set -euo pipefail

cd "$(dirname "$0")"

INSTALL_ELAN=0
USE_CACHE=1
DOCS=0
for arg in "$@"; do
  case "$arg" in
    --install-elan) INSTALL_ELAN=1 ;;
    --no-cache) USE_CACHE=0 ;;
    --docs) DOCS=1 ;;
    -h|--help) sed -n '2,20p' "$0"; exit 0 ;;
    *) echo "unknown option: $arg" >&2; exit 2 ;;
  esac
done

step() { printf '\n\033[1m==> %s\033[0m\n' "$*"; }

# 1. Lean toolchain ------------------------------------------------------------------------------
step "Locating the Lean toolchain"
if ! command -v lake >/dev/null 2>&1; then
  if [ -x "$HOME/.elan/bin/lake" ]; then
    export PATH="$HOME/.elan/bin:$PATH"
  elif [ "$INSTALL_ELAN" = 1 ]; then
    echo "Installing elan (https://github.com/leanprover/elan) ..."
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
    bash /tmp/elan-init.sh -y --default-toolchain none
    export PATH="$HOME/.elan/bin:$PATH"
  else
    cat >&2 <<'EOF'
error: `lake` (the Lean build tool) was not found.
Install the Lean toolchain manager elan, e.g.
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
or rerun this script with --install-elan.
EOF
    exit 1
  fi
fi
echo "toolchain: $(cat lean-toolchain)"
lake --version

# 2. Mathlib cache -------------------------------------------------------------------------------
if [ "$USE_CACHE" = 1 ]; then
  step "Downloading the prebuilt Mathlib cache"
  lake exe cache get
fi

# 3. Build ---------------------------------------------------------------------------------------
step "Building and checking all proofs (lake build)"
lake build

# 4. No sorry / axiom ----------------------------------------------------------------------------
step "Checking that the sources contain no sorry / admit / axiom"
if grep -rnE '\bsorry\b|\badmit\b|^[[:space:]]*(private[[:space:]]+)?axiom[[:space:]]' --include='*.lean' GsimOT GsimOT.lean ThinMatching ThinMatching.lean; then
  echo "error: found sorry/admit/axiom in the sources" >&2
  exit 1
fi
echo "ok"

# 5. Axioms --------------------------------------------------------------------------------------
step "Axioms used by the main results"
AXIOM_OUT=$(lake env lean scripts/CheckAxioms.lean)
echo "$AXIOM_OUT"
if echo "$AXIOM_OUT" | grep -v 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' | grep -q .; then
  echo "error: unexpected axioms (see above)" >&2
  exit 1
fi
echo "ok: only the standard axioms propext, Classical.choice, Quot.sound are used"

# 6. Documents -----------------------------------------------------------------------------------
if [ "$DOCS" = 1 ]; then
  step "Regenerating the correspondence and proof overview PDFs"
  python3 scripts/gen_correspondence.py
  python3 scripts/build_overviews.py
fi

step "All proofs checked successfully."
