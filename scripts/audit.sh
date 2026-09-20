#!/usr/bin/env bash
# Audit: no sorry/admit/axiom in Lean sources (comments stripped first),
# then build all layers and report the implemented results' axiom dependencies.
set -euo pipefail

PY=python3
command -v python3 >/dev/null 2>&1 || PY=python

"$PY" scripts/audit_scan.py

lake build
lake env lean scripts/axioms.lean
echo "All layers, leafLemma and graphConjecture84 built; axiom dependencies printed above."
