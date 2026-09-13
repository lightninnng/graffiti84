#!/usr/bin/env bash
# Audit: no sorry/admit/axiom in Lean sources (comments stripped first),
# then build the three layers.
set -euo pipefail

PY=python3
command -v python3 >/dev/null 2>&1 || PY=python

"$PY" scripts/audit_scan.py

lake build Graffiti84.RadiusCriticalStructure
lake build Graffiti84.LeafLemma
lake build Graffiti84.GraphConjecture84
echo "All three layers built."
