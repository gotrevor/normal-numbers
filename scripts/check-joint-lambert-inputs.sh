#!/usr/bin/env bash
# Axiom audit for the joint-Lambert prime-input deliverables (lap 7, 2026-09-28).
# Expected: every line lists exactly [propext, Classical.choice, Quot.sound].
set -euo pipefail
cd "$(dirname "$0")/.."
lake build NormalNumbers.JointLambertPrimeInputs
tmp=$(mktemp /tmp/jlpi-XXXX.lean)
cat > "$tmp" <<'LEAN'
import NormalNumbers.JointLambertPrimeInputs
#print axioms NormalNumbers.JointLambert.primeIntervalSupply_holds
#print axioms NormalNumbers.JointLambert.jointLambertDisjunctivity_of_agp
#print axioms NormalNumbers.JointLambert.jointWords_two_four_of_agp
LEAN
lake env lean "$tmp"
rm -f "$tmp"
