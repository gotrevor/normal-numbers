# Found: Boris Alexeev's `plby/lean-proofs` covers our analytic floors (2026-09-24)

Trigger: erdosproblems.com shows #239 as "PROVED (LEAN)" (set 2026-08-23 by Boris Alexeev,
teorth/erdosproblems commit dfbf467).  The proof is `plby/lean-proofs`
`src/latest/ErdosProblems/Erdos239.lean` (1642 lines, Codex / GPT-5.6, Lean/Mathlib v4.33.0, comparator
challenge JSON with the standard three axioms).  Our `~/src/fc-erdos-239` run is therefore an
independent second proof by a different route (Elliott's dilation-Lipschitz estimate, elementary),
not a first.

Relevant to C1 / the two-point bet (grep tier only, not built here):
- `ErdosProblems/Erdos67/` (437 files, no `sorry` by grep): Tao's Erdős discrepancy proof, including
  `LogElliott.lean` (the finitary log-averaged two-point Elliott statement), `MRT.lean`
  (Matomäki–Radziwiłł–Tao), entropy decrement (`Entropy.lean`), Halász-type pieces.
- `ErdosProblems/Erdos69/HalaszMean.lean`: a finite Halász–Selberg mean bound for prime-avoidance
  functions (Tao–Teräväinen branch).

Consequence: `TwoPointElliott` (log-density form) and the C1-log route may be reachable by
vendoring from Erdos67, the way `src/PNTPort` vendored PNT+.  Next: read which exact Elliott
statement Erdos67 proves (non-pretentious hypothesis form, bounded vs ±1) and whether it covers
`ζ^ω` along `pn+1`, `qn+1`.
