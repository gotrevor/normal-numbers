# HANDOFF 2026-09-21-0330 — arithmetic moment budget + joint transfer COMPLETE

Timestamped checkpoint (treadmill STOP requested; session ends after this).
Branch `proof/prime-model-complement`, HEAD `afdd39e` (proof commits `f4d6af0`,
`afdd39e`).  Same content as `HANDOFF-radical-moment.md`.

## Exact next steps for a fresh session

1. Optional leftover from this kickoff: specialize `radical_box_tail_exp20` at
   `T = x^(1/(4k))`, `y = x^ε` to `k·exp 20·exp(−1/(8kε))` (k ≥ 1, x > 1,
   ε > 0, log(x^ε) ≥ 2).  Pure `rpow` bookkeeping: `T^α = exp(1/(8kε))`.
2. Sharper budget if ever wanted: `mertens_crude`'s constant 4 can drop to
   ~1 by using `log y + log 4 + 4` — needs `PrimeNumberTheoremAnd` actually
   wired into `lakefile.toml` + `lake-manifest.json` (it is NOT today).
3. The real downstream blockers are unchanged and live on other branches:
   two-sided sieve discrepancy δ (fundamental lemma), general CRT counting,
   phase decay, final constants.  Repo crux remains `RoughIndependenceAt h 2`.


Branch `proof/prime-model-complement`.  Full `lake build` GREEN (9107 jobs,
pre-commit hook).  `KICKOFF-radical-moment.md` PRIMARY and SECONDARY both done.

## Delivered

`src/NormalNumbers/PrimeModelRadicalMoment.lean` (new, imported from
`src/NormalNumbers.lean`), namespace `NormalNumbers.PrimeModel.Radical`.
No `sorry`, no `axiom`; `radical_moment_budget`, `radical_box_tail_exp20`,
`mertens_crude`, `radical_joint_phase_transfer` all `#print axioms` =
`[propext, Classical.choice, Quot.sound]`.  Pure addition; no frozen statement
touched.

PRIMARY: `theta_le` (θ(N) ≤ N log 4 from `primorial_le_four_pow`),
`mertens_crude` (∑_{p≤N} log p/p ≤ 4 log N, dyadic strong induction),
`exp_sub_one_le_two_mul`, `radical_moment_budget` (≤ 20; proof gives 4),
`radical_box_tail_exp20` (tail ≤ k·exp 20 / T^(1/(2 log y)), no moment hyp).

SECONDARY: `jointModel`, `jointModel_mass_one`, `jointModel_tail`,
`radical_joint_phase_transfer` (≤ 2 k exp 20 / T^α + 2δ; ν's residue marginal
NOT assumed uniform).

## Key finding

`PrimeNumberTheoremAnd` is **not** a dependency of this project (absent from
`lake-manifest.json`; its `Mertens.olean` is unbuilt), so the kickoff's
`Mertens.sum_log_prime_div_eq_log` was unavailable.  The needed prime sum is
proved here from mathlib alone via the primorial bound — looser
(4 log y vs log y + log 4 + 4) but far inside the budget.

## Not done (deliberately, out of scope)

The optional specialization `T = x^(1/(4k))`, `y = x^ε` to
`k exp 20 exp(−1/(8kε))`.  Remaining obligations elsewhere: general CRT
counting, two-sided sieve discrepancy δ, phase decay, final constants.  This is
a selected-prime shortcut layer, NOT G4 normality.
