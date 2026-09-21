# HANDOFF — arithmetic moment budget + joint transfer COMPLETE

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
