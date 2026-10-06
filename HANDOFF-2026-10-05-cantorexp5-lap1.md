# HANDOFF 2026-10-05 — cantorexp5 lap 1

Branch `proof/cantorexp5`.  New file `src/NormalNumbers/CantorExactExponentFive.lean`; base-3
files untouched.

## Done
* Threshold derived: `thresholdFive = 2 + log₄ 5 ≈ 3.161` (`summable_bc_five`, `rho_five_lt_one`).
  Kernel controls on the real schedule: `bcTerm_red_five` (μ₀ = 31/10, block cost 5^116·4^-127 > 1),
  `bcTerm_green_five` (μ₀ = 7/2).
* Headlines frozen and wired: `exists_computable_mem_cantorFive_irrExponent_normal`,
  `exists_mem_cantorFive_irrExponent_normal` (the latter from the former).
* `not_isNormal_five_cantorFiveExpReal` proved (digit 2 never occurs).
* Open node `StretchFive` (2 < μ₀ ≤ T₅).

## Design decision: copy, not generalize
The base-3 stack (`CantorLiouville` 2382 l., `CantorLiouvilleAll` 954 l., `CantorExpGeneric`
711 l., `CantorExactExponent` 1805 l.) hard-codes base 3 and digits {0,2}: `tdig`, `changes`,
the cos bounds, the `3 ∣ b²−1` orbit count.  Generalizing is well over two laps before payoff.
Instead: **keep the Boolean coin space**, one base-5 digit = `3·ω(2i) + ω(2i+1)` ∈ {0,1,3,4}
(`ptDigitF`).  Then `coins`, `pre`, and the derandomizer
`CantorLiouvilleAll.exists_computable_normal_sched_family` (generic in `G`) and the schedule
`expRunStart/expRunEnd/expFree` are reused verbatim.

## Open leaves (sorry)
1. `exists_exponent_tests_five` — port of base-3 §§ Trunc/window/BC/primrec with 3→5, 2→4.
2. `exists_computable_normal_avoid_five` — needs a base-5 second moment for `5 ∤ b`.  Per digit
   φ(t) = ((1+e(3t))/2)((1+e(t))/2); crux is the analogue of `secondMoment_le_b`.
