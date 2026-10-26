# Testing the genuine BBP residual denominator budget

Let r_n be the actual rational residual at cutoff s, and let D_n be its reduced denominator.  The test requires a candidate residual S_n to satisfy `S_n.den ∣ D_n`.  This uses the exact reduced denominator, not a generic height estimate.  It allows proper divisors; it does not demand that every candidate's reduced denominator equal D_n.

All results below are proved in [ReservoirDenominator.lean](../../src/NormalNumbers/PiDisjunctiveRoutes/ReservoirDenominator.lean).

## Rational targets survive at the grid scale

`rational_comparison_actual_denominators` proves that for every cutoff s and every finite prefix length N, there are a rational target q and a rational residual S such that:

- S_n = r_n through index N, including the zero initial value.
- The reservoir is unchanged, and `S_n.den ∣ D_n` for every n.
- The head differs from `16^n q − 16^n piTail(n)` by less than 1/D_n.
- Its BBP forcing defect is less than `1/D_(n+1) + 16/D_n`.
- q is not disjunctive in base 16.

The construction rounds the desired residual to the grid D_n^(-1) Z.  It first chooses q sufficiently close to pi to retain the prescribed exact prefix.  `denominator_preserving_pole` separately proves that this denominator constraint preserves a reservoir pole at every prime absent from D_n.  The denominators D_n are defined directly from the actual residual (`rationalResidual`, `residualDenominator`); `rationalResidual_cast` connects it to the original real-valued definition.

This statement makes no asymptotic claim about the growth of D_n.  Its error bounds are explicit in the actual denominators.  It does not reproduce the preceding arbitrary-error-schedule construction: fixed denominator grids cannot support arbitrary precision.

## Finer precision forces exact equality

Put d_n = S_n − r_n.  If both denominators divide D_n, then

```
den(d_(n+1) − 16 d_n) divides lcm(D_(n+1), D_n).
```

A nonzero rational with denominator dividing L has absolute value at least 1/L.  Consequently, if the forcing defect at every index is strictly below

```
1 / lcm(D_(n+1), D_n),
```

every defect is zero.  With S_0 = r_0 = 0, induction gives S_n = r_n for all n.  This is `actual_denominator_rigidity`; `recurrence_defect_den_dvd` and `rat_eq_zero_of_denominator_small` supply the arithmetic.  The theorem uses the head forcing defect directly, through `headForcingDefect_eq`.

The comparison and rigidity thresholds differ.  No sharp classification of all intermediate tolerances is claimed.

## The resulting sufficient criterion is exactly the original problem

`DenominatorCouplingCriterion s` says that there exists a positive pointwise tolerance schedule such that every denominator-controlled model, with zero initial value, approximate BBP forcing, and the prescribed head shadow, has a disjunctive target.

`denominatorCouplingCriterion_iff` proves

```
DenominatorCouplingCriterion s ↔ IsDisjunctive 16 pi.
```

In one direction, the genuine BBP residual is a model for every positive tolerance, with target pi and zero error.  In the other, choose the tolerance below the reciprocal-lcm threshold and at most 1.  Rigidity recovers the genuine residual; bounded head error then identifies the target as pi (`bounded_head_error_identifies_target`).  An assumed proof of pi disjunctivity supplies the final conclusion.

Thus the denominator budget does add exact rigidity at a specified scale.  This sufficient criterion provides no additional digit-distribution step.  A further argument would need to extract a visitation estimate from the arithmetic, beyond recovering the BBP sequence.  Neither pi disjunctivity nor impossibility of the overall prime-reservoir route has been established.
