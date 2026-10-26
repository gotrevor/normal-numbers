# What a reservoir-to-sum argument must use

The comparison investigation produced a precise obstruction to a class of coupling arguments.  The formal record is [ReservoirComparison.lean](../../src/NormalNumbers/PiDisjunctiveRoutes/ReservoirComparison.lean) and [ReservoirComparisonRobustness.lean](../../src/NormalNumbers/PiDisjunctiveRoutes/ReservoirComparisonRobustness.lean).

## Exact forcing: the missing initial value matters

Keep the actual reservoir R, exit E, entry I, and BBP kick.  Replace its residual by

```
S_x(n) = S_pi(n) + 16^n (x - pi).
```

`shiftedResidual_succ` proves that this satisfies the very same residual recurrence.  `shiftedResidual_shadow` proves

```
R(n) + S_x(n) + 16^n piTail(n) = 16^n x.
```

Every exit fact is unchanged, but the initial residual is now x−pi.  This is not a counterexample with the genuine initial data.  `residual_recurrence_classification` classifies all solutions, and `residual_recurrence_rigid` proves that the exact recurrence together with S(0)=0 uniquely determines the genuine residual.

## Arbitrarily accurate forcing: a stronger counterexample

The headline `not_cutoffSix_robustBBPCouplingCriterion` refutes a precisely stated strategy.  Fix **any** finite prefix length N and **any** positive error schedule η(n).  There is a rational q and a rational residual sequence S such that:

- R is the actual cutoff-six reservoir, hence all its exits and their established arithmetic are retained.
- Through index N, R+S is exactly the original BBP rational head.  In particular the initial residual is zero.
- After index N, every nonintegral odd-prime pole of R survives in R+S with exactly the same p-adic norm.
- R+S stays within η(n) of `16^n q − 16^n piTail(n)` at every index.
- Its recurrence differs from the exact BBP forcing by less than η(n) at every step.
- q is not disjunctive in base 16.

The formal model is `ApproximateBBPModel`; the existence theorem is `exists_rational_approximateBBPModel`.  The stronger quantified refutation is `not_robustBBPCouplingCriterion`, valid for any prescribed rational reservoir R.  `rationalReservoir_cast` identifies the concrete rational reservoir with the original real-valued one.

The construction first chooses q close enough to pi to fit the finitely many exact prefix values.  Beyond that prefix, it chooses dyadic residuals approximating the desired real values.  Dyadic rationals are integral at every odd prime, so they cannot cancel a reservoir pole there.  If head errors are less than ε(n), the forcing defect is less than ε(n+1)+16ε(n).  Choosing ε(n)=min(η(n)/64,η(n−1)/4) fits both requested budgets.

The schedule can decay exponentially, faster than every exponential, or otherwise: only strict positivity is required.  The counterexample depends on the chosen schedule and prefix; a single counterexample matching every finite prefix is not asserted.

## Scope and the surviving question

This rules out an argument whose only inputs are the listed arithmetic, finite data, and pointwise error bounds.  It does not rule out exploiting the exact BBP formula at every index.  It also does not preserve the genuine residual's denominator restrictions: the dyadic denominators used for approximation have no height bound.  A proposed coupling argument must identify a property outside this comparison class, such as an exact algebraic relation in the forcing or sufficiently specific denominator information, and supply a mechanism that uses it.

The DFI–Chebotarev nonvanishing result remains intact.  Because the reservoir itself was never changed, stronger exit statistics alone do not distinguish these comparison models from the genuine split.  This is an obstruction to the stated inference, not a proof that the prime-reservoir route or pi disjunctivity is impossible.
