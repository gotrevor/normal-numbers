# Cutoff-six nonvanishing by positive-density thinning

The restricted equidistribution theorem sought in the previous handoff is unnecessary for nonvanishing.  The Lean theorem `CutoffSix.nonvanishing_of_dfi_chebotarev` proves the implication from two explicit literature inputs in [ReservoirCutoffSixDensity.lean](../../src/NormalNumbers/PiDisjunctiveRoutes/ReservoirCutoffSixDensity.lean).  It does not prove those inputs in Lean, and it does not establish anything about π's digits.

## The missed degree of freedom

`RestrictedRootFar` asked for distance at least 1/4.  The preceding counting objection was correct for that fixed distance: a small positive-density prime set can avoid a region of measure 1/2.

`ExitSixNonvanishing`, however, only asks for some fixed ε > 0.  We can shrink the forbidden neighborhood of zero until its total root count is smaller than the supply of eligible primes.  No independence or equidistribution within the eligible set is needed.

Let S(X) count primes p < X with p = 120t+1 and 2^(20t) ≠ 1 mod p.  Let Bε(X) count all primes p < X for which at least one root of x²+64x+4096 has distance less than ε from an integer after division by p.

1. Positive density supplies S(X) ≥ δ π(X) eventually, for some δ > 0.
2. Unrestricted quadratic-root equidistribution supplies, for a sufficiently small fixed ε > 0, Bε(X) ≤ (δ/2) π(X) eventually.
3. Therefore S(X) − Bε(X) ≥ (δ/2) π(X), which grows without bound.
4. Infinitely many eligible primes have **all** quadratic roots outside the boundary neighborhood.  Opus already proved that their full cutoff-six exit numerator is one such root.  The exit distance is therefore at least ε infinitely often.

The finite counting step is `exists_large_mem_not_mem`.  The bridge is `quadraticRootEscape_of_density`, followed by Opus's `nonvanishing_of_quadraticRootEscape`.  No theorem with the old fixed threshold 1/4 is claimed.

## The two inputs, kept visible

**`DFIBoundaryScarcity`.**  This is a weakening of unrestricted Duke–Friedlander–Iwaniec, *Equidistribution of roots of a quadratic congruence to prime moduli*, Annals of Mathematics 141 (1995), pp. 423–441, Theorem on p. 424.  The introduction and theorem were read from the locally stored paper.  Its normalization is root count divided by π(X); its theorem applies because a=1, b=32, c=4096 give ac−b²=3072>0.  The two boundary intervals have total length 2ε, so their root count is asymptotic to 2ε π(X).  Bad-prime count is bounded by bad-root count.  This yields the stated arbitrarily small upper bound.  The Lean input is global and contains no eligibility restriction.

**`EligibleChebotarevDensity`.**  This pins density 1/48 for S among all primes; `eligiblePositiveDensity_of_chebotarev` proves that it supplies the weaker lower bound needed above.  The number-field specialization is an external input, with the following arithmetic justification:

- L = Q(ζ₁₂₀) is an abelian Galois extension of degree 32.
- L cannot contain ∛2: every intermediate field of an abelian Galois extension is Galois over Q, whereas Q(∛2) is not.  The cubic polynomial therefore remains irreducible over L.
- K = L(∛2) is Galois over Q, of degree 96, with Gal(K/L) cyclic of order three.  Its two nonidentity elements form a conjugacy-stable subset.
- Primes p ≡ 1 mod 120 split completely in L.  Their Frobenius in Gal(K/L) is nonidentity exactly when 2 is not a cube modulo p.  Since p ≡ 1 mod 8, 2 is already a square, and this is equivalent to 2^((p−1)/6) ≠ 1.
- Chebotarev gives density 2/96=1/48 for those two elements.  The finitely many ramified primes do not affect density.

The number-field argument and Chebotarev are not formalized here.  The kernel-checked conclusion is the implication from these explicit inputs, not an unconditional Lean proof of nonvanishing.  No restricted DFI theorem is assumed.

## What this changes next

The nonvanishing subproblem now has an argument from unrestricted DFI and the explicit Chebotarev specialization.  Searching for a special restricted-DFI source is unnecessary for that argument.  The `RestrictedRootFar` conjecture remains stronger in its fixed-distance requirement.

For the original π objective, the obstacle is unchanged: `reservoirS_add_residualS` proves that exit transfers cancel from R+S.  A new mechanism must constrain this sum using the arithmetic of the decomposition.  Nonvanishing alone supplies no such constraint.
