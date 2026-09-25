```sh
cd /Users/gotrevor/src/nn-c3mrt && lake env lean reviews/2026-09-25-input-audit/C3MrtInputAudit.lean
```

# C3-MRT mathematical input audit, 25 September 2026

Review snapshot: branch `wip/c3-mrt`, commit `0134c0d`.  Relevant definitions: `src/NormalNumbers/C3MrtTTThm31.lean` and `src/NormalNumbers/C3MrtUnifK.lean`.  Another session owns the active changes to `C3MrtSlowSched.lean`; this audit does not change those files.

## Findings

### 1. Nonpretentiousness has a misplaced quantitative constant

The current definition has quantifier order

    TTNonPretentious g X L := exists A>0, forall allowed t, A*L <= exp(sum(g,X,t)).

For the constant function g=1, every summand is `(1-cos(t log p))/p >= 0`.  For every L>0, choose A=1/L.  The named hypothesis therefore holds for the maximally pretentious constant function at every scale.  The same nonnegativity argument applies to any pointwise 1-bounded function.

This makes `KPointNoExcWith` impossible when its exponent at K=2 is positive and its multiplicative constant is finite.  Take both functions constantly one, W=1, shifts 1 and 2, and sufficiently large L.  Choose X=exp(L) and N=ceil(sqrt(X)); eventually sqrt(X)<=N<=X and the shifts are at most L^c.  The normalized dyadic sum over N<n<=2N is exactly 1.  Its purported upper bound C*L^(-c) tends to zero.  This argument is independent of the unknown ordinary-average Elliott problem.

**Persistent Lean witnesses:** `ttNonPretentious_const_one` proves the bad hypothesis at every positive L.  `kPointNoExcWith_one_one_two_false` gives the concrete contradiction with c=C=1, K=2, X=N=16, L=2, W=1 and shifts 1,2: 1<=1/2.  The latter witness is for those fixed constants; the preceding mathematical limit argument addresses arbitrary positive c and finite C.

### 2. The exceptional set can swallow every tested scale for free

`TwoPointNaturalCorrelation` charges a measurable subset E of a real interval by `integral_E dt/t`, but tests the conclusion only at N:Nat.  Set E to all natural-number points in `[sqrt(X),X]`.  This countable set has Lebesgue measure zero, yet contains every N to which the conclusion could apply.

**Persistent Lean witness:** `twoPointNaturalCorrelation_vacuous` proves the entire current proposition with c=C=1, without using any arithmetic hypotheses.

### 3. The pretentious-distance parameters do not match the source

[Tao-Teravainen, arXiv:2512.01739v2](https://arxiv.org/abs/2512.01739), equation (1.18), minimizes over Dirichlet characters modulo q<=Q and real twists |t|<=X in M(g;X,Q).  Theorem 3.1 uses M(g;X^2,(log X)^(1/125)).  The Lean interface omits the characters and bounds t by the third parameter, whereas the source's twist range at that application is X^2.  Its implied constant must also be uniform in the scales, unlike the existential above.

## Consequence and required repair

The downstream conditional Lean implications can be correct while their assumptions are false.  This audit invalidates the current inputs as a route to a nonvacuous C3 result.  It does not refute C3 itself or affect the independent sparse-prime normality and logarithmic Elliott proofs.

Before further quantitative scheduling work:

1. Define the actual distance with characters and the correct height parameters.
2. Put absolute quantitative constants outside the scale quantifiers, with exactly the source's dependence.
3. State the exceptional-scale conclusion for real scales, or use a discrete weighted measure that charges each tested integer and prove the required conversion from the source theorem.
4. Recheck the concrete z^omega nonpretentiousness proof against those definitions.
5. Distinguish the published two-point almost-all-scale theorem from the genuinely stronger no-exception K-point hypothesis.

The wider twopoint route also needs a separate analytic bridge: the alternating identity in TT section 5.2 is used under a rationality contradiction hypothesis.  It is not by itself a bound on an arbitrary Weyl mean.  See the [portfolio review](/Users/gotrevor/src/normal-numbers/docs/REVIEW-2026-09-25-research-trajectory.md).

## Reproduction and interpretation

`C3MrtInputAudit.lean` imports the real current interface, not a copied test definition.  It was compiled with the repository's existing oleans; compiler output is saved in `compiler-output.txt`.  All three named audit results were inspected with `#print axioms`.

These are witnesses of the current defects.  After repairing the definitions, some proofs should cease to typecheck.  At that point replace them with the intended rejection/nonvacuity checks and retain this dated audit as history.  Do not change the repaired definitions to make a defect witness compile again.
