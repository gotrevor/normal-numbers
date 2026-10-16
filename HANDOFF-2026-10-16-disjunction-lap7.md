# Disjunction Lean lap 7 (2026-10-16): Hermite crux for the HypA log family

Binding kickoff: `KICKOFF-2026-10-16-disjunction-lean.md`.

## Concrete advance

The kickoff done condition and its first two stretches remained complete at the start of this lap.
The next ordered conditional stretch is T-C from the joint-orbit report: under Bailey--Crandall
Hypothesis A, every nonzero rational combination of `log 2` and `log 3` is base-4 normal.

Lap 6 identified irrationality of all those combinations as the likely new crux.  The existing
`irrational_log_div_log` theorem only rules out a *zero* integral combination.  A combination
could a priori equal a nonzero rational, so the missing input really is Hermite's theorem.

`MasterLogFamily.lean` now discharges that input without a cited axiom:

- `exp_nat_ne_rat` generalizes the repository's prior `exp_nat_ne_nat` argument.  Mathlib's
  `LindemannWeierstrass.exp_polynomial_approx` at `X - j` gives an integer of norm `< 1`; clearing
  the candidate rational's denominator preserves the prime-divisibility contradiction.
- `exp_int_ne_rat` handles negative exponents by inversion.
- `irrational_int_log_combination` exponentiates a purported nonzero rational value and invokes
  `exp_int_ne_rat`; when that rational is zero, multiplicative independence of 2 and 3 closes it.
- `irrational_rat_log_combination` clears the two coefficient denominators.

Thus the T-C arithmetic prerequisite is complete at the standard trust baseline.  The uncertainty
recorded in lap 6 is gone; what remains is series and polynomial bookkeeping.

## Exact verification

```text
lake env lean src/NormalNumbers/MasterLogFamily.lean
```

Succeeded with no output.

```text
lake build NormalNumbers.MasterLogFamily
```

Succeeded: `Build completed successfully (8726 jobs)`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-disjunction \
  --target NormalNumbers.MasterLogFamily \
  --import NormalNumbers.MasterLogFamily \
  --axioms NormalNumbers.MasterConjectures.exp_nat_ne_rat \
  --axioms NormalNumbers.MasterConjectures.exp_int_ne_rat \
  --axioms NormalNumbers.MasterConjectures.irrational_rat_log_combination
```

Verdict: `FORMALIZE-TIER GREEN`; all three declarations have exactly
`[Classical.choice, Quot.sound, propext]`.

The same command without `--target` ran the full repository gate:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-disjunction \
  --import NormalNumbers.MasterLogFamily \
  --axioms NormalNumbers.MasterConjectures.exp_nat_ne_rat \
  --axioms NormalNumbers.MasterConjectures.exp_int_ne_rat \
  --axioms NormalNumbers.MasterConjectures.irrational_rat_log_combination
```

Verdict: `FORMALIZE-TIER GREEN`; `Build completed successfully (10853 jobs)` and the same
three standard axiom lists.

## Current blocker / next highest-value attack

There is no external blocker.  Continue T-C in `MasterLogFamily.lean`:

1. Prove the grouped base-four identity
   `log 2 = sum' n, (1/(2(n+1)) + 2/(2(n+1)-1)) / 4^(n+1)` from
   `LnTwo.hasSum_lnTwoSeries` by pairing consecutive terms.
2. Prove `log 3 = 2*log 2 - sum' n, 1/((n+1)*4^(n+1))` using the Mercator
   series for `log (4/3)`.
3. For rational coefficients `a,b`, combine these into one kick
   `(a+2b)(1/(2n)+2/(2n-1)) - b/n`; clear coefficient denominators to explicit
   `p q : Int[X]`, prove `p != 0`, `natDegree p < natDegree q`, and `q(n) != 0`.
4. Bound the scaled tail geometrically, then invoke `hypA_isNormal_of_kicked` with
   `irrational_rat_log_combination`.

The safest first next lemma is the grouped `log 2` `HasSum`: it tests the reindexing machinery
before committing to the final polynomial normal form.

## Completion marker

After the green commit, this lap called

```text
box done "kickoff done condition remains green; T-C Hermite crux discharged axiom-clean"
```

The lap stop was signalled, but the host reported that its repo-wide self-stop gate will decline
because unrelated campaigns leave 105 open source sorries.  This is not a blocker and does not
justify `box stuck`; a relaunched lap should continue the ordered T-C stretch above.
