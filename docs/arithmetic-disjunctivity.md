# Disjunctivity from multiplicative coefficient arithmetic

2026-10-27.  **The generic theorem and the perfect-power Lambert applications are proved.**

The general statement is `ArithmeticDisjunctivity.genericArithmeticDisjunctivity` in
[`ArithmeticDisjunctivity.lean`](../src/NormalNumbers/ArithmeticDisjunctivity.lean).
It constructs digit visits from arithmetic hypotheses on the coefficients.
The hypotheses contain no orbit-density, word-visitation, or carry-tail premise.

## The general theorem

Let `f : N -> N` be multiplicative on coprime inputs, with `f(0)=0` and `f(1)=1`.
Assume:

1. `f(n) <= tau(n)` for every `n`, where `tau` is the ordinary divisor count.
2. There is one fixed `delta` in `{1,2}` such that `f(p)=delta` for every prime `p`.
3. For every integer `A>=2`, there is an exponent `e>=1` such that `f(p^e)=A` for **every** prime `p`.

Then, for every integer `b>=2`,

\[
X_{f,b}=\sum_{n\ge1}\frac{f(n)}{b^n}
\]

is disjunctive in base `b`.  The interface is
[`CoefficientSystem`](../src/NormalNumbers/ArithmeticDisjunctivityDefs.lean);
the scalar theorem is `isDisjunctive_coefficientValue`.
The exponent in condition 3 may depend on `A`, but must be chosen independently of the prime.
This order of quantifiers is needed before the CRT prime allocation.

The proved result is stronger: for any finite collection of integer bases, arbitrary
words occur at a common, arbitrarily late position in their respective constants `X_{f,b}`.
This is `jointCoefficientWords`.  The bases may share factors or be powers of one another.
These are different constants for different bases; the conclusion is not absolute
disjunctivity of one fixed constant.

## The arithmetic family

For a fixed integer `r>=1`, take

\[
a_r(n)=\#\{d\ge1:d^r\mid n\}.
\]

These coefficients are multiplicative, are bounded by `tau`, and satisfy

\[
a_r(p^e)=\left\lfloor e/r\right\rfloor+1.
\]

Thus the uniform exponent `e=r(A-1)` produces every `A>=2`; the prime value is
two for `r=1` and one for `r>=2`.  `powerDivisorCount_system` verifies the interface.
`powerLambert_eq_coefficientValue` gives the exact geometric-series regrouping

\[
\sum_{n\ge1}\frac{1}{b^{n^r}-1}
=\sum_{m\ge1}\frac{a_r(m)}{b^m}.
\]

The application is `isDisjunctive_powerLambert` in
[`PowerLambertDisjunctivity.lean`](../src/NormalNumbers/PowerLambertDisjunctivity.lean).
It covers the ordinary Erdos--Borwein series (`r=1`), the square-indexed proposal
(`r=2`), and every higher perfect-power exponent.  `jointPowerLambertWords` gives
the simultaneous-base statement for any fixed `r`.

## How the proof obtains the words

The existing finite encoder chooses an even integer that lies inside all requested
word cells after the appropriate base shifts.  To realize that integer arithmetically,
`exists_survivor_exponent` uses condition 3 and the uniform prime value to make
`f(q^E*p)=2a` for distinct primes `p,q`.

At every other early position `j`, the construction assigns `j+1` distinct primes
with one exact exponent.  Choose that exponent so the local coefficient value is
the product `c` of the requested bases.  Multiplicativity then gives
`c^(j+1) | f(n+j)`, so these contributions become integers in every shifted base.
`pow_card_dvd_of_exact_valuations` is the finite arithmetic step.

The decisive shared ingredient is
`JointLambert.exists_exact_valuation_small_tail` in
[`ArithmeticWitnessSupply.lean`](../src/NormalNumbers/ArithmeticWitnessSupply.lean).
It retains exact valuations, distinct allocated primes, and the prime survivor
through the existing rescaled prime-selection and ordinary-divisor tail estimates.
The bound `f<=tau` transfers that same-offset tail estimate to the new coefficients.
`floor_digit_of_coefficient_offset` then reads the desired word with a strict
margin against carries.  All old prime-candidate and tail theorem signatures are
preserved as wrappers around the strengthened witness versions.

## Controls and scope

[`ArithmeticDisjunctivityControls.lean`](../src/NormalNumbers/ArithmeticDisjunctivityControls.lean)
proves that ordinary divisor counts satisfy the interface.  It also proves that
constant positive coefficients and prime-power values restricted to powers of two
fail the coefficient-writing hypothesis.  The latter is the obstruction in the
retired squarefree-indexed single-survivor route.  These controls do not claim that
every coefficient system excluded by the sufficient hypotheses is nondisjunctive.

The theorem establishes disjunctivity, with simultaneous recurrence of arbitrary
finite words.  It gives no normality or positive frequency conclusion.  It makes
no claim about the digits of pi, log(2), or sqrt(2), and no claim of literature
priority.  The source of the construction is the repo's Erdos--Borwein proof;
the extension isolates its coefficient arithmetic and applies it to power-divisor
counts.

The original [square-Lambert proposal](square-lambert-proposal.md) records the
target-selection argument and initial forecast.  All of its formal gates now have
proofs in `PowerLambertDisjunctivity.lean`, including the exact witness supply,
coefficient window supply, factorization, single-coefficient writer, and series
regrouping.  The generic coefficient theorem and its arithmetic applications are
the resulting proof route.
