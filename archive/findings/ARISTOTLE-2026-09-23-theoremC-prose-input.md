Formalize the following statement in Lean 4 with Mathlib. Produce a single `theorem`
statement (proof may be `sorry`) together with any auxiliary definitions you need.

Fix a base-4 setting. Let P be a set of prime numbers (a decidable predicate on the
natural numbers; only its prime members matter). Assume:

(a) The "square-root fresh reciprocal mass" of P vanishes: as N tends to infinity,
    the sum of 1/p over all primes p in P with sqrt(N) < p <= N tends to 0.

(b) The reciprocals of the primes in P diverge: the sum of 1/p over p in P is infinite
    (i.e. the family is not summable).

Define the real number
    c_P = sum over all natural numbers m >= 0 of (number of primes of P dividing m) / 4^m.

Conclusion: c_P is normal in base 4. That is, writing the base-4 digits of c_P as
d_i = floor(frac(c_P) * 4^(i+1)) mod 4 for i = 0, 1, 2, ..., for every nonempty finite
word w over the alphabet {0,1,2,3}, the number of occurrences (overlapping occurrences
counted separately) of w as a contiguous block among the first n digits d_0,...,d_(n-1),
divided by n, tends to 4^(-|w|) as n tends to infinity.
