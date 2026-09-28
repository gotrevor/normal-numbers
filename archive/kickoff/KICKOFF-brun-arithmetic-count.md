# Active attended override: quantitative lower arithmetic sieve

Trevor said next on 2026-09-21.  Opus/low, one scoped lap in main.
Supersedes stale campaigns.  Stop after this task; no fallback objectives.

## Deliverable

New module src/NormalNumbers/PrimeModelBrunCount.lean imports
PrimeModelPrimeDimension and PrimeModelRadicalCRT.
Prove named targets `brun_remainder_le_square` and `brun_sifted_count_lower`.
Existing definitions and theorem statements are frozen.  No new analytic
hypotheses.  Only this module, its root import and a dated handoff are owned.

For h>=1, finite disjoint prime sets A,U, all primes >h, U bounded by integer
y>=exp 2, Q>0, r<Q, Q coprime to every prime of A union U, assignment
j:Nat -> Fin h, X:Nat, and s>=1920h and
s>=40*log(4^h*exp(16h))+4, prove the actual arithmetic count:

  card {n<X : Radical.SiftedCond h A U Q r j n}
    >= (1-2*exp(-s/2)) * X/(Q*product A) * product_U(1-h/p)
       - (y^s)^2.

Casts to Real as needed.  No `Dimension`, sieve-weight, counting-error or
root-cardinality hypothesis may remain: existing theorems discharge them.
X=0 is allowed; no unjustified positivity of 1-eta is needed.

## Remainder simplification

Do NOT build a generalized divisor function unless this route fails.
For any weights lambda(E) with |lambda|<=1 and support product(E)<=R, R>=1,
and U a finite set of primes p>h:

  sum_{E subset U} |lambda(E)| * h^card(E) <= R^2.

Each h^card(E)<=product(E).  The map E -> product(E) is injective on subsets
of distinct primes (prove via p divides product iff p in E).
Supported products are positive integers <=floor R.  Thus there are <=floor R
of them; each summand <=R, giving floor R * R <=R^2.
Include empty E: product=1, rho=1.  Prove this as brun_remainder_le_square.
This is coarser than R(1+log R)^(h-1), but sufficient for this application's
error budget and avoids unnecessary divisor-sum machinery.

## Counting transfer

Apply the Brun pointwise minorant to the hit-prime subset at each n with the
base assigned conditions; sum n<X and interchange finite sums.
Use Radical.radical_sieve_count for each E subset U.
Main term factors as X/(Q*D) times the Brun weighted density sum.
Use PrimeDensity.prime_density_brun_lower for all three weight properties.
Apply the remainder bound with R=y^s.  R>=1 follows from y and s.
Read the existing Legendre proof for finite indicator rearrangements; its
private lemmas can be locally reproved, but do not edit that module.

## Why R squared is sufficient (operator is checking target constants)

For retained joint atom count <=Q*T^h, Q<=x^(1/8), T^h=x^(1/4),
R=x^(1/4), normalized sum of remainders <=x^(-1/8).
The sharp divisor-sum estimate is not required for decay.
Do not claim the final selected-prime theorem from this counting result:
state encoding/cardinality, phase decay and parameter assembly remain.

Commit a compiling skeleton early; permanent small numeric controls in Lean.
Build module and full project, record exact hypotheses in the handoff.
No progress-by-sorry-count reporting.  box done --green after both theorems,
then stop.
