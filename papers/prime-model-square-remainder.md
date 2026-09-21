# A square remainder is sufficient

Ren / Codex, 2026-09-21.  Parameter audit for the arithmetic Brun lap.

## Remove the generalized divisor-sum dependency

The intended sieve primes satisfy p>k.  Thus k^card(E)<=product(E).
Distinct subsets of primes give distinct positive products.  If |lambda(E)|<=1
and lambda(E) vanishes above level R>=1, there are at most floor(R) supported
subsets, and each contributes at most R.  Hence

    sum_E |lambda(E)| k^card(E) <= R^2.

This includes the empty subset, whose product and root count both equal 1.
No estimate for a generalized divisor function is needed.

## Check against the actual frozen epsilon window

The frozen window is 1/log(log x)<epsilon<1/2, not a weaker inverse-log-x
window.  Its nonemptiness gives log(log x)>2 and x>exp(exp 2).
With Q<=x^(1/8), retained state count <=T^k=x^(1/4), and R=x^(1/4),
the sum of normalized retained-atom remainders is at most

    Q*T^k*R^2/x <= x^(-1/8).

For k>=1 this is already <=exp(-1/(8*k^2*epsilon)): indeed
1/(k^2*epsilon)<log(log x)/k^2<=log x.  Therefore the coarser count costs
only an absolute coefficient in C2, not a worse decay rate or growth class.
The lower-only phase transfer doubles this term.

This absorption is now proved as `square_remainder_absorbed` in
[PrimeModelErrorBudget.lean](../src/NormalNumbers/PrimeModelErrorBudget.lean),
using t=log x and the exact epsilon-window premise.

## Brun threshold and exceptional range

Use Y=floor(x^epsilon), R=x^(1/4), s=log R/log Y.  In the nonempty window
Y>=exp 2, and s>=1/(4*epsilon).  For epsilon<=1/(7680*k), s>=1920*k,
which is the support threshold for dimension24k.
Also log(4^k*exp(16k))=(log4+16)k<=18k, so
40log K+4<=720k+4<=1920k.  Both Brun size conditions follow.

For epsilon>1/(7680*k), the target error factor is at least exp(-960/k),
hence at least exp(-960).  The trivial phase bound 1 is absorbed by the
absolute coefficient exp960 in C2.  This is deliberately coarse; tuning it
does not improve the required asymptotic growth condition.

The exceptional-epsilon bound is proved in the same module as
`brun_large_epsilon_absorbed`.  The numerical threshold and remaining
parameter substitutions in this section are still paper-level.

The small-x exception needed for Q<=x^(1/8) is unchanged from the earlier
assessment: Q<=4^k gives the sufficient threshold x>=4^(8k).
Below it, 1/epsilon<log(log x)<=log(8k log4), so the cost in C2 is at most
exp(log(8k log4)/(8k^2)).  No additional growth obstruction appears.

## Remaining obligations

This is a parameter derivation, not a completed selected-prime theorem.
The arithmetic lap proves the actual sifted count and the R^2 remainder.
State/predicate identification, injectivity into retained integer tuples,
the bound on their number, phase decay and final assembly remain separate
Lean obligations.  The old sharper divisor-sum route remains valid, but is
not a prerequisite for this route.
