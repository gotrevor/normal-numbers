# Arithmetic moment budget and joint probability transfer

Bounded Opus/low lap. Work only here; main has an active G4 writer.
Reuse PrimeModelRadicalTail, PrimeModelRadical, PrimeModelComplement.
New module PrimeModelRadicalMoment.lean, root import, project note and handoff.
No axioms/sorry, no frozen statement edits, no unrelated sorries or sieve campaign.
Shared deps checked and ready. Full build and commit green before stopping.

PRIMARY: discharge the arithmetic budget, not merely rename its hypothesis.
The installed dependency has import PrimeNumberTheoremAnd.IEANTN.Mertens,
Mertens.sum_log_prime_div_eq_log (hx : 1 <= y):
 |sum p in Ioc 0 floor(y) with p.Prime, log p / p - log y| <= log 4 + 4.
Its source has no sorry. Check theorem ancestry once before relying on it.
For log y >= 2 this easily implies the deliberately loose bound <=8 log y.
Use finite prime SET P, or injective indexing (DO NOT omit injectivity),
each p prime and p<=y. For alpha=1/(2 log y), prove
 sum_{p in P} ((p:Real)^alpha -1)/p <=20.
For example show exp t -1 <=2t on 0<=t<=1/2; then the sum <=8, leaving
ample room under20.  No need to optimize constants. Use existing exp
convexity/derivative bounds. This avoids recreating Mertens or Chebyshev.

Required theorem radical_moment_budget: the above <=20 with log y>=2,
P finite primes <=y.  Required radical_box_tail_exp20: instantiate
radical_box_tail with prime index {p // p in P}, every p>=k, T>=1,
alpha as above, and no remaining moment-budget hypothesis.
Expose the direct result k*exp20 / T^(1/(2logy)). If easy, specialize
T=x^(1/(4k)), y=x^epsilon to k*exp20*exp(-1/(8k epsilon)), k>=1,
x>1, epsilon>0, log(x^epsilon)>=2. Do not let this optional step consume lap.

SECONDARY, if primary green: joint uniform-residue transfer.
For any nonempty finite residue type R and radical state S, define model
mu(r,s)=weight(s)/(Fintype.card R). Prove normalized, nonnegative, and
tail outside R x B(T) equals the state-only tail. Compose the existing
probability_complement_phase for any normalized actual nu on R x S.
Result <=2*k*exp20/T^alpha+2delta from retained JOINT L1 discrepancy<=delta.
Name radical_joint_phase_transfer. This is needed because empirical residue
masses are not exactly uniform for finite x; do not assume nu's marginal is uniform.
Small-prime phase factor can depend on r. If this secondary task does not fit,
leave it explicitly open, with PRIMARY committed and built.

Correct the old tail note: it quoted a 2 log y prime bound as if supplied;
this lap uses the actual dependency bound log y+log4+4 and a loose8 log y.
Record exact remaining obligations: general CRT counting, two-sided sieve
discrepancy, phase decay and final constants. This proves a selected-prime
shortcut layer, NOT G4 normality.
