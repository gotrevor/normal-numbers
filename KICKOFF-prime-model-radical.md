# Finite radical model

Read CLAUDE.local.md and existing PrimeModelComplement.lean first.  Work only in
this worktree.  Keep the original valuation argument and broad proof route intact.

Create src/NormalNumbers/PrimeModelRadical.lean, import it from the root module,
and prove a useful finite model layer.  No axioms, sorry, or frozen-target edits.
Use namespace NormalNumbers.PrimeModel.Radical.  Model at each prime p > k:
Option (Fin k), none mass 1-k/p, each some j mass 1/p.  Independent finite
products over a finite prime index type.  Real weights, complex phases.

Required mathematical results (choose ergonomic exact Lean signatures):
1. local weights nonnegative and sum one;
2. product law nonnegative and sum one;
3. local phase expectation = 1 + (sum_j (z_j-1))/p;
4. global phase expectation factors as the product of those local factors;
5. single-site moment identity, preferably for arbitrary real multipliers t_p:
   E product_p (if state_p=some j then t_p else 1)
   = product_p (1+(t_p-1)/p).
Name the global results radical_mass_one, radical_phase_product,
radical_site_moment.  Avoid unnecessary analytic bounds in this lap.

You may parameterize reciprocal probabilities q_p instead of primes if it
simplifies proofs, but expose the prime-specialized formulas too.  This is an
actual model change, NOT truncating the old valuation law to squarefree support.
All higher valuations are merged into the same some j state (mass 1/p).

Mathematical bridge for documentation (not required Lean in this lap):
d_j(n)=product of p in (k,y] dividing n+j.  D=product_j d_j.
mu(d)=1/D * product over unassigned p of (1-k/p).
After fixing n mod Q and assigned divisibilities, progression modulus QD:
assigned primes need NO exclusion (g=0); unassigned primes exclude k roots
(g=k/p).  Thus sieve main product/(QD)=mu(d)/Q.
With alpha=1/(2 log y), y>=e^2, the moment identity gives
E d_j^alpha <= exp(sqrt(e)*alpha*sum_{p<=y} log(p)/p) <= exp(4 sqrt(e)).
The old e^20 bound is therefore retained without geometric series.
This does NOT prove the needed two-sided fundamental lemma: mathlib's
SelbergSieve contains upper-bound machinery, not that full analytic input.

Write papers/prime-model-radical.md documenting model change and residual
analytic obligation.  Full lake build, commit green work, leave HANDOFF-radical.md.
Shared deps and project outputs are prepared.  No new worktree or dependency
downloads needed.  Persistent CLI controls in the personal KB instrument now
check k=2, primes 3,5, n even mod30: radicals (3,5) hit n=8 (where n+1=9),
(1,1) hit 0,6,12; (3,1) hit 2,20,26; (15,1) hit14.
