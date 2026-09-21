# Audit of the specialized prime-model proof

Ren / Codex, 2026-09-20.  Paper-level audit of
[the recovered candidate](prime-model-complement-2026-09-20.md).
The original KMT derivation remains in `kmt-2023-prop43-k-dependence.md`.

## Verdict and scope

The arithmetic interface in §2 survives this audit.  Below is the explicit
progression calculation underlying its root counts, main term and remainder.
The complement argument is valid for the infinite model support, not just its
finite truncations.  One Opus/low lap proved all three frozen statements in
`src/NormalNumbers/PrimeModelComplement.lean`:
discarded mass, full L1 distance, and transfer to arbitrary bounded complex phases.

This does not constitute a Lean proof of `KMT_quant₂`.  The sieve theorem,
prime estimates, arithmetic counting, model moment bound and their assembly
remain paper arguments.  The selected-prime existence theorem consumes the
exact `KMT_quant₂` statement in `G4WiringSparse.lean`.
The shortcut does not establish G₄ normality.

## Exact progression and root counts

Take k ≥ 1 and a valid tuple of pairwise coprime positive integers d₁,…,d_k,
all with prime factors in (k,y].  Put D = ∏d_j and Q = ∏_{p≤k}p.
For each r modulo Q, CRT gives a unique a in [0,QD) with
a ≡ r mod Q and a ≡ −j mod d_j.  Write n = a + QD t, with t restricted by
0 ≤ n < x.  The permitted t form an interval of real length x/(QD).

* If p divides d_j, the exact exponent of p is enforced by
  (a+j)/d_j + (QD/d_j)t ≠ 0 mod p.
  The coefficient QD/d_j is invertible modulo p, even when d_j includes p to
  a high power: pairwise coprimality puts the entire p-power in d_j.
  There is exactly one forbidden root.  Every other n+i is automatically
  prime to p, since 0 < |i−j| < p.
* If p does not divide D, QD is invertible modulo p, and
  a+j+QD t ≡ 0 mod p gives one root for each j.  These k roots are distinct,
  again since the differences of site indices have magnitude less than p.

For a squarefree e built from the sieve primes, CRT on t therefore gives
ρ_d(e) = ∏_{p|e}ρ_d(p), with ρ_d(p) = 1 or k as above.
Each root class has count x/(QD e) with error at most one.  Thus the count
for all root classes has error at most ρ_d(e), uniformly in a,Q,D and x.
This is valid even if QD e > x; no hidden minimum progression length is used.

Define m(t) as the squarefree product of forbidden primes actually hit by t.
Then e|m(t) expresses precisely these root conditions.  The indicator m(t)=1
is exactly the indicator that the prescribed tuple has its exact valuations.
This is the integer to which the pointwise upper/lower sieve inequalities apply.

## Source and normalization

Checked the local source text, lines 1962 onward, and the
[primary source, Matomäki–Teräväinen Lemma 9.1](https://arxiv.org/html/2301.07679#S9).
It supplies bounded coefficients supported on squarefree divisors of P(z) up
to the chosen level, pointwise inequalities in both directions, and the explicit
relative error under the interval dimension condition.

Use z=2y and set the density to zero for primes outside (k,y].
The integer m(t) never contains those other primes, so their divisors contribute
zero in both the counting and model sums.  The use of 2y includes a prime exactly
equal to y while respecting the source's strict p<z endpoint.

Multiplying the progression density 1/(QD) by the sieve product gives

    (1/(QD)) ∏_{p|D}(1−1/p) ∏_{k<p≤y, p∤D}(1−k/p) = μ(d)/Q.

In particular, higher valuations are retained through 1/D.  Replacing d_j by its
squarefree radical would give the wrong measure.

There are at most Q floor(T)^k retained pairs (r,d), with
Q≤x^(1/8), T=x^(1/(4k)), and sieve level R=x^(1/4).
The remainder divided by x is at most

    Q floor(T)^k R (1+log R)^(k−1) / x
    ≤ x^(−3/8) (1+log x)^(k−1).

The relative sieve errors sum against retained model mass ≤1.
Both one-sided counts therefore give the claimed retained L1 bound Δ.

## Remaining estimates and the exact Lean interface

The subsequent steps also survive paper-level checking:

* The one-site model marginal is geometric, including its zero state.
  With α=1/(2 log y), its exponential moment bound is independent of k.
  The union bound then yields the stated discarded model mass.
* For normalized nonnegative laws, the missing actual mass is obtained from
  normalization.  No distributional assumption is made outside the retained set.
  Absolute summability is needed when passing to infinite L1 sums and complex
  expectations; this is explicit in the frozen Lean statements.
* Primes k<p≤2k are handled by a binomial product, not by a Taylor expansion
  near k/p=1.  Above 2k the quadratic correction is summable with total ≤k/2.
* The complex inequality used for the exact Euler factor is global.  Squaring
  reduces it to 1+t≤exp(t), with t=|1+w|²−1≥−1.
* Restoring large primes costs the reciprocal-mass term and endpoint errors.
  In n=0,…,x−1 with sites j=1,…,k, only primes up to x+k−1 can occur.
  The tail (x,x+k] has at most k primes and at most one multiple per site when
  x≥2k, yielding the claimed O(k²/x) normalized error.
* The nonempty ε-range implies log x>e² and log y>2.
  The trivial-bound regimes and log-power remainder are absorbed with
  log C₂(k)=O(k log(k+2)); log C₁(k)=O(k).
* For integral primes, p≤y iff p≤floor(y), and y<p≤x iff floor(y)<p≤x.
  This matches the frozen Lean `recipSumLe` and `recipSumIoc` endpoints.
  No x=0 or site j=0 convention enters: x≥3 and the sites start at 1.

Next mathematical work: package the retained-box sieve estimate as a named
interface, formalize the model and its moment bound, and combine them through
the complement theorem.  The completed Opus task covers only the elementary
probability layer.  Retain the original KMT route as a broader comparison.
