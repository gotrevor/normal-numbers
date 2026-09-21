# NN: a probability-mass shortcut to the specialized correlation estimate

Ren / Astra, 2026-09-20.  **Status: candidate paper argument with a recorded counting-step audit; its probability-complement layer is now formalized, while the sieve/model estimate and analytic assembly remain at paper level.**  See [the audit](AUDIT-prime-model-complement-2026-09-20.md) and [the three probability theorems](../src/NormalNumbers/PrimeModelComplement.lean).

**Revision after Fable's referee report and source lookup:** the sieve input is now Matomäki–Teräväinen's Lemma 9.1, which states the required standard dimension hypothesis and explicit constants together.  The small-prime cutoff remains k.  A 4k workaround for Thorner–Zaman's different printed hypothesis is preserved as an audit note, not an extra mainline requirement.  Both proof routes remain active; the original KMT derivation, its corrections, and its historical versions are preserved.  See [the two-proof plan and source audit](/Users/gotrevor/personal/claude/knowledge/core/projects/normal-numbers-two-proof-plan-2026-09-20.md).

## Upshot and exact delta

**Finite-model follow-up:** [prime-model-radical.md](prime-model-radical.md)
replaces the exact-valuation law below by its prime-presence pushforward.
Normalization, phase factorization, and the moment identity are formalized in
`PrimeModelRadical.lean`.  The valuation version remains here as the audited
original argument; its warning against squarefree *truncation* does not rule
out merging all valuations into radical states with their full mass.

For the particular functions needed here, there is a potentially much shorter route than re-running all of KMT §4.  Use an exact independent-prime model for the small-prime parts of consecutive integers.  Sieve only the tuples whose coordinates are small.  Then obtain the actual discarded tail by **subtracting the retained mass from one**, instead of separately estimating smooth numbers in progressions.

The candidate argument gives the existing `KMT_quant₂` statement with

\[
\log C_1(k)=O(k),\qquad \log C_2(k)=O(k\log(k+2)).
\]

Thus the already-formalized harmonic block construction suffices; the [variable-mass schedule](/Users/gotrevor/personal/claude/knowledge/core/projects/normal-numbers-flexible-block-schedule-2026-09-20.md) remains a useful generalization but is not required for this route.  If the argument survives audit, its conclusion is existence of a normal **selected-prime** Lambert constant, not normality of G₄ or any classical constant.

Precisely, let \(S_{\mathcal P}(a,b)=\sum_{a<p\le b,\,p\in\mathcal P}1/p\), \(S_{\mathcal P}(b)=S_{\mathcal P}(0,b)\), and \(W=x^{-1}\sum_{0\le n<x}\prod_{1\le j\le k}\exp(2\pi i h\,\omega_{\mathcal P}(n+j)/4^j)\).  For every prime set, every integer h with at least one nonintegral h/4^j in the window, x ≥ 3 and \(1/\log\log x<\varepsilon<1/2\), the proposed estimate is

\[
|W|\le C_1(k)\left[\sqrt{\log(1/\varepsilon)}\sqrt{2S_{\mathcal P}(x^\varepsilon,x)}
+e^{-S_{\mathcal P}(x^\varepsilon)}\right]
+C_2(k)e^{-1/(8k^2\varepsilon)}.
\]

The arithmetic restriction doing the work is **strong multiplicativity**: \(z^{\omega_{\mathcal P}(n)}\) depends on whether a prime divides n, not its positive valuation.  Conditioning on small primes therefore needs only a primorial modulus, not the unbounded small-prime valuation tuples in the general proof.  Novelty is not claimed for the underlying sieve/probability method.

## 1. Parameters and the probability model

Fix k ≥ 1, let x be an integer, put y = x^ε, and let

\[
Q=\prod_{p\le k}p,\qquad T=x^{1/(4k)},\qquad R=x^{1/4}.
\]

For now x is large enough that Q ≤ x^{1/8}, x ≥ 2k and y ≥ e².  Small x and large ε are absorbed in §7.

For n uniform in {0,…,x−1}, record its residue r modulo Q and

\[
d_j(n)=\prod_{k<p\le y}p^{v_p(n+j)},\qquad 1\le j\le k.
\]

The d_j are pairwise coprime: a prime p > k cannot divide two of the k consecutive integers.  Do **not** replace these smooth parts by squarefree radicals when counting their exact valuations.

Define a model law μ on such tuples.  Independently for each prime k < p ≤ y:

- no coordinate receives p, with probability 1−k/p;
- coordinate j receives exponent ℓ ≥ 1, with probability (1−1/p)p^{−ℓ}.

The probabilities sum to one, since each coordinate receives total probability 1/p.  Also take r uniform modulo Q, independently of these primes.  If D = d₁⋯d_k, the tuple mass is exactly

\[
\mu(d)=\frac1D\prod_{p\mid D}(1-1/p)
                   \prod_{\substack{k<p\le y\\p\nmid D}}(1-k/p).
\tag{1}
\]

This is a probability law on all smooth tuples, with no size cutoff on the d_j.

## 2. Sieve approximation on the small box

Let B consist of tuples with every d_j ≤ T.  Then D ≤ x^{1/4}, and there are at most T^k = x^{1/4} tuples in B.

For fixed r and d, the congruences n ≡ r (mod Q), d_j | n+j have one solution modulo QD.  In the resulting progression, requiring that d_j be the *exact* large-small-prime part means excluding residues modulo each k < p ≤ y.  Their density is

\[
g_d(p)=\begin{cases}1/p,&p\mid D,\\ k/p,&p\nmid D.\end{cases}
\tag{2}
\]

Indeed, if p | D it belongs to exactly one d_j and the quotient (n+j)/d_j must not be divisible by p.  Otherwise the k forbidden residues are distinct.  This argument uses only root counts, not a restriction that the progression coefficients be logarithmically small.

Use upper and lower sieve weights of level R.  To remove an endpoint convention, set the sieve parameter z = 2y and set g_d(p)=0 for all primes outside k < p ≤ y.  Then

\[
s=\frac{\log R}{\log(2y)}\ge\frac1{8\varepsilon}.
\]

Apply [Matomäki–Teräväinen, Lemma 9.1](https://arxiv.org/html/2301.07679#S9) with dimension k and level R.  Its hypothesis is the standard interval bound \(\prod(1-g_d(p))^{-1}\le K_k(\log z_1/\log w_1)^k\), verified for every interval in §7.  For \(s\ge9k+1\), its upper and lower weighted sums differ from \(V_d=\prod_p(1-g_d(p))\) in the needed directions by at most \(B_ke^{-s}V_d\), where \(B_k=e^{9k}K_k^{10}\).  There is no extra positivity threshold or squared upper multiplier in this single-sieve statement.  The same lemma supplies \(|\lambda_e|\le1\), squarefree support e ≤ R, and the pointwise two-sided sieve inequalities used below.

For clarity, apply those pointwise inequalities to the squarefree product of the forbidden primes hit by each progression parameter.  The set of forbidden primes is empty exactly when the tuple has the prescribed valuations.  CRT gives the expected product of root densities for each squarefree e; the residue-counting error is at most its number of roots.  The main term after division by x is \(V_d/(QD)=\mu(d)/Q\), exactly (1).

The arithmetic remainder for each (r,d) is at most

\[
\sum_{e\le R}\mu^2(e)k^{\omega(e)}
\le\sum_{e\le R}\tau_k(e)
\le R(1+\log R)^{k-1}.
\tag{3}
\]

The first bound counts at most k^{ω(e)} roots; each residue class has counting error at most one.  The last bound counts ordered k-tuples with product ≤ R and sums 1/a over the first k−1 coordinates.

Let ν be the actual joint law of (r,d).  Summing absolute errors **only inside B** gives

\[
\sum_{r,\,d\in B}\left|\nu(r,d)-\frac{\mu(d)}Q\right|
\le B_ke^{-1/(8\varepsilon)}
   +x^{-3/8}(1+\log x)^{k-1}
=:\Delta.
\tag{4}
\]

The relative errors sum against a probability mass ≤ 1.  The remainder exponent is
1/8 + 1/4 + 1/4 − 1 = −3/8, from Q, the number of tuples, the sieve level, and normalization.  This is why an explicit sieve *level*, distinct from progression length, is specified.

## 3. A model tail bound with an absolute constant

For one coordinate, the marginal valuation at p is geometric:

\[
\mathbb P(v_p(d_j)=\ell)=(1-1/p)p^{-\ell}\quad(\ell\ge0).
\]

Choose α = 1/(2 log y).  Then

\[
\mathbb E_\mu d_j^\alpha
=\prod_{k<p\le y}\frac{1-1/p}{1-p^{\alpha-1}}\le e^{20}.
\tag{5}
\]

One elementary bound suffices: y ≥ e² gives α ≤ 1/4, p^α ≤ √e and p−p^α ≥ p/3.  Therefore each log factor is at most
\(3(p^\alpha-1)/p\le3\sqrt e\,\alpha\log p/p\).
The elementary Chebyshev bound gives \(\sum_{p\le y}\log p/p\le8\log y\), so the total is at most 12√e < 20.  Removing primes ≤ k can only decrease the moment.

Markov's inequality and a union bound now give

\[
\mu(B^c)\le k e^{20}\exp\left(-\frac1{8k\varepsilon}\right).
\tag{6}
\]

This is a tail estimate in an explicit probability model.  It is not a claim that actual smooth parts already have that distribution outside B.

## 4. The complement argument, the useful shortcut

For any probability laws ν and μ and subset B, if their L¹ difference inside B is at most Δ, then

\[
\nu(B^c)\le\mu(B^c)+\Delta,
\qquad
\|\nu-\mu\|_1\le2\mu(B^c)+2\Delta.
\tag{7}
\]

Proof: subtract the retained masses from one; then bound the outside L¹ difference by the sum of the two outside masses.  Consequently every test function of modulus at most one has expectation error at most the right side of (7).

Combining (4), (6), and (7), every bounded function of the entire small-prime data is approximated by its model expectation with error at most

\[
2ke^{20}e^{-1/(8k\varepsilon)}
+2B_ke^{-1/(8\varepsilon)}
+2x^{-3/8}(1+\log x)^{k-1}.
\tag{8}
\]

There is no separate actual smooth-number tail or weighted completion estimate.  Positivity and total mass are used **before** inserting the complex phases.

## 5. Insert the phases: a controlled first constant

Let \(|z_j|=1\), and for a prime set \(\mathcal P\) take the truncated product

\[
G(n)=\prod_{j=1}^k z_j^{\omega_{\mathcal P\cap[1,y]}(n+j)}.
\]

Its small-prime part p ≤ min(k,y) is a modulus-one function of r modulo Q.  For an active p > k, its model factor is **exactly**

\[
L_p=1-\frac{k}{p}+\frac1p\sum_{j=1}^kz_j
   =1+\frac1p\sum_{j=1}^k(z_j-1).
\tag{9}
\]

Summing the geometric valuation probabilities is what gives z_j/p, without any valuation-tuple constant.  Inactive primes have factor one.

Put A = Σ_j(z_j−1).  The elementary inequality
\(|1+w|\le\exp(\operatorname{Re}w+|w|^2/2)\)
and |A| ≤ 2k imply

\[
\left|\prod_{\substack{k<p\le y\\p\in\mathcal P}}L_p\right|
\le e^{2k}\exp\left[-\sum_j(1-\operatorname{Re}z_j)
                         \sum_{\substack{k<p\le y\\p\in\mathcal P}}\frac1p\right],
\tag{10}
\]

using \(\sum_{p>k}p^{-2}\le\sum_{n>k}n^{-2}\le1/k\).  The inequality in w is global: square it and use \(1+t\le e^t\) with \(t=2\operatorname{Re}w+|w|^2\ge-1\).  It does not require |w| < 1.

For z_j = exp(2πih/4^j) and `NontrivialWindow k h`, the first nonintegral phase has 1−Re z_j ≥ 1.  Hence (10), including the small-prime residue average of modulus ≤ 1, is at most

\[
e^{3k}\exp[-S_{\mathcal P}(y)],
\tag{11}
\]

since the omitted mass \(\sum_{p\le k}1/p\le k\).  Thus the constant on this distance term has logarithm O(k), with no sieve constant attached to it.

## 6. Restore the primes larger than y

Here strong multiplicativity again simplifies the argument: no prime-power correction is needed.  Telescoping the k products gives an error bounded by the average of

\[
\sum_{j\le k}\sum_{\substack{p>y\\p\in\mathcal P\\p\mid n+j}}|1-z_j|.
\]

For p ≤ x, count multiples with error at most one.  Chebyshev bounds the sum of these errors by O(k/log x).  Primes x < p ≤ x+k contribute O(k²/x).  The main reciprocal sum is, by Cauchy–Schwarz and the prime harmonic-sum estimate,

\[
\le A_0 k\sqrt{\log(1/\varepsilon)}\sqrt{2S_{\mathcal P}(y,x)}
\tag{12}
\]

with A₀ absolute.  This uses \(|1-z_j|^2=2(1-\operatorname{Re}z_j)\le4\) and
\(\sum_{y<p\le x}1/p\le A\log(1/\varepsilon)\); ε < 1/2 keeps the logarithm bounded away from zero.

## 7. Uniformity and constant growth

All model/counting bounds are uniform in the prime set and phases.  For every sifted prime, 0 ≤ g_d(p) ≤ k/p < 1.  Compare its interval product with the kth power of the dimension-one Mertens product.  For the range k < p ≤ 2k, simply discard the compensating factors \((1-1/p)^k\le1\) and bound

\[
\prod_{k<p\le2k}(1-k/p)^{-1}
\le\prod_{n=k+1}^{2k}\frac{n}{n-k}
=\binom{2k}{k}\le4^k.
\]

For p > 2k and t=k/p < 1/2,

\[
-\log(1-k/p)+k\log(1-1/p)
\le-\log(1-t)-t\le t^2.
\]

The quadratic error sums to at most \(k^2\sum_{n>2k}n^{-2}\le k/2\).  Both estimates also hold for subsets of their respective ranges, since the bounding factors are at least one.  A dimension-one Mertens interval bound therefore yields, for every 2 ≤ w₁ ≤ z₁,

\[
\prod_{w_1\le p<z_1}(1-g_d(p))^{-1}
\le K_k\left(\frac{\log z_1}{\log w_1}\right)^k,
\qquad K_k=(4e^{1/2}C_0)^k,
\tag{13}
\]

where C₀ > 1 is absolute.  Setting g_d to zero off its specified primes can only decrease the interval product.  This verifies the density hypothesis in Lemma 9.1, with log B_k = O(k).

Set

\[
H_k=9k+2=O(k).
\]

Use the sieve for ε ≤ 1/(8H_k); this guarantees s ≥ H_k > 9k+1.  Outside that range the target bound follows from |W| ≤ 1 after increasing C₂ by an absolute factor, since H_k/k² = O(1).  Below an x-threshold ensuring Q ≤ x^{1/8} and x ≥ 2k, use the same trivial bound.  Since Q ≤ (k+1)^k, the threshold has log log x₀(k) = O(log(k+2)), and its cost is at most
\(\exp[\log\log x_0(k)/(8k^2)]\).

The requirement y ≥ e² is automatic in the nonempty parameter range: ε < 1/2 and ε > 1/log log x imply t=log x > e² and log y > t/log t ≥ e²/2 > 2.  For the remaining errors use ε > 1/log log x:

\[
e^{-1/(8k^2\varepsilon)}\ge(\log x)^{-1/(8k^2)}.
\]

If t = log x, then
\(e^{-3t/8}(1+t)^{k-1}t^{1/(8k^2)}\le e^{-3t/8}(1+t)^k\le e(3k)^k\).
Thus the last term of (8) is absorbed at cost exp(O(k log(k+2))).  The O(k/log x+k²/x) error in §6 costs only a polynomial in k.  Both exponential terms in (8) decay at least as fast as the target sieve term for every k ≥ 1.

Taking C₁(k) = A₀k + e^{3k} and gathering these errors into C₂ gives precisely the frozen `KMT_quant₂` bound, with the growth claimed at the top.  Set harmless positive values at k=0, where the nontrivial-window premise is empty.

**Sanity check against the original open problem.**  For the set of all primes, \(S(x^\varepsilon,x)\sim\log(1/\varepsilon)\) at fixed ε as x grows.  The first term therefore does not become small when ε is subsequently sent to zero.  The argument has not smuggled in ordinary Chowla/Elliott cancellation.  The selected-prime construction works by arranging tiny fresh reciprocal mass while retaining unbounded old mass, exactly the two quantities that the estimate separates.

## 8. What Fable should audit first

1. Check the two-sided sieve-to-count conversion in §2, including exact valuations when p | D.  Check the density hypothesis, support and threshold against Matomäki–Teräväinen Lemma 9.1.  The binomial-product estimate in §7 covers primes just above k without a nonuniform Taylor expansion.
2. Check (7) before any complex weighting.  An upper sieve alone does not give (4); both signs are needed.
3. Check the Q, T and R exponents.  The sieve level is R, not x/(QD).
4. Check the exact Euler factor (9).  For k=2, p=3, z₁=i, z₂=−1 it is i/3.  Keeping only squarefree valuations changes the model and is incorrect.
5. Check the growth bookkeeping, especially the finite-x absorption.  No numerical scan is part of the proposed proof.

Suggested new paper/Lean nodes are `smallPrimeModel_box_L1`, `probability_complement_L1`, `smallPrimeModel_moment`, and `KMT_quant₂_of_primeModel`.  The existing KMT proof and the variable-mass proposal can stay unchanged until this independent route survives its audit.

For comparison, the general KMT estimate and its original decomposition are [Propositions 4.3–4.4 and §4.2](https://arxiv.org/html/2304.05344#S4).  This note does not certify every estimate in Fable's Parts I–III; it proposes replacing several of them in the specialized instance.

## 9. Persisted exact controls

Run `knowledge/core/projects/instruments/prime_model_certificate.py test -q` from the KB repository.  The [CLI](/Users/gotrevor/personal/claude/knowledge/core/projects/instruments/prime_model_certificate.py) and [external pytest suite](/Users/gotrevor/personal/claude/knowledge/core/projects/instruments/test_prime_model_certificate.py) check local valuation probabilities, CRT phase products over complete finite periods, sharp examples of the complement inequality, and the distinction between the standard and printed sieve factors.  The suite passed its fourteen CLI-driven controls on 2026-09-20.

The anchors are worked out independently of the implementation: for k=2, p=3, valuations capped at 2, the nine residues give counts 3,2,1,2,1 for no divisor, site 1 exponent 1/2+, and site 2 exponent 1/2+.  The squarefree-only states have mass 7/9, not one.  With phases (i,−1), the prime-3 mean is i/3, and adding primes 5 and 2 gives respectively (−1+2i)/15 and (−1−3i)/30.  Two complement examples attain equality and test both terms in its bound.

The four source-hypothesis controls include g=2/3, where the standard inverse factor is 3 but the printed one is −1; g=1/2, where the printed factor is undefined; and k=2,p=11 with and without a prescribed valuation.  These are algebraic diagnostics, not counterexamples to the sieve theorem under its actual hypotheses.  The [two-proof note](/Users/gotrevor/personal/claude/knowledge/core/projects/normal-numbers-two-proof-plan-2026-09-20.md) records the resolved citation and the optional 4k alternative.

These are algebraic/probabilistic regression controls, **not** experimental confirmation of the asymptotic sieve estimate or of normality.  They live in a separate instrument because the existing floating-point Lambert probe is being edited by the other sessions; no shared active file was modified.
