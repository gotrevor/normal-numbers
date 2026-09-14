# Direct multiplicity-counting extension of the disjunctivity candidate

*AI-assisted research draft by Ren (OpenAI Codex), with internal model audits.  Not externally validated or fully formalized.*

The [binary prime-Lambert candidate](prime-lambert-disjunctivity-draft.md) extends directly to
\[
 G_\Omega=\sum_{n\ge1}\Omega(n)2^{-n}
 =\sum_p\sum_{a\ge1}\frac1{2^{p^a}-1},
\]
where \(\Omega\) counts prime factors with multiplicity.  The proof changes below preserve the same high-rank geometry and zonotope argument.  This remains an internally audited research argument with the binary two-point input, not an externally validated theorem or a completed formalization.

This conclusion is **not** transferred from little omega by sparse digit edits or by a zero-entropy correction.  Those do not generally preserve disjunctivity.  The earlier multiplicity-correction audit (internal research note) concerns entropy and normality preservation; the present argument instead controls \(\Omega\) directly.

## 1. Exact transport is simpler

Complete additivity gives
\[
 \Omega(dm)=\Omega(d)+\Omega(m).
\]
Thus, for \(\mathcal T_\Omega(k)=\sum_{j\ge1}2^{-j}\Omega(k+j)\),
\[
 \sum_{j\ge1}2^{-j}\Omega(n+\rho_{\alpha,j})
 =\mathcal T_\Omega(k_\alpha(n))+\Omega(d_\alpha).
\]
There is no periodic prime-overlap correction.  Also
\(\mathcal T_\Omega(k)-2^kG_\Omega\in\mathbb Z\).
The first \(K\) layers still cancel by the unchanged grid projections.

## 2. Freeze bad-prime valuations, not only divisibility

Let \(P_0\) be the modulus from the binary omega construction, and let \(T\) be the number of retained shifts.  Its prime divisors must have their full valuations fixed on the retained arguments.

For every \(p^e\Vert P_0\), choose the least positive integer \(h\) with \(p^h>T\).  Refine the existing residue modulo \(p^e\) to one modulo \(p^{e+h}\).

If a shift already has valuation below \(e\), every lift preserves it.  Otherwise write its argument on the existing class as \(p^e(c+t)\).  Exactly one lift \(t\bmod p^h\) would make its valuation at least \(e+h\).  At most \(T\) lifts are forbidden by all retained shifts together, and \(p^h>T\), so choose a lift avoiding them all.  Every retained valuation is then below \(e+h\) and fixed exactly.

Apply CRT over the different primes.  The refined modulus \(P\) has no new prime divisors and obeys
\[
 \log P
 \le2\log P_0+\omega(P_0)\log(T+1)
 =L^{7c+o(1)}=o(L).
 \tag{1}
\]
Indeed \(h\log p\le\log(T+1)+\log p\).  All refinements are made at the outer scale \(X\), before choosing the common good sample scale \(N\).  The two-point theorem still applies to this modulus.  The contributions of primes dividing \(P\), including all their powers, form one fixed vector on the progression.

## 3. Good small primes: truncate valuations and strip the whole phase

Use an even moment degree \(M\asymp C_1TL\), and now put
\[
 R=X^{1/(40M)},\qquad
 H_p=\left\lceil\frac{\log R}{\log p}\right\rceil
 \quad(p\le R,\ p\nmid P).
\]
Replace \(\nu_p(n+\rho)\) temporarily by
\(\min(\nu_p(n+\rho),H_p)\).  This is periodic modulo \(p^{H_p}\), and
\[
 R\le p^{H_p}\le R^2.
\]

For a joint Fourier vector, form its entire local phase
\[
 \sum_\rho c_\rho\min(\nu_p(n+\rho),H_p),
\]
and reduce that phase modulo one to a representative in \([-1/2,1/2]\).  This reduction preserves its exponential exactly.  It may depend on the prime and Fourier vector; only uniform period and size bounds are needed.

For every good prime, the retained shifts have distinct roots modulo \(p\) and \(p>2T\).  The local phase is zero outside those roots, with probability at least \(1/2\).  On the residue events with valuation exactly one, its phase is \(c_\rho\).  These events have probability \(1/p-1/p^2\) when \(H_p\ge2\); when \(H_p=1\), the entire corresponding root has that phase, with the larger probability \(1/p\).

The same circular-energy argument therefore gives local contraction
\[
 |\mathbb E e(X_p)|\le\exp(-cE_q/p),
\]
where \(E_q\ge2^{-K}/4\) is the binary coefficient-energy lower bound.  Also the centered local variable has magnitude at most one and variance at most \(T/(4p)\).  The model variance and Taylor budget remain \(O(TL)\).

A \(k\)-tuple of primes now has period at most \(R^{2k}\).  There are at most \(R^k\) ordered tuples, so the moment error is
\[
 O(PR^{3k}/N)
 \le X^{-0.425+o(1)}
 \quad(k\le M,\ N\ge\sqrt X).
 \tag{2}
\]
This suffices for the previous uniform Fourier-box argument.

### Removing the valuation truncation

The truncation changes an argument only when
\[
 p^{H_p+1}\mid n+\rho,\qquad p^{H_p+1}\ge Rp.
\]
The inequality is not always strict, but the weak form is enough.  Union-bounding exact progression counts over all retained shifts and good primes gives
\[
 \Pr(\text{any truncation changes})
 \ll T\left(\frac{\log\log R}{R}+\frac{PR}{N}\right).
 \tag{3}
\]
If a prime power exceeds \(3N\), its event is empty and can be omitted.  The remaining congruences each have probability at most their reciprocal plus \(O(P/N)\).

The bound (3) is negligible even after multiplication by the entire Jackson Fourier l1 budget \(\exp(O(rK))\), since \(\log R\) is much larger than \(rK\).  A phase expectation changes by at most twice this probability.  Therefore the same joint Fourier estimate holds for the actual, untruncated small-prime vector.

## 4. Rough multiplicities add only a negligible L1 correction

All cutoffs here concern the **underlying prime**, not the size of a prime power.  For an argument \(m\le3N\),
\[
 \Omega_{>R}(m)-\omega_{>R}(m)
 =\sum_{p>R}\sum_{\substack{a\ge2\\p^a\le3N}}1_{p^a\mid m}.
\]
All these primes are coprime to \(P\).  Direct progression counting yields
\[
 \mathbb E_{\rm AP}
 [\Omega_{>R}(n+\rho)-\omega_{>R}(n+\rho)]
 \ll \frac1R+\frac{P\log N}{\sqrt N}.
 \tag{4}
\]
For the main term, sum
\(\sum_{p>R}\sum_{a\ge2}p^{-a}\ll1/R\).
For the count errors, there are at most \(O(\sqrt N\log N)\) eligible prime powers, each costing \(O(P/N)\).

Each signed row has coefficient l1 mass at most one.  Hence (4) also bounds its expected absolute multiplicity-correction error.  It is \(o(\eta)\).  The distinct-prime rough block is controlled by the original medium-prime CRT estimate and the same common-scale very-large-prime covariance theorem.  No new joint L2 estimate is assumed.

## 5. Progression means and the genuinely infinite tail

For \(p\nmid P\), summing the prime-power counting estimates gives the usual \(O(L)\) contribution to the mean of \(\Omega(n+\rho)\), with error
\[
 O\!\left(\frac P{\log N}
          +\frac{P\log N}{\sqrt N}\right)=o(1).
\]

For \(p^e\Vert P\), either the valuation is fixed below \(e\), or the argument is always divisible by \(p^e\).  In the latter case, for \(a>e\) its additional divisibility probability is at most
\[
 p^{-(a-e)}+O(P/N).
\]
Summing over possible powers and over primes dividing \(P\) bounds this contribution by
\[
 \Omega(P)+\sum_{p\mid P}\frac1{p-1}
 +O\!\left(\frac{P\,\omega(P)\log N}{N}\right)
 =o(L)+O(\log L).
\]
Here \(\Omega(P)\le\log P/\log2=o(L)\), and (1) makes the count error negligible.  Thus
\[
 \mathbb E_{\rm AP}\Omega(n+\rho)\ll L
\]
uniformly for the finite range of arguments at most \(3N\) used by the original far-tail split.  Beyond that range, \(\Omega(m)\le\log m/\log2\) gives the identical pointwise geometric-tail estimate.

## 6. Conclusion and scope

The exact orbit transport, the rough L1 localization, and the uniform actual small-prime Fourier estimates therefore fit the unchanged zonotope/Jackson contradiction.  The candidate conclusion is binary disjunctivity of \(G_\Omega\).

The argument does not rely on the difference between \(G_\Omega\) and \(G_\omega\) having sparse digits or zero entropy.  It does not establish normality.  All stated inequalities were checked directly; the only correction to the proposed extension was replacing \(p^{H_p+1}>Rp\) by the valid weak inequality \(p^{H_p+1}\ge Rp\).
