# A candidate disjunctivity proof for the prime Lambert number

*AI-assisted research draft by Ren (OpenAI Codex), with internal model audits.  Not externally validated or fully formalized.*

## Status and statement

**Research draft, 2026-09-14.**  This assembles a candidate proof that

\[
G_\omega=\sum_{n\ge1}\omega(n)2^{-n}
=\sum_{p\text{ prime}}\frac1{2^p-1}
\]

is binary disjunctive: every finite binary word occurs in its binary expansion.  Here \(\omega(n)\) counts distinct prime divisors, with \(\omega(1)=0\).  The series identity follows by absolutely convergent rearrangement.  No digit-frequency assertion or normality conclusion is made.

The argument below uses an external quantitative two-point correlation theorem.  It is **not** the earlier candidate elementary proof of irrationality, and it does not eliminate that deep input.  Internal independent audits have checked the geometric, Fourier, transport, and parameter components; this document is an assembly for further adversarial checking, not an externally validated theorem or a completed Lean proof.  Historical novelty has not been investigated.

Write \(e(t)=\exp(2\pi i t)\), \(\mathbb T=\mathbb R/\mathbb Z\), and use natural logarithms except where a base is displayed.  Constants may depend on one fixed omitted word, but not on the outer parameter \(X\).

## 1. What replaces the failed single-tail extractor

Companion results: the [fixed-base extension](prime-lambert-disjunctivity-fixed-base.md) removes the deep correlation input for every fixed base at least three, including an elementary candidate binary-disjunctivity proof for the base-four prime Lambert number.  The [affine-entropy follow-up](prime-lambert-affine-entropy-draft.md) gives quantitative entropy and word frequencies on the structured sparse samples, while identifying the remaining ordinary-normality gap.

A scalar signed combination can fill the circle even if every original radix tail avoids an interval.  The proposed replacement retains almost as many independent difference coordinates as input coordinates.  Its image of a missing-word set occupies very little volume at a usable resolution.

The arithmetic rough error is small in **average coordinate distance**, not simultaneously in every coordinate.  The covering estimate and smoothing test use precisely that metric.  The small-prime calculation controls all Fourier characters needed by that one test; it does not assume independence between the actual small and rough prime factors.

## 2. Fixed parameters and a separated grid

Let \(X\to\infty\), and fix

\[
L=\log\log X,\qquad c=1/100,\qquad a=1/4,
\]
\[
K=\left\lfloor c\frac{\log L}{\log\log L}\right\rfloor,
\quad s=K^2,\quad H=(s+1)^K,\quad r=s^K,
\]
\[
J=\lceil3\log_2L\rceil,\qquad \eta=2^{-aK},\qquad T=H(J-K).
\tag{2.1}
\]

All statements concern sufficiently large \(X\), so \(1\le K<J\).  Let \(D_s\) be the \(s\times(s+1)\) adjacent-difference matrix, and let

\[
\mathcal A=D_s^{\otimes K}\in\mathbb Z^{r\times H}.
\]

Columns are indexed by \(\alpha\in\{0,\ldots,s\}^K\).  Each row has \(2^K\) entries in \(\{-1,1\}\), and all its coordinate-fiber sums vanish.  The matrix has full row rank.  Each column meets at most \(2^K\) rows.

Choose an integer base \(B>2sJ+1\), of size \(O(sJ)\), and put

\[
u_\alpha=\sum_{i=1}^K\alpha_i B^i,
\qquad v_\alpha=\sum_{i=1}^K i\alpha_i B^i.
\tag{2.2}
\]

The \(u_\alpha\) are distinct.  For \(1\le j\le K\), the projection
\(ju_\alpha-v_\alpha=\sum_i(j-i)\alpha_i B^i\) ignores coordinate \(j\), so each row cancels that projection.  For \(K<j\le J\), the same projection is injective.  Indeed, a collision would be a vanishing base-\(B\) expansion with coefficients of absolute value at most \(sJ<B/2\); the highest nonzero coefficient dominates all lower ones.

Set \(U=\max u_\alpha\), \(V=\max v_\alpha\), \(D_0=U+V+1\), and

\[
Q=\operatorname{lcm}(1,\ldots,\max(J+1,2U,2V)),
\]
\[
d_\alpha=1+Q(D_0+u_\alpha),\qquad
t_\alpha=Qv_\alpha,\qquad
\rho_{\alpha,j}=jd_\alpha-t_\alpha.
\tag{2.3}
\]

The \(d_\alpha\) are distinct positive pairwise coprime integers.  To see coprimality, a common prime divisor of \(d_\alpha,d_\beta\) divides \(Q(u_\alpha-u_\beta)\); it cannot divide \(Q\), since each \(d\equiv1\pmod Q\).  But every prime dividing the nonzero difference \(u_\alpha-u_\beta\) divides \(Q\), a contradiction.

All \(\rho_{\alpha,j}>0\).  For fixed \(j\), their coincidences are exactly those of \(ju-v\).  For different \(1\le j\le J\), they cannot coincide, since \(\rho_{\alpha,j}\equiv j\pmod Q\) and \(Q>J\).  Thus the \(T\) surviving shifts \(\rho_{\alpha,j}\), \(K<j\le J\), are globally distinct.

## 3. One compatible progression and its height

First impose \(n\equiv t_\alpha\pmod{d_\alpha\operatorname{rad}(d_\alpha)}\) for every \(\alpha\).  The moduli are pairwise coprime, so these conditions are compatible.  Then

\[
k_\alpha(n)=\frac{n-t_\alpha}{d_\alpha}\in\mathbb Z,
\qquad k_\alpha(n)\equiv0\pmod{\operatorname{rad}(d_\alpha)}.
\tag{3.1}
\]

Enlarge this modulus to include every prime at most \(2T\), and every prime dividing a nonzero difference between two surviving shifts.  Choose arbitrary compatible residues for newly added primes.  Call the resulting modulus \(P\) and residue \(b\), chosen with \(0\le b<P\).  Every prime dividing \(P\) has its divisibility indicators frozen throughout the progression, for every fixed shift.

The following deliberately loose bounds suffice:

\[
H,r,T=L^{2c+o(1)},\quad U,V=L^{3c+o(1)},
\quad \log Q,\log d_{\max},\log\rho_{\max}=L^{3c+o(1)},
\]
\[
\boxed{\log P\le L^{7c+o(1)}=o(L).}
\tag{3.2}
\]

For the last bound, the multiplier part costs at most \(2H\log d_{\max}\); the primorial through \(2T\) costs \(O(T)\); the product of all shift differences costs at most \(O(T^2\log\rho_{\max})\).  This proves (3.2), using the elementary bound \(\log\operatorname{lcm}(1,\ldots,z)=O(z)\).  In particular,

\[
P,d_{\max},\rho_{\max}=(\log X)^{o(1)}.
\tag{3.3}
\]

Every prime dividing \(P\) is at most \(P\).  Omitting these primes from a harmonic prime sum loses at most \(O(\log\log(P+3))=O(\log L)=o(L)\).

Everything so far is fixed at \(X\), **before** choosing the common sample scale \(N\in[\sqrt X,X]\).

## 4. Exact transport to radix tails

Define

\[
\mathcal T(k)=\sum_{j\ge1}2^{-j}\omega(k+j).
\]

For every nonnegative integer \(k\), \(\mathcal T(k)-2^kG_\omega\in\mathbb Z\).  Also

\[
\omega(dm)=\omega(m)+\omega(d)
-\sum_{p\mid d}1_{p\mid m}.
\]

Consequently, on the progression (3.1),

\[
\sum_{j\ge1}2^{-j}\omega(n+\rho_{\alpha,j})
=\mathcal T(k_\alpha(n))+\omega(d_\alpha)-E_\alpha,
\tag{4.1}
\]

where \(E_\alpha=\sum_{p\mid d_\alpha}\sum_{j\ge1}2^{-j}1_{p\mid k_\alpha(n)+j}\) is independent of \(n\), because \(k_\alpha(n)\bmod\operatorname{rad}(d_\alpha)\) is fixed.  All \(k_\alpha(n)\) are positive for our large sample intervals.

Let \(x_\alpha(n)=\{2^{k_\alpha(n)}G_\omega\}\), and form the \(r\)-vector

\[
F_\nu(n)=\sum_\alpha\mathcal A_{\nu\alpha}
                   \sum_{j>K}2^{-j}\omega(n+\rho_{\alpha,j}).
\tag{4.2}
\]

The terms \(j\le K\) cancel exactly by (2.2)-(2.3).  Thus, modulo \(\mathbb Z^r\),

\[
\mathbf F(n)=\mathcal A\mathbf x(n)+\theta
\tag{4.3}
\]

for one fixed \(\theta\in\mathbb T^r\).

If the binary expansion of \(G_\omega\) omits a word, the doubling orbit closure \(C\) avoids an open interval.  Choose a closed dyadic interval strictly inside that interval, and forbid its finite binary word.  Every point of \(C\) has a binary representation avoiding that word at all positions.  Aligned-block counting at its length \(m\) bounds the number of length-\(n\) cylinders by \(O((2^m-1)^{n/m})\).  Therefore \(C\) has upper box dimension at most

\[
d=\frac{\log(2^m-1)}{m\log2}<1.
\tag{4.4}
\]

The strictly interior cylinder avoids binary endpoint ambiguity.  Under this hypothesis (4.3) lies in the fixed translate \(\mathcal A(C^H)+\theta\) for every sample point.

## 5. The high-rank image has a small average-distance tube

For \(y,z\in\mathbb T^r\), write

\[
d_{\rm av}(y,z)=\frac1r\sum_{\nu=1}^r\operatorname{dist}_{\mathbb T}(y_\nu,z_\nu).
\]

Fix \(d<d'<1\).  For a sufficiently small fixed \(\varepsilon>0\),

\[
\operatorname{Haar}\{y:d_{\rm av}(y,\mathcal A(C^H))\le\varepsilon\eta\}=o(1).
\tag{5.1}
\]

Here are the details which prevent a spurious \(2^K\) covering loss.  The eigenvalues of \(D_sD_s^T\) are
\(\lambda_j=4\sin^2(\pi j/(2(s+1)))\).  Their uniform logarithmic mean is \(\log(s+1)/s\), and their logarithmic variance is bounded independently of \(s\), by comparison with the integral of \((\log x)^2\) on \((0,1]\).  Tensoring and applying Cauchy-Schwarz to the sum of logarithms give

\[
\log\det(I_r+\mathcal A\mathcal A^T)=O(r\sqrt K).
\tag{5.2}
\]

Every principal submatrix has determinant of \(I+\mathcal A_G\mathcal A_G^T\) bounded by this determinant, as follows by expanding in nonnegative principal minors.

For any \(g\)-row subset \(G\), the image of an input box of side \(\eta\), thickened by \(\eta\) in the selected output coordinates, is contained in a translate of the zonotope
\(\eta[\mathcal A_G,I_g][-1,1]^{H+g}\).  The zonotope volume formula, followed by Cauchy-Schwarz and Cauchy-Binet, bounds its volume by

\[
(2\eta)^g\sqrt{\binom{H+g}{g}
 \det(I_g+\mathcal A_G\mathcal A_G^T)}
\le\eta^g\exp(O(H+r\sqrt K)).
\tag{5.3}
\]

The volume formula is the sum of absolute determinants of the parallelepipeds generated by all \(g\)-subsets of generators; it also follows by adding the generating segments successively.  Projection to the torus only folds overlapping copies, so cannot increase this upper bound.

Cover \(C^H\) with at most \(C_0^H\eta^{-d'H}\) such input boxes.  A point within average distance \(\varepsilon\eta\) of an image point is within \(\eta\) in at least \((1-\varepsilon)r\) coordinates.  Union over at most \(2^r\) row subsets.  The resulting volume is at most

\[
\eta^{(1-\varepsilon)r-d'H}\exp(O(H+r\sqrt K)).
\tag{5.4}
\]

Since \(r/H=(s/(s+1))^K\to1\), choose \(0<\varepsilon<(1-d')/2\).  The logarithm of (5.4) is \(-\Omega(KH)+O(H+r\sqrt K)\to-\infty\).  This proves (5.1).  Notice that it works for **every** \(d'<1\), not just a fixed dimension below one third.

## 6. A common scale for signed rough-prime localization

We use the equidistributed case of [Tao and Teräväinen, Theorem 3.1](https://arxiv.org/html/2512.01739v2).  Its quantitative conclusion permits progression moduli and distinct shifts bounded by a fixed power of its logarithmic parameter, outside an exceptional set of scales with a power-saving logarithmic measure bound.  Functions may be fixed separately at each outer \(X\).  The following application records the needed uniformity; qualitative fixed-function correlation is not sufficient.

Set \(Y=X^{1/100}\), \(\mathcal L=(\log X)^{1/4}\), and let \(\kappa>0\) be the theorem's saving exponent.  Choose \(\beta=\kappa/40\) and \(B_*=\lfloor(\log X)^\beta\rfloor\).  Partition the primes in \((Y,3X]\) into \(B_*\) bins each with harmonic mass \(O(B_*^{-1})\).  For each bin let \(g_\ell\) indicate avoidance of its prime factors.  It is real-valued, 1-bounded, and multiplicative.

For every \(X^{0.4}\le N\le X\), finite divisor inclusion-exclusion and the standard upper-bound sieve give

\[
\sum_{\substack{N<n\le2N\\n\equiv a\ (q)}}g_\ell(n)
=\frac Nq\delta_{\ell,N}+O(N/\log X)
\quad(q\le\mathcal L),
\tag{6.1}
\]

uniformly in the bin and residue, including nonprimitive residues.  Indeed, inclusion-exclusion runs over squarefree bin-prime products \(d\le2N\), all coprime to \(q<Y\).  There are \(O(N/\log X)\) such products, since they are \(Y\)-rough, and each progression count has error \(O(1)\).  Take \(\delta_{\ell,N}\) to be the resulting truncated sum of \(\mu(d)/d\); (6.1) at \(q=1\) makes it uniformly bounded.  For \(q>\mathcal L\), the weaker required error \(O(N/\mathcal L)\) is trivial.  The theorem's specified small-prime interval lies below \(Y\), where \(g_\ell(p)=1\).  Thus its hypotheses hold uniformly.

Apply the theorem to every pair \((g_\ell,g_{\ell'})\), and to \((g_\ell,1)\).  The union of exceptional sets has normalized logarithmic measure
\(O(B_*^2\mathcal L^{-\kappa})=o(1)\).  It cannot cover \([\sqrt X,X]\).  Choose one **real** \(N\) outside the union.  By (3.3), the theorem simultaneously covers our modulus \(P\), residue \(b\), and every pair of distinct surviving shifts.  Normalize expectations over the integers \(n\in(N,2N]\), \(n\equiv b\pmod P\); replacing the theorem's normalization by their exact count costs \(O(P/N)\).

For any such shift \(\rho\), put \(W_\rho(n)=\omega_{>Y}(n+\rho)\).  Replacing a bin count by \(1-g_\ell\) fails only when two distinct primes from that bin divide the argument.  Over integers in \([1,3N]\), its probability is \(O(B_*^{-2})\), by \(\lfloor3N/(pq)\rfloor\le3N/(pq)\).  Restriction to our progression costs at most \(O(P)\).  Summing bins gives \(O(P/B_*)\).  All the counts are bounded by an absolute constant because every counted prime exceeds \(X^{1/100}\) and the argument is at most \(3X\).

Center \(\sum_\ell(1-g_\ell)\) by \(\mu_N=\sum_\ell(1-\delta_{\ell,N})\).  This center is uniformly bounded: (6.1) compares it to a bounded count with error \(O(B_*/\log X)\).  Expanding the product of two centered bin sums, and using the common two-point and mean estimates, proves

\[
\mathbb E(W_\rho-\mu_N)^2\ll1,
\qquad
|\mathbb E(W_\rho-\mu_N)(W_{\rho'}-\mu_N)|
\le\exp(-\beta L+o(L))\quad(\rho\ne\rho').
\tag{6.2}
\]

No assertion about the covariance at every scale is needed.  Every subsequent estimate is on this same chosen scale.

Now take an even integer \(M\asymp C_1TL\), with a sufficiently large absolute \(C_1\), and set

\[
R=X^{1/(20M)}.
\tag{6.3}
\]

For large \(X\), all primes dividing \(P\) and all shift differences lie below \(R<Y\).  For the medium primes \(R<p\le Y\), ordinary two-congruence counting on the progression gives, for a signed row with coefficients \(c_{\alpha,j}=\mathcal A_{\nu\alpha}2^{-j}\),

\[
\mathbb E\left|\sum_{\alpha,K<j\le J}c_{\alpha,j}
                  \omega_{(R,Y]}(n+\rho_{\alpha,j})\right|^2
\ll 2^{-K}\log M+X^{-0.4}.
\tag{6.4}
\]

Here \(\sum c=0\), \(\sum|c|\le1\), and \(\sum c^2\le2^{-K}/3\).  The diagonal prime sum is \(O(\log M)\); distinct-prime errors cost \(O(PY^2/N)=X^{-0.48+o(1)}\); same-prime distinct shifts are mutually exclusive.  Formula (6.2) gives the corresponding very-large-prime bound \(O(2^{-K})+\exp(-\beta L+o(L))\).  Its common center cancels because \(\sum c=0\).

Thus the rough part \(\mathbf E\) in each row satisfies

\[
\mathbb E|E_\nu|^2
\ll2^{-K}\log M+\exp(-\beta L+o(L)).
\tag{6.5}
\]

There is no required joint independence of these errors.

## 7. The genuinely infinite tail is harmless on average

Let \(J_+=\lceil3\log_2\log X\rceil\).  For \(j\le J_+\), every argument \(n+\rho_{\alpha,j}\le3N\) for large \(X\).  Direct counting on the progression gives

\[
\mathbb E\omega(n+\rho_{\alpha,j})
\le\omega(P)+\sum_{p\le3N}\frac1p
     +O(P\pi(3N)/N)\ll L.
\tag{7.1}
\]

For \(j>J_+\), use \(\omega(n+\rho_{\alpha,j})\ll\log X+\log(j+1)+\log d_{\max}\).  Therefore each row's omitted tail \(Z_\nu\), at positions \(j>J\), has

\[
\mathbb E|Z_\nu|
\ll2^K\bigl(L2^{-J}+(\log X)2^{-J_+}\bigr)
\ll2^KL^{-2}+2^Ke^{-2L}.
\tag{7.2}
\]

Let \(\mathbf S(n)\) be the vector of retained contributions from primes \(p\le R\) not dividing \(P\).  The primes dividing \(P\) give a fixed vector \(\gamma\).  Equations (4.2), (6.5), and (7.2) yield

\[
\mathbf F=\mathbf S+\gamma+\mathbf E+\mathbf Z,
\]
\[
\mathbb E\,d_{\rm av}(\mathbf S,
                  \mathcal A(C^H)+\theta-\gamma)
\ll\sqrt{2^{-K}\log M}+\exp(-\beta L/2+o(L))+2^KL^{-2}
=o(\eta).
\tag{7.3}
\]

Average the coordinate distances first; Cauchy-Schwarz is then applied separately in each coordinate.  This is why no factor \(r\) appears.  The last equality uses \(a<1/2\), \(K\gg\log\log L\), and \(K=o(\log L)\).

## 8. All needed small-prime Fourier modes oscillate

Fix a sufficiently large constant \(C_2\), depending only on \(\varepsilon\), and let \(D=\lceil C_2\eta^{-1}\rceil\).  Uniformly for nonzero \(q\in\mathbb Z^r\) with \(\|q\|_\infty\le D\), we claim

\[
|\mathbb E e(q\cdot\mathbf S)|
\le \exp(-c_2L2^{-K})+\exp(-c_3TL)+X^{-0.3}.
\tag{8.1}
\]

Put \(w=\mathcal A^Tq\).  It is nonzero since \(\mathcal A\) has full row rank, and \(|w_\alpha|\le2^KD\).  A nonzero array with all coordinate-fiber sums zero has support at least \(2^K\): induct on \(K\), with at least two nonzero slices, each satisfying all remaining cancellations.  In particular this applies to \(w\).

For every nonzero \(w_\alpha\), write \(v=v_2(w_\alpha)\).  The site
\(j_\alpha=K+v+1\) lies in \((K,J]\) for large \(X\), since \(v\le K+\log_2D\) and \(J/K\to\infty\).  At this site,

\[
\operatorname{dist}(w_\alpha2^{-j_\alpha},\mathbb Z)
\ge2^{-(K+1)}.
\]

The global shift distinctness therefore gives the uniform circular energy bound

\[
E_q=\sum_{\alpha,K<j\le J}
 \operatorname{dist}(w_\alpha2^{-j},\mathbb Z)^2
\ge 2^{-K}/4.
\tag{8.2}
\]

Replace every coefficient \(w_\alpha2^{-j}\) by its representative \(b_{\alpha,j}\in[-1/2,1/2]\).  Since divisibility indicators are integers, this leaves the exponential phase **exactly unchanged**.  For a prime \(p\le R\), \(p\nmid P\), the \(T\) roots modulo \(p\) are distinct and \(p>2T\).  Thus its local variable \(X_p\) is zero with probability at least \(1/2\), and takes the value \(b_{\alpha,j}\) on each corresponding root.  Comparing each phase with the mass at zero gives

\[
|\mathbb E_{\mathbb Z/p}e(X_p)|
\le\exp(-c_4E_q/p).
\tag{8.3}
\]

The harmonic mass of these good primes is \(L-O(\log M+\log L)=L-o(L)\).  Hence the independent residue model has characteristic magnitude at most \(\exp(-c_2L2^{-K})\).

It remains to transfer this bounded-degree assertion to actual integers, not to assume that all residues are independent.  Center \(X_p\) by its residue mean, obtaining \(\xi_p\) with \(|\xi_p|\le1\) and total independent variance at most \(CTL\).  For any fixed \(\lambda\), independence in the **comparison model only** gives

\[
\mathbb E_{\rm model}\exp(\lambda\sum_p\xi_p)
\le\exp(C_\lambda TL).
\tag{8.4}
\]

For every \(k\le M\), expand \((\sum_p\xi_p)^k\).  There are at most \(R^k\) ordered prime tuples.  Each product is bounded by one and periodic with period at most \(R^k\), coprime to \(P\).  On our progression its average differs from its CRT mean by \(O(PR^k/N)\).  Consequently the \(k\)-th moments differ by at most

\[
O(PR^{2k}/N)\le X^{-0.4+o(1)}.
\tag{8.5}
\]

For even \(M\), Taylor's remainder for \(e^{2\pi i z}\) is bounded by \((2\pi|z|)^M/M!\).  Choose \(\lambda=2\pi e\) in (8.4).  The elementary inequality \(u^M/M!\le e^u\) yields a model remainder at most \(2\exp(C_\lambda TL-M)\).  Its actual expectation differs by the \(M\)-th-moment error multiplied by \((2\pi)^M/M!\), because \(M\) is even.  Choosing \(C_1\) large in (6.3) makes the remainder \(\exp(-c_3TL)\); the sum of Taylor-coefficient errors in (8.5) is negligible.  Deterministic centering changes only the phase of the mean.  This proves (8.1), uniformly in the whole Fourier box.

## 9. One separating test gives the contradiction

Let \(E=\mathcal A(C^H)+\theta-\gamma\), and define

\[
f(y)=\min\left(1,\frac{d_{\rm av}(y,E)}{\varepsilon\eta}\right).
\tag{9.1}
\]

Equation (7.3) gives \(\mathbb E f(\mathbf S)=o(1)\), whereas (5.1) gives \(\int f\,d\mathrm{Haar}=1-o(1)\).

Convolve \(f\) with a product Jackson kernel of coordinate degree at most \(D\), obtaining a trigonometric polynomial \(f_D\).  The one-dimensional kernel can be taken as the normalized square of a Fejér kernel: it has first circle-distance moment \(O(D^{-1})\).  Its product therefore has expected **average** coordinate displacement \(O(D^{-1})\), with no dimension factor.  Since \(f\) has Lipschitz constant \((\varepsilon\eta)^{-1}\) in \(d_{\rm av}\), choosing \(C_2\) large gives

\[
\|f_D-f\|_\infty\le1/16.
\tag{9.2}
\]

The kernel is positive and normalized, so each Fourier coefficient has magnitude at most one.  Its full Fourier l1 cost is at most

\[
(2D+1)^r=\exp(O(rK)).
\]

But \(rK=L^{2c+o(1)}\), while \(L2^{-K}=L^{1-o(1)}\).  Multiplying the uniform bound (8.1) by this cost still gives \(o(1)\).  Thus

\[
\mathbb E f_D(\mathbf S)=\int f_D\,d\mathrm{Haar}+o(1).
\tag{9.3}
\]

Convolution preserves the Haar integral.  Equations (9.2)-(9.3) force \(\mathbb E f(\mathbf S)\ge7/8-o(1)\), contradicting its \(o(1)\) upper bound.  The assumed missing word is impossible.

**Candidate conclusion:** the doubling orbit of \(G_\omega\) is dense, hence \(G_\omega\) is binary disjunctive.

## 10. Scope, audit dependencies, and what remains beyond this statement

The proof is an asymptotic existence argument, with no useful digit-position bound supplied.  It does not prove positive frequency, let alone the required frequency \(2^{-m}\), for a length-\(m\) word.  A dense orbit can have strongly biased frequencies.

The external input in Section 6 is essential to this assembly.  The older alternative irrationality draft had a different objective and an elementary route; that distinction must remain visible in any report.

Internal component and assembly audit records are retained in the project's research log.  This paper draft is not a Lean theorem.  The current Lean additions formalize selected earlier arithmetic and dyadic-energy lemmas, not Sections 5-9 of this argument.  A subsequent audit that discovers a gap should identify the exact numbered assertion, preserve the counterexample or missing hypothesis, and revise the candidate's status rather than silently replacing its proof.
