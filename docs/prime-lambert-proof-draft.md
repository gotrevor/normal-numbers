# Prime Lambert irrationality: complete candidate proof draft

This is the assembled compressed-cancellation argument, recorded on 2026-09-14.  It is a paper proof draft surviving internal audits, not an externally validated or completely formalized proof.  See [formalization status](prime-lambert-irrationality.md) for the exact Lean boundary.  Irrationality of the target is already known; no historical novelty claim is made.

The target is

\[
G=\sum_{n\ge1}\omega(n)2^{-n}=\sum_{p\text{ prime}}\frac1{2^p-1},
\]

where \(\omega(n)\) counts distinct prime factors.  Sections retain their original numbering for correspondence with the Lean modules.  The exact transport and cancellation identities, Taylor transfer, and several tail estimates are formalized.  Construction of the complete analytic chain remains open in Lean.

Products of directional differences are an existing construction in discrete tomography.[^tomography]  The proposed use here is the arithmetic compatibility and asymptotic ledger below.


All logarithms below are natural unless a base is displayed.  Write \(e(x)=\exp(2\pi i x)\), and let \(\operatorname{rad}(d)\) denote the product of the distinct prime factors of \(d\).

## 2. Exact six-for-three geometry

Represent an affine tail shift by a point \((u,s)\), with projection \(\ell_j(u,s)=ju-s\).  For three positions \(i<j<k\), set

\[
v_i=k-j,\quad v_j=i-k,\quad v_k=j-i,
\qquad g_h=(v_h,hv_h).
\]

Then \(g_i+g_j+g_k=0\).  In the signed convolution

\[
(\delta_0-\delta_{g_i})*
(\delta_0-\delta_{g_j})*
(\delta_0-\delta_{g_k}),
\]

the empty and full subsets coincide and cancel.  The remaining six atoms are \(g_i,g_j,g_k\), each of coefficient \(-1\), and their negatives, each of coefficient \(+1\).  Projection at each of \(i,j,k\) vanishes identically because the corresponding convolution factor has zero projection.

For \(K\) divisible by six, partition its positions into triples

\[
(6a+1,6a+2,6a+4),\qquad
(6a+3,6a+5,6a+6).
\]

Each triple has six distinct first coordinates \(\{\pm1,\pm2,\pm3\}\).  Scale successive triples by powers of an integer \(B>12J\), where \(J>K\) is the eventual tail cutoff, and convolve.  Balanced-base uniqueness gives \(H=6^{K/3}\) distinct first coordinates, all coefficients \(w_\alpha=\pm1\), and

\[
\sum_\alpha w_\alpha\,\delta_{j u_\alpha-s_\alpha}=0
\qquad(1\le j\le K).
\tag{1}
\]

For uniqueness, a highest differing base-\(B\) digit has magnitude at least \(B^a\), while lower digit differences contribute at most \(6(B^a-1)/(B-1)\).  For projected digits through \(J\), the same argument applies with their difference bounded by \(6J\).

At \(j=K+1\), all \(H\) projected atoms are distinct.  For \(K<j\le J\), the only possible extra coincidence is at \(j=K+3\), from the final triple of the second type.  It has multiplicity two, with agreeing signs.  At that site the squared coefficient mass is \((5/3)H\); at every other surviving site it is \(H\).  These statements follow by solving the linear equalities between local projected atoms.  For the seed triple \((3,5,6)\), its extra collision is at \(j=9\), where the three direction projections are \(6,-12,6\).

The geometry audit (internal research record) supplies additional algebra.  Exact tests in the carry instrument (internal research record) cover \(K=6,12\), the exceptional collision, the affine transform below, and an equally spaced negative control.  They corroborate the general proof; finite enumeration alone is not the proof.

## 3. Integer transport with manageable moduli

Put \(U=\max|u_\alpha|\), \(S=\max|s_\alpha|\).  Choose

\[
D=U+S+1,\qquad
Q=\operatorname{lcm}(1,\ldots,\max(J+1,2U,2S)),
\]

and define

\[
d_\alpha=1+Q(D+u_\alpha),\qquad s'_\alpha=Qs_\alpha,
\qquad r_{\alpha,j}=j d_\alpha-s'_\alpha.
\tag{2}
\]

The \(d_\alpha\) are positive, distinct, and pairwise coprime.  A common prime divisor of two would divide \(u_\alpha-u_\beta\), but every prime divisor of that nonzero difference divides \(Q\), whereas \(d_\alpha\equiv1\pmod Q\).

Also \(r_{\alpha,j}=j+Q(jD+j u_\alpha-s_\alpha)>0\).  This preserves (1).  Since \(r_{\alpha,j}\equiv j\pmod Q\) and \(Q>J\), distinct sites through \(J\) cannot collide.

The congruences \(n\equiv s'_\alpha\pmod{d_\alpha}\) are compatible.  On such a progression,

\[
k_\alpha=(n-s'_\alpha)/d_\alpha
\]

is an integer, positive for sufficiently large \(n\).  Extend each congruence to some residue modulo \(d_\alpha\operatorname{rad}(d_\alpha)\).  These moduli remain pairwise coprime, so this fixes every \(k_\alpha\bmod\operatorname{rad}(d_\alpha)\) simultaneously.

## 4. The exact \(\omega\)-transport correction is periodic

For every positive integer \(d\),

\[
\omega(d(k+j))
=\omega(k+j)+\omega(d)-\sum_{p\mid d}1_{p\mid k+j}.
\]

Let

\[
T(k)=\sum_{j\ge1}2^{-j}\omega(k+j),\qquad
E_d(k)=\sum_{p\mid d}\sum_{j\ge1}2^{-j}1_{p\mid k+j}.
\]

Then

\[
\sum_{j\ge1}2^{-j}\omega(d(k+j))
=T(k)+\omega(d)-E_d(k).
\tag{3}
\]

Crucially, \(E_d(k)\) is **exactly periodic** modulo \(\operatorname{rad}(d)\).  Section 3 freezes it completely, including its infinite tail.  We do not estimate it as small.

Combining (1)–(3),

\[
F_N(n):=
\sum_\alpha w_\alpha\sum_{j>K}2^{-j}\omega(n+r_{\alpha,j})
=\sum_\alpha w_\alpha T(k_\alpha)+C_N
\tag{4}
\]

on that progression, where \(C_N\) is constant there.  This is why the argument below works first with \(\omega\).  Freezing arbitrary \(\Omega\)-valuations requires an additional modulus ledger and is not imported silently.

## 5. The proposed oscillation theorem

For all sufficiently large \(N\), the construction gives a modulus \(A_N=N^{o(1)}\) and a residue \(a_N\) such that, for every fixed nonzero integer \(q\),

\[
\left|
\mathbb E_{\substack{N<n\le2N\\n\equiv a_N\pmod{A_N}}}
e\bigl(qF_N(n)\bigr)
\right|\longrightarrow0.
\tag{5}
\]

The configuration, modulus, and residue may depend on \(N\).  The expectation is normalized by the actual number of terms in the progression.  This is **not** the ordinary Fourier average of the radix orbit.

### 5.1 Parameter window

Set

\[
L=\log\log N,\quad t=\log L,\quad
K=6\left\lfloor\frac t5\right\rfloor,\quad H=6^{K/3},
\]

\[
J=\left\lceil2\log_2\log N\right\rceil,\quad
B=12J+1,\quad
M=2\left\lfloor\frac{L^{1/12}}2\right\rfloor,\quad
R=N^{1/(20M)}.
\tag{6}
\]

Consider \(N\) large enough that \(K,M\ge6\).  Rounding changes the subsequent powers by bounded factors.  Writing \(\kappa=(\log6)/3\),

\[
H=L^{(6/5)\kappa+o(1)},\qquad
H2^{-K}=L^{-(6/5)(\log2-\kappa)+o(1)}
       =L^{-0.11507\ldots+o(1)}.
\tag{7}
\]

The coordinates satisfy \(U,S\ll K B^{K/3}\).  Even the crude factorial bound for the lcm gives

\[
\log Q,\ \max_\alpha\log d_\alpha
\le \exp(O(t^2)).
\tag{8}
\]

There are at most \(HJ=\exp(O(t))\) finite shifts.  They are all \(N^{o(1)}\).

### 5.2 Freeze exactly the collision primes

Aggregate equal shifts in

\[
F_{N,J}(n)=
\sum_\alpha w_\alpha\sum_{K<j\le J}2^{-j}\omega(n+r_{\alpha,j})
=\sum_r c_r\omega(n+r).
\]

Let \(W\) be the product of all \(d_\alpha\) and all positive differences between distinct aggregated shifts.  Then

\[
\log W\le\exp(O(t^2))=o(\log N).
\tag{9}
\]

Let \(A_0=\prod_\alpha d_\alpha\operatorname{rad}(d_\alpha)\), with a residue chosen as in Section 3.  Extend it to a residue modulo

\[
A=\operatorname{lcm}(A_0,\operatorname{rad}(W)).
\]

Primes already dividing \(A_0\) already have their residue fixed; choose any residues at the other primes.  Thus extension is compatible, and \(A=N^{o(1)}\).

For every \(p\mid W\), all indicators \(1_{p\mid n+r}\) are fixed.  Their finite-tail contribution is a deterministic real number.  Its exponential has modulus one, so its magnitude need not be bounded.

At every other prime, distinct shifts are distinct modulo \(p\).  Freezing *all* primes below the largest shift would be a different, unnecessarily expensive construction; it is not being used.

The excluded harmonic mass satisfies

\[
\sum_{p\mid W}\frac1p=O(1+\log t)=o(L).
\tag{10}
\]

To see this, split at \(y=\max(3,\log W)\).  Primes at most \(y\) contribute \(O(1+\log\log y)\).  At most \(\log W/\log y\) prime divisors exceed \(y\), and their reciprocal sum is at most \(\log W/(y\log y)\).  Apply (9).

### 5.3 An independent small-prime model

For \(p\le R\), \(p\nmid W\), define on a uniform residue \(n\bmod p\)

\[
X_p(n)=\sum_r c_r1_{p\mid n+r}.
\]

At most one indicator is nonzero.  Signed mass is zero at every site, so

\[
\mathbb EX_p=0,\quad |X_p|\le2^{-K},\quad
\mathbb EX_p^2=\frac{\sigma^2}{p},
\qquad \sigma^2=\sum_r c_r^2.
\tag{11}
\]

The projection ledger and cross-site separation give

\[
H4^{-(K+1)}\le\sigma^2\le C H4^{-K}.
\tag{12}
\]

Let \(X'_p\) be independent variables with these marginal laws and put \(S'=\sum X'_p\).  Its variance is

\[
V=\sigma^2\sum_{\substack{p\le R\\p\nmid W}}\frac1p
\asymp H4^{-K}L
=L^{v+o(1)},
\]

\[
v=1-\frac65\left(\log4-\frac{\log6}{3}\right)
=0.05315\ldots>0.
\tag{13}
\]

The elementary prime harmonic estimate gives \(\log\log R=L-\log(20M)=L-O(t)\), and (10) removes only \(o(L)\).

For each fixed real \(\lambda\), mean zero and the vanishing bound on \(X'_p\) imply

\[
\mathbb E\exp(\lambda S')\le\exp(C_\lambda V).
\tag{14}
\]

For fixed \(q\ne0\),

\[
|\mathbb E e(qS')|\le\exp(-c_q V).
\tag{15}
\]

For (15), square each local characteristic function and apply \(1-\cos x\gg x^2\) to \(2\pi q(X'_p-\widetilde X'_p)\), with an independent copy \(\widetilde X'_p\).  This is valid uniformly because \(2^{-K}\to0\).  Multiply the local bounds.  For (14), use \(\exp(\lambda x)=1+\lambda x+O_\lambda(x^2)\) and multiply.

### 5.4 CRT compares enough moments

On the actual progression in \((N,2N]\), put

\[
S(n)=\sum_{\substack{p\le R\\p\nmid W}}X_p(n).
\]

Every good prime is coprime to \(A\).  For a tuple of \(k\le M\) primes, the product of its local variables is periodic with period at most \(R^k\).  On an arithmetic progression of length \(\asymp N/A\), comparison with the uniform residue average has error at most

\[
O\left(\frac{A R^k}{N}\right),
\]

because the product has absolute value at most one.  CRT identifies that uniform average with the corresponding independent-model expectation, **including repeated primes**.  Expanding the \(k\)-th power uses at most \(R^k\) ordered tuples.  Therefore

\[
|\mathbb ES^k-\mathbb E(S')^k|
\ll\frac{A R^{2k}}N
\le N^{-9/10+o(1)}
\qquad(1\le k\le M).
\tag{16}
\]

Only the displayed finite moments are compared, not the joint law of all primes.

Use the Taylor polynomial of degree \(M-1\) for \(\exp(2\pi iqx)\).  Since \(M\) is even, its mean remainder is bounded by

\[
\frac{|2\pi q|^M}{M!}\mathbb E S^M.
\]

Equation (16) compares this moment with the independent one.  Choose \(\lambda=e|2\pi q|\).  The inequality
\(|x|^M\le M!\lambda^{-M}e^{\lambda|x|}\), together with (14), bounds the independent mean remainder by

\[
2\exp(C_qV-M).
\tag{17}
\]

The actual mean remainder differs by at most \(N^{-9/10+o(1)}\).  The polynomial expectations also differ by that bound, using (16) and the bounded sum of the absolute Taylor coefficients.  Since \(v<1/12\),

\[
|\mathbb E e(qS)|
\le e^{-c_qV}+O_q(e^{C_qV-M})+N^{-9/10+o(1)}
=o(1).
\tag{18}
\]

This is the centered moment step that cannot be replaced by a crude absolute first-moment bound.

### 5.5 Large primes are now cheap pointwise

Every finite-tail argument \(n+r\) lies between \(1\) and \(3N\), once \(N\) is large.  Such an integer has at most

\[
\frac{\log(3N)}{\log R}=O(M)
\]

distinct prime factors exceeding \(R\).  After separating the fixed bad-prime contribution, the omitted good large primes therefore contribute at most

\[
O(MH2^{-K})
=L^{1/12-0.11507\ldots+o(1)}
=L^{-0.03173\ldots+o(1)}
=o(1)
\tag{19}
\]

uniformly on the progression.  No shifted-prime correlation theorem is used here.

Finally, \(\omega(n+r_{\alpha,j})\ll\log N+\log j+\log d_\alpha\) gives

\[
|F_N-F_{N,J}|
\ll H2^{-J}(\log N+\log J+\max\log d_\alpha)
=o(1).
\tag{20}
\]

The leading term is \(O(H/\log N)\).  For fixed \(q\), the exponential is Lipschitz; (18)–(20), with the deterministic bad-prime phase, give (5).

## 6. Why this would reprove irrationality

Suppose \(G=a/q\) were rational, with positive integer \(q\).  For every nonnegative integer \(k\),

\[
T(k)=2^kG-\sum_{m=1}^k2^{k-m}\omega(m),
\]

so \(qT(k)\in\mathbb Z\).  Equation (4) makes \(e(qF_N(n))\) constant on the constructed progression, of modulus one.  Its normalized average would have modulus one for all sufficiently large \(N\), contradicting (5).

This would prove the already-known irrationality if the growing-family oscillation argument withstands review.  Its interest is the method: exact signed geometry makes a pointwise large-cofactor bound sufficient.  The external theorem is not used as a premise.

The independent analytic audit (internal research record) checked the parameter and CRT ledger, then separately checked the complete centered-moment argument in Section 5.4.  No gap was found in those checks.  The assembled argument remains a private research proof draft requiring fresh review, not an externally validated theorem or a historical novelty claim.

A further adversarial review of the assembled argument found no fatal flaw in its varying configuration, exact transport, modulus sizes, variance, or approximation errors.  Its useful summary of the parameter window is: for \(K\sim a\log L\), \(M\sim L^\beta\), require

\[
0<1-a(2\log2-\kappa)<\beta<a(\log2-\kappa).
\]

Our parameters give \(0<0.05315<0.08333<0.11507\).  More generally, for comparable geometry with \(H\approx\rho^K\), this particular irrationality window is nonempty whenever \(\rho<2\).  Compression below the binary cube's growth rate is exactly what opens the window.  This observation assumes the same height, coefficient, and variance controls; support growth alone does not imply them.


## Sources and scope

[^tt]: Terence Tao and Joni Teräväinen, [Quantitative correlations and some problems on prime factors of consecutive integers](https://arxiv.org/html/2512.01739v2), Theorem 1.3 and Section 5.  Their theorem proves irrationality of G using a quantitative correlation estimate.  It is not used as a premise here.

[^tomography]: Viviana Ghiglione, [Switching Components in Discrete Tomography: Characterization, Constructions, and Number-Theoretical Aspects](https://mediatum.ub.tum.de/doc/1453778/1453778.pdf), Chapter 3 and the introductory direction-dependent constructions.  This is prior art for compressed projection cancellation, not a claim about arbitrary prescribed carry directions.

This draft does not prove normality or disjunctivity.  See the [single-coordinate mass obstruction](prime-lambert-isolator-obstruction.md) for a proved paper obstruction to upgrading this argument by isolating one radix tail while retaining the same absolute-value estimate.
