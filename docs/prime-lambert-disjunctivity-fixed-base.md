# Fixed-base extension of the prime-Lambert disjunctivity candidate

*AI-assisted research draft by Ren (OpenAI Codex), with internal model audits.  Not externally validated or fully formalized.*

The [assembled binary candidate](prime-lambert-disjunctivity-draft.md) extends to the following family:

\[
 \boxed{\text{For each fixed integer }b\ge2,\quad
 G_b=\sum_{n\ge1}\omega(n)b^{-n}
     =\sum_p\frac1{b^p-1}
 \text{ is disjunctive in base }b.}
\]

For **\(b=2\)**, the present assembly uses the external quantitative two-point correlation theorem.  For **every fixed \(b\ge3\)**, Section 5 below removes that input: the very-large-prime contribution is pointwise small at the required resolution, and the remaining argument uses elementary prime estimates, CRT moments, linear algebra, and Fourier smoothing.

This is an audited extension of a research proof draft, not an externally validated theorem or a completed formalization.  It makes no digit-frequency or normality assertion.  **The number changes with the base:** it does not prove that one fixed constant, such as \(G_2\), is disjunctive in every base.

Fix \(b\) before sending the outer parameter \(X\) to infinity.  Constants may depend on this fixed base and the putative omitted word.  Keep all geometric and prime-splitting parameters from the binary draft, in particular
\[
 L=\log\log X,\quad K=\left\lfloor\frac{\log L}{100\log\log L}\right\rfloor,
 \quad s=K^2,\quad J=\lceil3\log_2L\rceil,\quad
 \eta=2^{-K/4}.
\]

## 1. Exact transport and row norms

Define \(\mathcal T_b(k)=\sum_{j\ge1}b^{-j}\omega(k+j)\).  Then
\(\mathcal T_b(k)-b^kG_b\in\mathbb Z\).  The transported identity becomes
\[
 \sum_{j\ge1}b^{-j}\omega(n+\rho_{\alpha,j})
 =\mathcal T_b(k_\alpha(n))
   +\frac{\omega(d_\alpha)}{b-1}
   -E_{\alpha,b},
\]
where
\[
 E_{\alpha,b}=\sum_{p\mid d_\alpha}\sum_{j\ge1}
 b^{-j}1_{p\mid k_\alpha(n)+j}
\]
is fixed on the same progression as before.  The composite-multiplier correction is still exact and periodic.  The first \(K\) layers cancel by the unchanged projection geometry.

For every tensor-difference row, the infinite surviving coefficients satisfy
\[
 \sum_{\alpha,j>K}|c_{\alpha,j}|
 =\frac{(2/b)^K}{b-1}\le1,
 \qquad
 \sum_{\alpha,j>K}c_{\alpha,j}^2
 =\frac{(2/b^2)^K}{b^2-1}.
 \tag{1}
\]
Their signed sum is zero.  Finite truncation only decreases these norm bounds.

## 2. Uniform circular energy without a valuation argument

The zonotope test has the same Fourier box
\(\|q\|_\infty\le D=O(\eta^{-1})\).
For \(q\ne0\), the integer array \(w=\mathcal A^\top q\) is nonzero, has at least \(2^K\) nonzero atoms, and obeys
\[
 |w_\alpha|\le2^K D.
\]
For each nonzero atom choose
\[
 t_\alpha=\lceil\log_b|w_\alpha|\rceil,\qquad
 j_\alpha=K+t_\alpha+1.
\]
The definition of the ceiling gives
\[
 b^{-K-2}<|w_\alpha|b^{-j_\alpha}\le b^{-K-1}.
\]
These values are below \(1/2\), so their distance to an integer is their absolute value.  Also
\[
 K<j_\alpha\le
 K+\frac{K\log2+\log D}{\log b}+2
 =O_b(K)<J.
\]
The globally distinct atom/site shifts therefore give
\[
 \sum_{\alpha,K<j\le J}
 \operatorname{dist}(w_\alpha b^{-j},\mathbb Z)^2
 \ge b^{-4}(2/b^2)^K.
 \tag{2}
\]
This argument works for composite \(b\) and either sign of \(w_\alpha\); no base-\(b\) valuation is assumed.

After reducing coefficients modulo one into \([-1/2,1/2]\), all local boundedness and moment estimates are unchanged.  The comparison model contracts by
\[
 \exp\!\left(-c_b L(2/b^2)^K\right).
\]
For each fixed \(b\),
\[
 L(2/b^2)^K=L^{1-o_b(1)}
 \gg rK=L^{2/100+o(1)}.
 \tag{3}
\]
Thus contraction beats the whole Jackson Fourier l1 budget.  The upper model variance remains \(O(TL)\), so the same even moment degree \(M\asymp TL\), cutoff \(R=X^{1/(20M)}\), and CRT error estimates apply.

## 3. The actual rough and infinite-tail errors still beat the resolution

Using the common-scale very-large-prime covariance estimate gives a uniform treatment of all \(b\ge2\): together with the medium-prime calculation and (1), it gives for each row
\[
 \|E_\nu\|_2
 \ll_b(\sqrt2/b)^K\sqrt{\log M}
       +\exp(-\beta L/2+o(L)).
\]
Dividing by the fixed resolution \(\eta=2^{-K/4}\) gives
\[
 \eta^{-1}\|E_\nu\|_2
 \ll_b(2^{3/4}/b)^K\sqrt{\log M}+o(1)
 =o(1).
 \tag{4}
\]
Indeed \(2^{3/4}/b<1\) for every \(b\ge2\), and
\(K\gg\log\log L\), while \(\log M=O(\log L)\).

The far-tail estimates are no worse than in base two: \(b^{-j}\le2^{-j}\).  The same average prime-count estimate and remote cutoff give an omitted-row mean
\[
 O(2^K L^{-2}+2^Ke^{-2L})=o(\eta).
\]
Averaging coordinate distances therefore supplies the same normalized-metric localization needed by the zonotope test.

## 4. Missing words and the unchanged contradiction

If \(G_b\) omits a base-\(b\) word, its multiplication-by-\(b\) orbit closure \(C_b\) avoids an open interval.  Choose a smaller closed \(b\)-adic cylinder strictly inside that interval.  If its word has length \(m\), aligned-block counting gives
\[
 \overline{\dim}_{\rm B}(C_b)
 \le\frac{\log(b^m-1)}{m\log b}<1.
\]
The zonotope argument depends only on this strict upper-box-dimension deficit and on the unchanged integer tensor matrix.  It does not depend on the radix.  Equations (2)–(4), the same Jackson approximation, and the exact transported orbit identity therefore give the same contradiction.

All comparisons here require **fixed \(b\)**.  No uniform conclusion for a base growing with \(X\), no absolute disjunctivity of one fixed number, and no normality statement is inferred.

## 5. For fixed \(b\ge3\), the two-point input is unnecessary

For this case take the sample scale \(N=X\) directly, on the same geometrically constructed progression.  No prime bins, exceptional sets, or two-point correlation theorem are needed.

Keep the split \(R=X^{1/(20M)}<Y=X^{1/100}\).  For a retained argument at most \(3X\), the number of prime factors exceeding \(Y\) is bounded by
\[
 \omega_{>Y}(n+\rho)\le\frac{\log(3X)}{\log Y}=O(1).
\]
Consequently (1) supplies the pointwise estimate
\[
 \left|\sum_{\alpha,K<j\le J}
 c_{\alpha,j}\omega_{>Y}(n+\rho_{\alpha,j})\right|
 \ll_b(2/b)^K.
\]
At the required spatial resolution,
\[
 \eta^{-1}
 \left|\sum_{\alpha,K<j\le J}
 c_{\alpha,j}\omega_{>Y}(n+\rho_{\alpha,j})\right|
 \ll_b(2^{5/4}/b)^K=o(1)
 \quad(b\ge3).
 \tag{5}
\]
The numerical threshold is \(b>2^{5/4}\), which every integer \(b\ge3\) satisfies.  For \(b=2\), this bound does not tend to zero, so it does not remove the binary two-point input.

The medium-prime error remains
\[
 O_b\!\left((\sqrt2/b)^K\sqrt{\log M}\right)
\]
in L2, by elementary two-congruence counting.  This beats \(\eta\) by (4).  The infinite tail is already controlled by its elementary progression mean.  The joint small-prime argument, uniform circular energy (2), and zonotope/Jackson test do not use the two-point theorem at all.

Thus all analytic pieces of the base-\(b\) candidate close without that external correlation input when \(b\ge3\).  This is not the stronger and false claim that the pointwise estimate handles *all* primes above \(R\): the intermediate range \(R<p\le Y\) must still be treated in L2.
