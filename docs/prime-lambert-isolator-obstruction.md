# A universal mass obstruction for a single-coordinate carry isolator

Status: complete internally audited paper proof, not yet formalized in Lean.  Recorded on 2026-09-14; no historical novelty claim.  The arithmetic estimate being tested is in the [candidate irrationality proof](prime-lambert-proof-draft.md), Section 5.5.

The coordinate-isolation route from the carry-cancellation investigation cannot use the current pointwise absolute large-prime estimate.  **Every compatible integer single-coordinate isolator canceling the first \(K\) places has mass at least \(2^K\).**  This holds for any nonzero isolated coefficient, with no restriction on its odd part or on multiplier height.

The stronger statement below survives aggregation of all equal integer arguments and removal of integer coefficients invisible to the exponential.  It is an obstruction to this absolute-value estimate, not a proof that disjunctivity is impossible or that the actual signed arithmetic tail is large.

The main audit derived the generating-function argument; the independent algebra audit checked convergence, CRT recentering, polynomial division, negative coefficients, and coefficient stripping.

## 1. Polynomial hypotheses

Let \(K\ge1\).  For a finite set of positive integer multipliers \(d\), let

\[
 W_d(t)=\sum_{h\ge0}w_{d,h}t^h\in\mathbb Z[t].
\]

Assume the exact projection identities

\[
 \sum_d z^{dj}W_d(z^d)=0
 \quad\text{in }\mathbb Z[z],
 \qquad 1\le j\le K.
 \tag{1}
\]

Assume there is exactly one multiplier \(d_*\) with nonzero effective radix coefficient:

\[
 W_{d_*}(2)=C\in\mathbb Z\setminus\{0\},
 \qquad W_d(2)=0\quad(d\ne d_*).
 \tag{2}
\]

Write

\[
 H_1=\sum_{d,h}|w_{d,h}|.
\]

Then

\[
 \boxed{H_1\ge2^K.}
 \tag{3}
\]

Here \(H_1\) denotes coefficient mass, not support cardinality.  If identical atoms were listed separately, first combine their weights; the original uncombined mass is at least the resulting mass.

## 2. The absolutely convergent generating function

Define

\[
 R(z)=\sum_d W_d(z^d)\frac{z^d}{2-z^d}
     =\sum_{j\ge1}2^{-j}\sum_d z^{dj}W_d(z^d).
 \tag{4}
\]

The coefficient sequence is absolutely summable.  Indeed, each finite polynomial has finite coefficient mass, and each geometric series in (4) has coefficient mass \(\sum_{j\ge1}2^{-j}=1\).  Thus all coefficient regroupings below are justified in the Banach algebra of absolutely summable power series.  Equivalently, every individual rational term has radius of convergence \(2^{1/d}>1\).

By (1), the first \(K\) summands in the second representation vanish identically.  Writing \(\|\cdot\|_{\mathrm{coef},1}\) for coefficient mass,

\[
 \|R\|_{\mathrm{coef},1}
 \le H_1\sum_{j>K}2^{-j}
 =H_1\,2^{-K}.
 \tag{5}
\]

The coefficients of \(R\) already combine all collisions between different multipliers, shifts, and tail sites.

## 3. Isolation forces at least one unit of aggregate coefficient mass

Division by the monic polynomial \(t-2\) takes place over \(\mathbb Z[t]\):

\[
 W_d(t)=(t-2)V_d(t)+W_d(2),
 \qquad V_d(t)\in\mathbb Z[t].
\]

Substitution in (4), using (2), yields

\[
 R(z)=P(z)+C\frac{z^{d_*}}{2-z^{d_*}},
 \qquad
 P(z)=-\sum_d z^dV_d(z^d)\in\mathbb Z[z].
 \tag{6}
\]

Since (1) evaluated at \(z=1\) gives \(\sum_dW_d(1)=0\), the absolutely convergent coefficient sum of \(R\) is

\[
 R(1)=\sum_dW_d(1)=0.
 \tag{7}
\]

Write \(C=\pm2^v m\), where \(v\ge0\) and \(m\) is a positive odd integer.  At exponent \(r=d_*(v+1)\), the geometric term in (6) has coefficient

\[
 \frac{C}{2^{v+1}}=\pm\frac m2.
\]

Adding an integer coefficient of \(P\) leaves a half-integer.  Therefore some coefficient of \(R\) has absolute value at least \(1/2\).  An absolutely summable real sequence with total sum zero has equal positive and negative masses, so its total mass is at least twice the absolute value of any single coefficient.  Hence

\[
 \|R\|_{\mathrm{coef},1}\ge1.
 \tag{8}
\]

Combining (5) and (8) proves (3).  The sign of \(C\) makes no difference.

## 4. Integer coefficient stripping does not evade the bound

Let

\[
 \|x\|_{\mathbb R/\mathbb Z}=\operatorname{dist}(x,\mathbb Z).
\]

Even after replacing every aggregate coefficient by its smallest absolute representative modulo the integers, one has

\[
 \boxed{
 \sum_{r\ge0}\big\|[z^r]R(z)\big\|_{\mathbb R/\mathbb Z}
 =\sum_{t\ge1}\|C2^{-t}\|_{\mathbb R/\mathbb Z}
 \ge1.}
 \tag{9}
\]

The equality follows from (6): \(P\) has integer coefficients and the noninteger geometric coefficients occur at the distinct exponents \(d_*t\).

For the lower bound, again write \(C=\pm2^v m\), \(m\) positive odd, and put \(L=\lfloor\log_2m\rfloor\).  The term \(t=v+1\) has distance exactly \(1/2\) from the integers.  At every

\[
 t\ge v+L+2,
\]

the absolute value \(m2^{-(t-v)}\) is below \(1/2\), so equals its distance to the integers.  These tail terms sum to

\[
 \sum_{t\ge v+L+2}m2^{-(t-v)}
 =\frac m{2^{L+1}}\ge\frac12.
\]

The two ranges are disjoint, including when \(m=1\).  This proves (9).

Replacing \(C\) by \(qC\) proves the same lower bound for the coefficients of \(qR\), for every nonzero integer frequency \(q\).  Thus allowing the integer stripping to depend on the Fourier frequency does not help either.

## 5. Compatible CRT configurations reduce to these hypotheses

Suppose the original quotient indices are

\[
 k_\alpha(n)=\frac{n-s_\alpha}{d_\alpha},
\]

with all congruences \(n\equiv s_\alpha\pmod{d_\alpha}\) simultaneously compatible.  Choose a common solution \(n_0\) sufficiently large that

\[
 h_\alpha=\frac{n_0-s_\alpha}{d_\alpha}\ge0
\]

for every slot.  After writing \(n=n_0+a\), the quotients are

\[
 k_\alpha(n)=a/d_\alpha+h_\alpha,
\]

and their transported arguments become \(a+d_\alpha(j+h_\alpha)\).  Translating all original projection values by \(n_0\) preserves every signed cancellation identity, so their aggregated weights give precisely (1).

Within a repeated-multiplier group, recentering multiplies the previously defined effective coefficient by a power of two.  It preserves which groups have zero coefficient and which single group is isolated.  The new isolated coefficient remains a nonzero integer, which is all the theorem needs.  Pairwise coprimality and distinct multipliers for individual slots are unnecessary.

## 6. Consequence for the current analytic method

The existing pointwise bound says an integer argument of size \(O(N)\) has \(O(M)\) prime factors above \(R=N^{1/(20M)}\).  Combining it with unaggregated coefficient mass incurs the budget

\[
 O(MH_1\,2^{-K}).
\]

The isolator theorem gives \(H_1\,2^{-K}\ge1\), so that budget cannot be made \(o(1)\) with growing \(M\).

This cannot be repaired solely by first grouping equal arguments.  Formula (8) already applies after all such grouping.  Nor can it be repaired solely by discarding integer coefficients, because (9) still leaves mass at least one.

For a finite cutoff

\[
 R_J(z)=\sum_{K<j\le J}2^{-j}\sum_dz^{dj}W_d(z^d),
\]

one has \(\|R-R_J\|_{\mathrm{coef},1}\le H_1\,2^{-J}\).  Therefore, whenever this omitted mass tends to zero, the aggregate mass of \(R_J\), even after integer stripping, is at least \(1-o(1)\).  The distance-to-integers function is 1-Lipschitz, which gives the stripped version directly from (9).

**What remains open:** the actual signed arithmetic large-prime contribution might cancel.  The theorem does not bound it below.  It shows that a successful single-coordinate extractor would require such arithmetic cancellation, or a different estimate, rather than a stricter use of the present absolute-value argument.  It does not rule out disjunctivity by another method or joint-coordinate approaches.
