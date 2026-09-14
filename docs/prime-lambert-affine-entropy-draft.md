# Normality after disjunctivity: joint entropy and scale synchronization

*AI-assisted research draft by Ren (OpenAI Codex).  Consequences of the candidate proof in [the main draft](prime-lambert-disjunctivity-draft.md) and [fixed-base extension](prime-lambert-disjunctivity-fixed-base.md); not externally validated or fully formalized.*

## Corrected verdict

The zonotope argument forces the joint quantized affine input to have entropy
\((1-o(1))mH\).  It needs neither ergodicity nor product typicality.  Hence the affine marginal
block entropies are near maximal on average.  The remaining normality gap is precise: ordinary
nonnormality must be synchronized with these varying affine scales strongly enough to force an
averaged marginal entropy deficit.

## 1. The false typical-set shortcut

An invariant low-entropy measure need not concentrate on a small typical set.  For example

\[
\nu=\tfrac12\delta_{0^\infty}+\tfrac12\mu_{1/2}
\]

has entropy \(\tfrac12\log2\), but every collection \(C_m\) of at most \(2^{dm}\) words, \(d<1\),
satisfies

\[
\nu(C_m)\le\tfrac12+\tfrac12\,2^{-(1-d)m}.
\]

Small high-probability typical sets require ergodicity, or a uniform entropy bound on every
relevant ergodic component.  They are unavailable for a general subsequential empirical limit.

## 2. An arbitrary-law information set

Let \(Z=(Z_1,\ldots,Z_H)\in(\{0,1\}^m)^H\) be the vector of length-\(m\) blocks at all affine
indices \(k_\alpha(n)\), with \(n\) uniform on the one common arithmetic sample.  Suppose

\[
\operatorname{Ent}_2(Z)\le(1-\delta)mH. \tag{1}
\]

Put \(I(z)=-\log_2\Pr(Z=z)\) and

\[
\mathcal A=\{z:I(z)\le(1-\delta/2)mH\}.
\]

Markov's inequality gives

\[
\Pr(Z\in\mathcal A)\ge1-\frac{1-\delta}{1-\delta/2}
=\frac\delta{2-\delta}, \tag{2}
\]

while every atom in \(\mathcal A\) has mass at least
\(2^{-(1-\delta/2)mH}\), so

\[
|\mathcal A|\le2^{(1-\delta/2)mH}. \tag{3}
\]

This positive-mass low-information set exists for every finite joint law.

## 3. Zonotope contradiction

Take \(m=aK+O(1)\), so these cylinders are arbitrary input boxes of side
\(\eta=2^{-aK}\).  The zonotope proof applies to their union without product structure.
Since \(r/H\to1\), choose \(\tau<\delta/4\); then

\[
(1-\tau)r-(1-\delta/2)H\gg_\delta H.
\]

Consequently

\[
\operatorname{Haar}\bigl((A(\mathcal A))_{d_{\rm av},\varepsilon\eta}\bigr)=o(1) \tag{4}
\]

for a sufficiently small fixed \(\varepsilon>0\).

Suppose rough-tail localization gives

\[
\mathbb E_n d_{\rm av}(Y_{\rm full}(n),Y_{\rm small}(n))=o(\eta). \tag{5}
\]

Equations (2) and (5), plus Markov, put at least \(\delta/(2-\delta)-o(1)\) of the small-prime
outputs inside the tube (4).  Use the bump equal to one on the image and falling linearly to zero across this tube.  Its actual expectation is at least \(\delta/(2-\delta)-o(1)\), directly by the unconditional expected-distance bound.  The uniform joint small-prime theorem applies to its Jackson approximation, even though this particular union depends on \(N\) and on the actual distribution.  Choose the fixed approximation error smaller than \(\delta/(10(2-\delta))\); all constants may depend on this fixed \(\delta\).  Haar expectation tends to zero, giving the contradiction.  No conditional prime estimate is being assumed.  Therefore

\[
\boxed{\operatorname{Ent}_2(Z)=(1-o(1))mH.} \tag{6}
\]

Entropy subadditivity now yields

\[
\boxed{\frac1H\sum_{\alpha=1}^H\operatorname{Ent}_2(Z_\alpha)
=(1-o(1))m.} \tag{7}
\]

This is a genuine consequence of the candidate arithmetic mechanism, stronger than
disjunctivity.

## 4. A quantitative version and a genuine frequency consequence

The same bounds allow a deficit fraction \(\delta=C/\sqrt K\), with a sufficiently large fixed constant \(C\).  Take \(m=\lfloor K/4\rfloor\), enlarge the Fourier box to degree \(D=O(K2^{K/4})\), and choose the tube width fraction \(\varepsilon=\delta/8\).  The logarithmic tube-volume saving is \(\Omega(\delta KH)\), which dominates the \(O(H\sqrt K)\) distortion once \(C\) is large.  Jackson error can be made smaller than any fixed positive multiple of \(\delta\) by enlarging its degree constant.  The arithmetic errors are exponentially small in \(K\), up to logarithmic factors, hence also negligible relative to this budget.  The circular-energy test sites still lie below \(J\), and the Fourier cost is unchanged at its leading order.  Thus the internally audited quantitative consequence is

\[
\operatorname{Ent}_2(Z)\ge mH-O(H\sqrt K).
\tag{8}
\]

Here \(Z_\alpha\) can equivalently be the first \(m\) dyadic digits of the actual circle input \(x_\alpha\).  This formulation also makes sense for the other fixed-base constructions.

For the binary construction, (8) forces **uniform word frequencies on a precisely specified averaged sample**.  Fix a length \(\ell\).  Average over the arithmetic sample \(n\), the \(H\) atoms \(\alpha\), and offsets \(0\le h\le m-\ell\).  The \(\ell\)-bit word at

\[
k_\alpha(n)+h
\]

has distribution tending to the uniform law on \(\{0,1\}^\ell\).

To prove this, subadditivity first gives \(\sum_\alpha\operatorname{Ent}_2(Z_\alpha)\ge mH-O(H\sqrt K)\).  For each residue of the starting offset modulo \(\ell\), partition each \(m\)-block into disjoint \(\ell\)-blocks and at most \(2\ell\) boundary bits.  Subadditivity again bounds the sum of the \(\ell\)-block entropy deficits by \(O(H\sqrt K+H\ell)\).  Sum the \(\ell\) partitions and divide by the \(H(m-\ell+1)\) sampled blocks.  Their mean entropy deficit is \(O_\ell(K^{-1/2})\).  Pinsker's inequality and Cauchy-Schwarz make their averaged total-variation distance from uniform \(O_\ell(K^{-1/4})\), proving the claim.

For the elementary base-4 construction the corresponding binary positions are \(2k_\alpha(n)+h\).  This is a structured sparse averaging theorem, **not** ordinary binary normality.

## 5. Exact remaining synchronization hypothesis

Nonnormality gives a defective ordinary empirical subsequence, not a defect under the sparse averaging weights just proved uniform.  The thin progressions matter at least as much as the unequal denominators: in this construction the \(d_\alpha\) are actually close in relative size, with \(d_{\max}/d_{\min}=1+O(1/K)\).  Thus wildly different affine scales are not the correct diagnosis.  Ordinary averages need not describe these residue classes, and the binary two-point branch additionally chooses favorable outer scales.

A sufficient final bridge is:

> Every fixed ordinary block-frequency defect supplies infinitely many construction scales at
> which the average affine marginal entropy in (7) is at most \((1-\delta)m\), for some fixed
> \(\delta>0\).

That would contradict (7) and prove normality.  It is not presently derived from nonnormality.
The earlier density-zero assignment claim is removed: overlapping sampled blocks require
compatibility, and the sampled-position density was not established for the actual family.
