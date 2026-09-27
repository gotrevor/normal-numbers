# Simultaneous words in distinct Erdős–Borwein constants

**Research draft, 26 September 2026.**  Ren (Codex) derived the simultaneous extension below.  The scalar construction is credited to the prior sources in §1.  This is a complete proposed paper proof, self-reviewed but not independently refereed.  The character-separation ingredient is proved in `src/NormalNumbers/JointLambertEncoding.lean`; the full arithmetic theorem is not yet formalized.  Mathematical confidence: 85%.  Novelty confidence: 75%, pending a broader literature check.

## Result and boundary

For an integer (b\ge2), write

\[
 E_b=\sum_{m\ge1}\frac1{b^m-1}=\sum_{m\ge1}\frac{\tau(m)}{b^m}.
\]

**Proposed theorem.**  Let (b_1,\ldots,b_d\ge2) be any finite list of **distinct** integer bases.  For each (i), prescribe a finite nonempty base-(b_i) word (w_i).  There are infinitely many common positions (n) such that (w_i) starts at digit (n) of (E_{b_i}), simultaneously for every (i).  In fact, for suitable constants (C,N_0), depending on the bases and words, the number of such positions among the first (N) digits is at least

\[
 N\exp\{-C(\log\log N)^3\}\qquad(N\ge N_0).
\]

Thus the orbit

\[
 (\{b_1^nE_{b_1}\},\ldots,\{b_d^nE_{b_d}\})\quad(n\ge0)
\]

is dense in the full (d)-torus.  The bases may share factors or be powers of one another: **2 and 4 are included**.  Repeated identical bases must be excluded, since their coordinates are identical.  This concerns different constants (E_2,E_4), not two expansions of the same real number.  It proves neither normality nor positive lower density of these occurrences; the displayed lower bound has relative density tending to zero.

## 1. Prior art and what is new here

The first candidate examined this session was scalar disjunctivity via selectable congruence primes.  That is already claimed in [CaptainSude's paper and Lean repository](https://github.com/CaptainSude/erdos-borwein-disjunctivity/tree/bd98789a177470cc4b3e33e6769e859f6144c906), revision `bd98789a177470cc4b3e33e6769e859f6144c906` (7 September 2026).  I read its complete `paper/erdos-borwein-disjunctivity.tex` this session.  It proves binary scalar disjunctivity on paper with the same quantitative shape as above.  Its Lean headline explicitly assumes AGP and a prime-interval estimate.  The paper invokes published unconditional results for these inputs; the conditional status of its Lean development is **not** a new open analytic assumption in the paper theorem.

Its method extends [Campbell, arXiv:2605.24160](https://arxiv.org/abs/2605.24160), which proves recurrence of `11`.  The construction uses the AGP prime-distribution theorem in [Vandehey, Proposition 2.1](https://arxiv.org/abs/1206.0340).  The underlying source is [Alford, Granville and Pomerance, 1994](https://math.dartmouth.edu/~carlp/PDF/paper95.pdf).

**The scalar congruence construction, the buffer of large primes, and its scalar occurrence bound are prior art.**  The new ingredient here is the simultaneous even-integer encoding in §2, followed by the adaptation that makes a single survivor prescribe every coordinate at a common position.  Neither coprimality nor multiplicative independence of the bases is assumed.  Targeted searches for joint/simultaneous Lambert disjunctivity and the repo's negative inventory found no matching result.  That search is limited evidence, not a priority claim.

The September 25 NN review had described scalar C2 as a fresh mathematical endpoint without carrying forward this prior claim, although the September 13 KB leaf had already recorded it.  The present note corrects that assessment; simply completing the scalar C2 branch would be an independent formalization.

## 2. One even integer encodes every coordinate

For (s\ge1), set (Q_s=\operatorname{lcm}(b_1,\ldots,b_d)^s).  Consider the uniform probability measure on the finite multiset

\[
 \left(\left\{\frac{2a}{b_1^s}\right\},\ldots,
 \left\{\frac{2a}{b_d^s}\right\}\right),\qquad 0\le a<Q_s.
\]

**Encoding lemma.**  These measures converge weakly to Haar measure on the full torus as (s\to\infty).

**Proof.**  For a fixed character (h=(h_1,\ldots,h_d)\in\mathbb Z^d), its integral is

\[
 \frac1{Q_s}\sum_{a=0}^{Q_s-1}\exp(2\pi ia\theta_s),
 \qquad\theta_s=2\sum_i\frac{h_i}{b_i^s}.
\]

Here (Q_s\theta_s\in\mathbb Z), so the geometric sum is exactly zero unless (\theta_s\in\mathbb Z), when it equals one.  If (h\ne0), let (b_j) be the smallest base with (h_j\ne0).  Distinctness gives

\[
 \frac{b_j^s\theta_s}{2}
 =h_j+\sum_{b_i>b_j}h_i(b_j/b_i)^s\longrightarrow h_j\ne0.
\]

Also (\theta_s\to0).  Hence eventually (0<|\theta_s|<1), so every fixed nontrivial character integral is eventually **exactly zero**.  Finite trigonometric polynomials are uniformly dense in the continuous functions on the torus, giving weak convergence to Haar measure.  This last step is the usual compact-torus Fourier criterion; it concerns the finite encoder measures, not the orbit of any (E_b).  ∎

Choose closed intervals (J_i) of positive length strictly inside the digit cylinders (I_i) for (w_i).  The lemma implies that for some sufficiently large (s\ge2) and integer (a\ge2),

\[
 x_i=\left\{\frac{2a}{b_i^s}\right\}\in J_i\quad\text{for every }i.
\]

To justify hitting a closed interior box directly, apply weak convergence to its nonempty open interior.  Adding a multiple of (Q_s) to (a) preserves all coordinates and ensures (a\ge2).  Fix this (s,a) for the remainder of the proof.  Set (r=s-1\ge1), and choose (\eta>0) so that (x_i+[0,\eta]\subset I_i) for every (i).

**Exact control.**  For bases 2 and 4, take (s=3,a=29).  Then (\{58/8\}=1/4) is inside the cylinder for binary `0`, while (\{58/64\}=29/32) is inside the cylinder for quaternary `3`.  The same divisor count will prescribe both.  Shallow character resonances really occur: (2(1/4-4/16)=0).  The lemma says they disappear for each fixed character as (s\to\infty), not at every depth or uniformly over all characters.

## 3. The inherited analytic input

Use the following published AGP consequence.  There are constants (X_0,D_0) such that for every (X>X_0), a set (\mathcal D(X)) of at most (D_0) integers greater than (\log X) exists with

\[
 \pi(X;B,u)\ge\frac{X}{2\varphi(B)\log X}
\]

for all (B\le X^{1/4}), (\gcd(u,B)=1), provided no member of (\mathcal D(X)) divides (B).  Fix the height **before** choosing the primes in the modulus.  The second input, a standard PNT consequence, is that ((L,2L)) contains (\gg L/\log L) primes.  Both are ordinary mathematical inputs; neither is newly proved in this note.

The elementary divisor-average estimate is

\[
 \sum_{m=0}^{M-1}\tau(u+mA)
 \le2M(1+\tfrac12\log Y)+2\sqrt Y
 \quad\text{if }\gcd(u,A)=1,\quad 1\le u\le u+(M-1)A\le Y.
\]

Indeed, pair divisors about the square root.  For each divisor (h\le\sqrt Y), the progression has no divisible terms if ((h,A)>1), and at most (M/h+1) otherwise.  Sum and use the harmonic-sum bound.  This estimate is also reproduced in the prior scalar paper.

## 4. A common arithmetic progression

Write (c=\operatorname{lcm}(b_1,\ldots,b_d)).  Let (X\to\infty), and put

\[
 k=\lceil4\log_2\log X\rceil,\qquad
 L=\lfloor(\log_2X)^2\rfloor.
\]

All subsequent inequalities hold for sufficiently large (X), depending on the fixed bases and words.  In particular (k>r\ge1), (L\ge2k), and (X>X_0).

For each exceptional integer (D\in\mathcal D(X)) with a prime divisor in ((L,2L)), discard one such prime.  At most (D_0) primes are removed.  From the remaining primes choose distinct (q) and (p_{j,t}), where

\[
 0\le j<k,\quad j\ne r,\quad1\le t\le j+1.
\]

There are (O(k^2)) primes to choose, and (L/\log L\gg k^2).  Let

\[
 P_j=\prod_{t=1}^{j+1}p_{j,t},\qquad Q=q^{a-1},\qquad
 A=q^a\prod_{j\ne r}P_j^c,\qquad B=A/Q=q\prod_{j\ne r}P_j^c.
\]

Then

\[
 \log B=O_c(k^2\log L)=O_c((\log\log X)^3),\qquad
 Q\le(2L)^{a-1}=(\log X)^{O_a(1)}.
\]

Thus (B\le X^{1/4}) eventually.  No exceptional (D) divides (B): if it did, all its prime factors would be in the chosen interval, including the divisor explicitly excluded from selection.

By CRT choose (0\le R<A) satisfying

\[
 R+r\equiv Q\pmod{q^a},\qquad
 R+j\equiv P_j^{c-1}\pmod{P_j^c}\quad(0\le j<k,\ j\ne r).
\]

The (j=0) congruence gives (R>0), since (r\ge1).  As (Q>r) eventually, (u=(R+r)/Q) is an integer with (1\le u<B), and (u\equiv1\pmod q).  Every selected prime at a killed position (j) sees

\[
 Qu=R+r\equiv r-j\not\equiv0\pmod{p_{j,t}}.
\]

Consequently ((u,B)=1).  Put (M=\lfloor X/B\rfloor+1) and (n_m=R+mA), for (0\le m<M).  AGP supplies at least

\[
 \frac{X}{2B\log X}\ge\frac{M}{4\log X}
\]

indices with (p=u+mB\le X) prime.  For them (n_m+r=Qp), and (p\equiv1\pmod q) implies (p\ne q), hence

\[
 \tau(n_m+r)=2a.
\]

For every (m), all other slots satisfy

\[
 c^{j+1}\mid\tau(n_m+j),
\]

because their (j+1) assigned primes have valuation exactly (c-1).  In particular, (b_i^{j+1}\mid\tau(n_m+j)) for **every** coordinate (i).  Increasing the valuation exponent from 1 in the scalar binary proof to (c-1) costs only the fixed factor (c) in (\log B).

## 5. One tail bound controls all coordinates

Define the nonnegative binary majorant

\[
 T_m=\sum_{j\ge k}\tau(n_m+j)2^{-j},\qquad Y=2QX.
\]

For (k\le j<L), every prime divisor of (A) is assigned to an earlier slot (j_p<k).  It cannot also divide (R+j), since (0<j-j_p<L<p).  Thus ((R+j,A)=1).  Also (n_m+j<QB+QX+L\le Y) for large (X).  The divisor-average estimate gives

\[
 \sum_{m<M}\tau(n_m+j)\ll_a M\log X\qquad(k\le j<L),
\]

since (\log Y=O_a(\log X)) and (\sqrt Y=o(M)), using (B=X^{o(1)}) and (Q=(\log X)^{O_a(1)}).

For (j\ge L), the elementary bound (\tau(n_m+j)\le2\sqrt{Y+j}) gives a summed tail (O(M(\sqrt Y+\sqrt L)2^{-L})).  As (Y\le2^L) and (L\ge2k) eventually, this is (O(M2^{-k})).  Summing both ranges yields

\[
 \sum_{m<M}T_m\ll_a M\log X\,2^{-k}.
\]

Markov's inequality shows that the number of indices with (T_m\ge2\eta) is

\[
 O_{a,\eta}(M(\log X)^{-3})=o(M/\log X).
\]

At least (M/(8\log X)) prime indices therefore have (T_m<2\eta).  For each coordinate the actual remainder satisfies

\[
 0\le\sum_{j\ge k}\frac{\tau(n_m+j)}{b_i^{j+1}}\le T_m/2<\eta.
\]

There is no independence assumption and no union bound over separate prime sets: a **single binary majorant** protects the whole vector.

## 6. Read and count the simultaneous words

For a good prime index, put (n=n_m\ge1).  The Lambert identity, the common divisibilities, and the survivor give, for every (i),

\[
 b_i^{n-1}E_{b_i}
 =\text{integer}+\frac{2a}{b_i^{r+1}}
    +\sum_{j\ge k}\frac{\tau(n+j)}{b_i^{j+1}}.
\]

The fractional part lies in (x_i+[0,\eta)\subset I_i).  Hence every prescribed word starts at position (n).  Distinct primes give distinct starts (n=Qp-r<QX).

For an arbitrary sufficiently large (N), choose the integer height

\[
 X=\left\lfloor\frac{N}{2(2(\log_2N)^2)^{a-1}}\right\rfloor.
\]

Then (X\to\infty), (QX\le N/2), (\log(N/X)=O_a(\log\log N)), and (\log B=O_c((\log\log N)^3)).  The number (M/(8\log X)\ge X/(8B\log X)) absorbs these costs into

\[
 N\exp\{-C(\log\log N)^3\}.
\]

This tends to infinity, completing the proposed proof including arbitrarily late simultaneous occurrences.  ∎

## 7. Adversarial checks and exact scope

| Possible defect | Resolution |
|---|---|
| Shared factors or bases 2 and 4 force dependent encoder coordinates | Only at fixed shallow depths for some characters.  The smallest supported base dominates at large depth. |
| Repeated bases | Real obstruction.  Excluded explicitly; the character `(1,-1)` never decays. |
| Parity of divisor counts | The encoder uses only (2a) from the outset.  No arbitrary odd divisor count is assumed. |
| Encoding lands on a digit boundary | Choose an interior box first, then a positive fixed common margin. |
| Several prescribed survivor values require prime tuples | There is exactly one survivor and one prime (p).  All bases read different fractions of the same count (2a). |
| Raising valuations enlarges the modulus too much | (c) is fixed; (\log B=O_c((\log\log X)^3)=o(\log X)). |
| Exceptional moduli depend on the selected primes | Height first, exclusions second, CRT modulus third. |
| Tail goodness only holds at composite indices | Bad indices are counted over the full progression and are fewer than the AGP prime lower bound. |
| Different words occur at different positions | Every coordinate is evaluated at the same (n_m). |
| A bound holds only along selected heights | §6 selects a height for every sufficiently large (N). |
| Finite probes prove the arithmetic theorem | They do not.  They check encoding and resonance controls only. |

## 8. Reproducible work and next proof boundary

The existing `probes/swingc2_window.py` now has `encode`, `character`, and `test` commands, with its original no-argument census retained.  Run the persistent CLI suite with `./probes/swingc2_window.py test -q`.  It includes hand-computed 58 and 22 witnesses, a shallow resonance, persistent duplicate-base obstruction, the zero character, and explicit resource-cap outcomes.  It does not approximate digit frequencies or infer infinite claims from a finite census.

`src/NormalNumbers/JointLambertEncoding.lean` proves normalized-character convergence, eventual nonvanishing, convergence of the original character to zero, and eventual nonintegrality of the even-lattice character.  The formal statement takes the smallest supported base explicitly; remove zero coefficients before applying it.  This is the key separation calculation in §2, not yet the compact-torus encoding theorem or §§3–6.

Next mathematical review should target the passage from scalar to simultaneous in §§2, 4, and 6.  Subsequent Lean work belongs on a prepared treadmill: freeze the joint cylinder statement, finish the finite-measure Fourier bridge, and parameterize the scalar CRT/tail construction by the lcm of the bases.  Preserve AGP and prime-interval supply as explicit named inputs until their proofs are imported.  Do not claim the full headline merely because the character lemma compiles, and do not detour into normality, prime-tuple hypotheses, or scalar C2 bookkeeping.
