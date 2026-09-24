# Campbell 2026 — pin note (added 2026-09-23)

J. M. Campbell, *Abelian-normal decimal expansions*, arXiv:2603.04396 (v2).  PDF alongside
(gitignored).  Short (≈ 8 pp).

## Coverage

Read: abstract, the definition, Theorem 1 statement and the opening of its proof.  Not read: the
full proof or the construction's details.

## What it says

**Abelian-normal:** count length-k subwords up to permutation (abelian equivalence), normalized
by the class size, and require the uniform limit.  Normal ⟹ abelian-normal.  **Thm 1:** an explicit
constant Ξ₁₀ is abelian-normal but not normal in base 10.

## Why it matters here

A strictly weaker notion between simple normality and normality, with an explicit separating
example.  Useful as a control in the style of our "disjunctive nonnormal" controls: a candidate
criterion that Ξ₁₀ passes cannot be a normality criterion.  Low priority.

## Ren's derivation (2026-09-23, not in the paper): abelian normality in the Walsh dual

Base 2, digits as signs ε_i = (−1)^{x_i}.  Abelian normality at window length k says the window
sum W_k(n) = Σ_{i<k} x_{n+i} has the Binomial(k, 1/2) law along n.  Write z^{ε} = a + bε with
a = (z+z⁻¹)/2, b = (z−z⁻¹)/2; then E[z^{Σε}] = Σ_{A⊆[k]} a^{k−|A|} b^{|A|} E[ε_A], and the
monomials a^{k−j}b^j are linearly independent in z.  Hence

    abelian-normal (base 2)  ⟺  for every k and 1 ≤ j ≤ k:  Σ_{A ⊆ {0..k−1}, |A| = j} parityMean(A) = 0,

against `isNormalSequence_two_iff_parityMean`: normal ⟺ parityMean(A) = 0 for every nonempty A.
Abelian normality asks only for the **S_k-symmetrized** (elementary-symmetric) sums of the
parity correlations to vanish; normality asks for each one.  Base b: the same with the
`WalshBase` characters of (ℤ/b)^k averaged over coordinate permutations.

Consequences:
- **Base 2 is rigid through length 3, free from length 4** (exact linear-algebra probe 2026-09-23,
  stationarity + abelian balance at every length ≤ L, solution-space dimension ignoring
  positivity): L=2: 0, L=3: 0, L=4: 1, L=5: 5, L=6: 16, L=7: 42.  k = 2 is free for the reason
  that #01 and #10 differ by at most 1; k = 3 is then forced by marginal consistency
  (p(00x) = p(x00) pins p(001) = p(100) = 1/8, hence p(010)).  ⚠️ Ren's first version of this
  note said "cheat at k ≥ 3"; the probe refuted it.  The L = 4 direction: +ε on
  0011, 0100, 1010, 1101 and −ε on 0010, 0101, 1011, 1100 (ε = 1/16 kills the second four).
  Base 3 is free already at L = 2 (dimension 1: cyclic flow 0→1→2→0).
- Lean: `src/NormalNumbers/AbelianNormal.lean` (headline iff, `rigid_three`, `separation_four`);
  kickoff `KICKOFF-2026-09-23-abelian-normal.md`.
