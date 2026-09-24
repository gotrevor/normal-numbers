# Becher–Lew Deveali 2026 — pin note (added 2026-09-23)

V. Becher, S. Lew Deveali, *Normal numbers in sparse Cantor sets*, arXiv:2607.06773 (v1,
2026-07-07).  PDF alongside (gitignored).

## Coverage

Read: abstract, §1 statements of Theorems 1–3 and the comparison with Volkmann.  Not read: the
proofs (extension of Schmidt 1960 to a Hausdorff-dimension-zero, non-identically-distributed
Bernoulli measure).

## What it says

S sparse (at least log k elements of S in every interval of length k); C(S) = numbers whose binary
expansion has 1s only at positions in S (Hausdorff dimension 0).
- **Thm 1:** uncountably many x ∈ C(S) are normal in **every odd base**.
- **Thm 2:** for any even b, uncountably many x ∈ C(S) are normal in no even base ≤ b.
- **Thm 3:** for computable S (computable sparsity exponent), an algorithm outputs such an x in
  base 2 — the first known numbers **deterministic in base 2 yet normal in all odd bases**.
- Conjecture: given determinism in one base, normality in all multiplicatively independent bases is
  prevalent.

## Why it matters here

Direct cousin of `normal-numbers-cross-base-intuition.md` (Schmidt 1960 Thm 2 witnesses, normal in
base 4 while ternary-nondisjunctive): here the base-2 side is as thin as possible (dimension 0) and
the odd-base side is still fully normal.  Relevant to any cross-base transfer argument and to the
"sparse carries" routes.  Constructed numbers, not natural constants.
