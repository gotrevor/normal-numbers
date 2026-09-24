# Kanado–Saito 2024 — pin note (added 2026-09-23)

Y. Kanado, K. Saito, *Normality of algebraic numbers and the Riemann zeta function*,
arXiv:2412.02337 (v2, 2024-12-17).  PDF alongside (gitignored).

## Coverage

Read: abstract, §1 (intro + Theorem 1.1, Corollary 1.2 statements), list of §2 results by name.
Not read: the proofs (§2–§4: Perron's formula, functional equation, Ridout's theorem).

## What it says

For a **positive algebraic irrational** α and base b ≥ 2: α is normal to base b **iff**, for every
k ≥ 0,

    lim_{N→∞} (1/log N) Σ_{1≤|n|≤N} ζ(−k + 2πin/log b) · e^{2πin log α/log b} / n^{k+1} = 0.

It extends the authors' 2023 result (simple normality of `2^{p/q}` to base 2 ⟺ an o(l) zeta sum)
from `2^{p/q}` to all algebraic numbers and all bases, via periodic Bernoulli polynomials ψ_k.
Algebraicity enters through **Ridout's theorem** (Thm 2.3), which bounds the approximation
error terms; the criterion is stated only for algebraic α.

## Why it matters here

A **reformulation**, not a normality proof: it converts Borel's conjecture for algebraic
irrationals into a statement about vertical-progression means of ζ.  It sits beside our
Weyl/Walsh criteria (`isNormalSequence_two_iff_parityMean`, `WalshBase`) as a *third* dual: an
analytic criterion specialized to algebraic inputs.  It does not apply to ζ(5)-type constants
(not known algebraic, and presumably transcendental).  Surfaced 2026-09-23 in a
"anything new on normality of zeta values?" sweep.
