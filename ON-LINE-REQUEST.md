
## 2026-10-06 (cantorbad lap 10)
Fetch arXiv:1606.07911 ("Differencing methods for Korobov-type exponential sums") and arXiv:1605.07553;
need: the exact range of N (relative to the modulus p^k, p fixed) for nontrivial bounds on
Σ_{n<N} e(a g^n / p^k).  Used by `CantorBadNormal.ThreeAdicWindowAvg`.

### Answer (Ren, host, 2026-10-06 16:50)
- arXiv:1606.07911 = Vandehey, "Differencing methods for Korobov-type exponential sums".  Abstract,
  verbatim: "Classically, non-trivial bounds were known for N ≥ √m by Korobov, and this range has been
  extended significantly by Bourgain ... [our] bounds become non-trivial around the time when
  exp(log m / log₂ log m) ≤ N."  General modulus m.
- arXiv:1605.07553 = Banks–Shparlinski, "Bounds on short character sums and L-functions for characters
  with a smooth modulus" (Postnikov 1956 + Korobov 1974 double Weyl sums, small-core moduli).  It is
  about character sums, not Σ e(a gⁿ/pᵏ) directly; the abstract states no range for that sum.
- Consequence for `ThreeAdicWindowAvg` at the middle depth: m = 3^k with k ≍ N log₃ b means
  N ≍ log m, far below every known range (√m; exp(log m / log log m); Postnikov-type prime-power
  ranges are polynomial in k at best and still need N ≫ k).  A single-a Korobov bound at that
  length is the digits-of-powers regime and should be treated as OPEN.  Record it as such in Lean
  (`Literature.*` Prop or node docstring with this citation), not as a lap target.
- The route still alive: averaging over the NUMERATORS.  Over a full residue system of a mod 3^k,
  Σ_a |Σ_{n<N} e(a bⁿ/3^k)|² = 3^k · #{(n,n') : bⁿ ≡ bⁿ' mod 3^k} = 3^k N for N ≤ ord, i.e.
  mean-square √N cancellation for free.  The question is whether the obstacle numerators p (with
  their μ_K / resLaw weights) are spread enough mod the 3-adic part of q to inherit that: a
  large-sieve / dispersion statement in a, not a Korobov statement in n.  State that as the node.
