# ON-LINE FINDINGS 2026-10-06: Korobov-type sum ranges for `ThreeAdicWindowAvg`

**Request:** cantorbad lap 10 (commit 78809195): fetch arXiv:1606.07911 and arXiv:1605.07553; give the
exact range of N, relative to the modulus p^k with p fixed, for nontrivial bounds on
Σ_{n<N} e(a gⁿ/p^k).  Used by `CantorBadNormal.ThreeAdicWindowAvg`.

**Sources read:** both arXiv abstracts, fetched from the arXiv API on 2026-10-06 (quoted verbatim
below).  Full texts not read.  The answer was first written inline in `ON-LINE-REQUEST.md`
(commit 8e3bbfdc).  It moves here so the request can be cleared.

## The two papers

- **arXiv:1606.07911**: J. Vandehey, *Differencing Methods for Korobov-type exponential sums* (2016).
  The abstract says, verbatim: "We study exponential sums of the form Σ_{n=1}^N e^{2πi a bⁿ/m} for
  non-zero integers a,b,m.  Classically, non-trivial bounds were known for N ≥ √m by Korobov, and
  this range has been extended significantly by Bourgain as a result of his and others' work on the
  sum-product phenomenon.  We use a new technique, similar to the Weyl-van der Corput method of
  differencing, to give more explicit bounds that become non-trivial around the time when
  exp(log m / log₂ log m) ≤ N.  We include applications to the digits of rational numbers and
  constructions of normal numbers."  This is for a **general modulus m**, not specifically p^k.
- **arXiv:1605.07553**: W. Banks and I. Shparlinski, *Bounds on short character sums and L-functions
  for characters with a smooth modulus* (2016).  It uses Postnikov (1956) and Korobov's (1974) double
  Weyl sums for moduli with a small core Π_{p|q} p.  It is about **character sums**, not
  Σ e(a gⁿ/p^k) directly, and its abstract states no N-range for that sum.

## Consequence for `ThreeAdicWindowAvg`

- **Shallow depth (3^j ≤ N, full periods):** no literature is needed.  This is the lap-10 handoff's
  Next #1 and stays a lap target.
- **Middle depth:** m = 3^k with k ≍ N log₃ b, so N ≍ log m.  That is far below every known range:
  √m (Korobov), Bourgain's sum-product range, and exp(log m / log log m) (Vandehey).  The p-adic
  Postnikov/Korobov route turns gⁿ mod p^k into a polynomial phase of degree about k.  Vinogradov-type
  bounds then need N superpolynomial in k.  I recall the shape as roughly log N ≫ (log m)^{2/3}, but
  **I could not confirm that exponent from a source**.  The conclusion does not depend on it: N ≍ k is
  out of range either way.
- So **a single-numerator Korobov bound at length N ≍ log m is the digits-of-powers regime, and it is
  OPEN.**  Record it in Lean as an open/believed node or a cited `Literature.*` Prop (citing
  Vandehey 2016 for the best known range).  Don't make it a lap target.

## The route still alive: averaging over numerators

Over a full residue system a mod M = 3^k, with 3 ∤ b and N ≤ ord_M(b):

  Σ_{a mod M} |Σ_{n<N} e(a bⁿ/M)|² = M · #{(n,n') : bⁿ ≡ bⁿ' (mod M)} = M·N,

which is mean-square √N cancellation with no input needed.  (It needs b's powers to be distinct mod M.
That fails when 3 | b, which matches `not_threeAdicWindowAvg_three`.)  The remaining question is
whether the obstacle numerators p, weighted by μ_K / resLaw, are spread enough mod the 3-adic part
of q to inherit this.  That is a **large-sieve / dispersion statement in a**, not a Korobov statement
in n.  The `CantorBadNormal.lean` large-sieve remark near line 2277 is the closest existing hook.

## Suggested Lean records (for the next lap)

1. Replace the docstring at `CantorBadNormal.lean` ~4675 ("Literature route (lap 10, not yet read in
   full)") with the verdict above, and state the middle-depth single-a bound as an open Prop
   (confidence: believed open, not believed false).
2. Prove the mean-square identity.  It follows from `sum_ee_mod` plus counting coincident powers, and
   it is a real theorem.
3. State the numerator-dispersion node: the μ_K-weighted obstacle numerators inherit the mean square
   up to a loss.  This is the new frontier node in place of a Korobov bound.
