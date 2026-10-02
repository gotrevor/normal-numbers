# Explicit normal `x` with `x²` non-normal (sweep rows 3 + 5): audit, 2026-10-02

Lean record: `src/NormalNumbers/ExplicitSquareNonNormal.lean` (namespace
`NormalNumbers.ExplicitSquare`).  This doc gives direction only; every claim below cites a declaration.

## Verdict

- **Row 3 (Manai: explicit normal `x` with `x²` not normal): tractable, 65%.**  The sweep's
  dimension-zero plan is the hard way round.  Row 3 only needs `x² = y` **non-normal**, not
  deterministic, so `y` can live on a **positive-dimension** self-similar set where the Fourier
  input is literature.  On the quarter-Cantor set (`cantorDigits`: digit 0 is `1`, odd digits `0`,
  even digits free), every point misses the block `11`, so it is non-normal by structure
  (`not_isNormal_cantorReal`, **proved**).  No frequency defect has to survive the
  derandomization.  Target: `exists_computable_normal_sq_not_normal`, already **wired**
  from the cited `BakerBanajiQuarterCantor` plus two named steps.
- **Row 5 (Bergelson–Downarowicz Q2/Q3): does NOT share the lemma; 15%.**  A deterministic `y`
  forces a dimension-zero support.  There, polynomial decay is impossible
  (`not_polyDecay_sparse_of_densityZero`), so Baker–Banaji is closed for row 5.  The open input is
  curved *logarithmic* decay, `inv_logDecay_squares`.  Manai 2606.08325 §1 says `√` and other
  analytic maps are beyond current methods, even for existence.  Target
  `exists_oneFreqZero_inv_normal` is wired via `exists_inv_normal_of_logDecay`.

**Freshness.**  Newest versions read: 2506.15422v5, 2508.09319v4 (2026-09-22), 2609.24665v1,
2607.06773v1, 2506.12929v1.  `papers followups` lists only Manai's own papers (2606.08325,
2609.24665, 2508.09319) plus Farhangi–Mance 2512.01239 and Downarowicz–Weiss 2308.04540.  None of
them gives an explicit example.  2508.09319v4 restates the explicit problem one day after
2609.24665 appeared.

## Difficulty check

1. **Proved implications** (this file): structural non-normality, `(√y)² = y`, the affine control,
   the non-explicit existence `exists_sqrt_normal_sq_not_normal` (from BB plus Step 1), and both
   targets' wiring.  **Unproved premises:** `ae_isNormal_of_polyDecay` (Manai `lem:decaynormal`,
   routine, 97%) and `exists_computable_isNormal_sqrt_of_polyDecay` (the derandomization, 75%).
   **Mechanism:** Becher–Figueira / BLD Algorithm 1 greedy halving.  Its bad sets have dyadic
   cylinder approximations with explicit error, so membership is decidable with rational arithmetic.
2. **Affine sibling.**  `not_polyDecay_rat_affine` is proved (from Step 1).  The same mechanism run
   on `F(t) = qt + r` provably fails, so the argument has to use `F'' ≠ 0`, and
   `BakerBanajiQuarterCantor` requires it.  **Dimension threshold.**  Density-zero `S` kills
   polynomial decay (Barrier 1).  `sCount S n = o(log n)` kills any uniform `(log|ξ|)^{-η}` decay
   (`not_logDecay_sparse_of_littleLog`, a Fejér mean-square bound).  So the DEL route needs
   `#S∩[0,n) ≳ log n`: powers of 2 sit on the edge and factorials fall below it.
3. **Repo tools reused:** `digitOf_realOfDigits`, `countOccurrences_eq`, `isNormal_rat_mul_add`
   (Wall rational).  Step 1 is to be closed with `equidistributed_of_weyl` +
   `isNormal_iff_equidistributed_orbit` (`fourierMean` is the Weyl average).  No prior
   Manai / Bergelson / Becher–Lew Deveali / pushforward work exists in `src/`, the Maze or `docs/`.

## Hardest step

`exists_computable_isNormal_sqrt_of_polyDecay`.  Its analytic content is light because the decay
is uniform in frequency, unlike BLD, who needed a Korobov residue count for odd bases.  The cost is
**computability engineering** in Mathlib's `Computable`: rational interval evaluation of
`fourierMean (orbit 2 √y)` on cylinders, plus BLD's invariant `μ(I_i \ Δ) > 0`.

**Caveats.**
- (a) `Computable` is the Becher–Figueira sense of "explicit".  Manai may want something more
  closed-form.
- (b) If Baker–Banaji's constants are ineffective, the witness is computable but not *named*: the
  algorithm takes rationals `C' ≥ C`, `δ' ≤ δ` as parameters.  Defining a named digit sequence
  needs effective constants (Mosquera–Shmerkin's homogeneous-case argument looks effective, 60%).
- (c) `BakerBanajiQuarterCantor` is taken from Manai's quotation of BB Cor 1.5, not from BB's own
  text.  Check that against arXiv 2401.01241 before any outward use.

## Recommended treadmill objective

> Prove the row-3 premises in `ExplicitSquareNonNormal.lean`: first `sqrt_bakerBanaji_hyp` and
> `ae_isNormal_of_polyDecay` (second moment → Borel–Cantelli on squares → Weyl); then
> `exists_computable_isNormal_sqrt_of_polyDecay`.  Done when
> `exists_computable_normal_sq_not_normal` depends only on `BakerBanajiQuarterCantor`.  A
> refutation of any premise is an advance: record it as a Maze row.

`--require-decls NormalNumbers.ExplicitSquare.exists_computable_normal_sq_not_normal,NormalNumbers.ExplicitSquare.exists_computable_isNormal_sqrt_of_polyDecay,NormalNumbers.ExplicitSquare.ae_isNormal_of_polyDecay,NormalNumbers.ExplicitSquare.sqrt_bakerBanaji_hyp,NormalNumbers.ExplicitSquare.not_isNormal_cantorReal,NormalNumbers.ExplicitSquare.not_polyDecay_rat_affine,NormalNumbers.ExplicitSquare.BakerBanajiQuarterCantor`

Row 5 should not go to a treadmill yet.  Its crux, `inv_logDecay_squares`, needs a mechanism first:
a curved Riesz-product / decoupling bound on a dimension-zero support.  The cheap moves are
Barriers 1 and 2, which record the closed route.
