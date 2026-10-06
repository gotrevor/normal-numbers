# ADDENDUM 2026-10-05 (late): the BFR bet — read after the kickoff

Trevor: dig into whether this lane's count says anything about counting rationals near the
Cantor set (Broderick–Fishman–Reich, Bugeaud–Durand) until that bet is below 1% or it lands.
Ren's opening estimate was 15%.  This addendum takes priority over H4/H5 ordering in the kickoff.

## What Ren settled on paper (verify, then record in Lean)

1. **The exact count is the classical covering bound.**  `card_lowResidue_le` (≤ `2^{k+1}`
   Cantor numerators per `q`) is, in BFR terms, "K at scale `1/q` has `2^m` pieces, each holding
   ≤ 2 fractions `p/q`", which gives `N_K(Q, δ) ≲ Q^{1+dim K}`, the known trivial bound.  So the
   count itself transfers nothing new.  Record: Maze row "exact residue count as a BFR input"
   (verdict `vacuous`), citing `card_lowResidue_le` and a stated `Literature` Prop or definition
   of the covering bound.
2. **`RunEnteringCount` and Bugeaud–Durand are siblings, neither implies the other.**  BD counts
   rationals near `K` at the measure level (resolution ≥ the cylinder); `RunEnteringCount` counts
   rationals within `q^{−τ} < 3^{−b}` of the `2^b` discrete endpoints `P/3^b`.  Write both
   directions' failure precisely (a finite point set is measure zero; endpoint counts at
   sub-cylinder scale are invisible to BD).  If either direction does hold in some regime, that
   is the transfer: find it.
3. **Inverse Cantor sums cancel (probe).**  `experiments/cantor_inverse_sums.py` (pytest file
   beside it): `S(n) = Σ_{P ∈ C_b, 3∤P} e(n P⁻¹ / 3^b)` has `max_{3∤n} |S|/|C|` falling from
   0.276 (b = 6) to 0.036 (b = 14), about `√(log 3^b / |C|)`, while the direct Riesz sum stays at
   0.466.  Freeze `InverseCantorSumBound : Prop` (power saving `|S(n)| ≤ C |C_b| 3^{−δ b}`).
4. **Single-sum cancellation is not enough.**  From `InverseCantorSumBound` with saving `δ`, the
   window count follows only for `m > (1 − δ) b`; even square-root (`δ = ½ log₃ 2 ≈ 0.315`) gives
   `m > 0.685 b`, while the binding windows are at `m ≈ b/τ ∈ [0.387 b, 0.5 b]`.  Prove the
   conditional implication and the arithmetic barrier in Lean; Maze row.

## The live question (where the remaining percentage sits)

`RunEnteringCount` needs a **bilinear** estimate: incidences between the 3-adic Cantor set `C_b`
and the product set `{r · q̄ : q ≈ 3ᵐ, |r| < R}` in `ℤ/3^b`.  Tools to price, in order:
- **Postnikov / 3-adic linearization** on the `q` side (inverses of `q` in a progression mod
  `3^j` are a polynomial in the progression variable), turning the hyperbola into a
  polynomial-phase sum against the Cantor set.
- **Type I/II à la Maynard (restricted digits)**: `C_b = C_low + 3^j C_high` is a genuine product
  structure; Maynard needs a large base because his `L¹` Fourier bound is weak.  Our
  `Λ = 1.29663` is that weakness.  Does the inverse map's square-root cancellation (item 3)
  substitute for the `L¹` bound in the Type II step?
- **Sum–product in `ℤ/3^b`** (Bourgain): `C_b` is non-concentrated (`|C ∩ (a + 3^k ℤ)| = 2^{−k}|C|`),
  so multilinear sums over it cancel, ineffectively.  Is the count expressible as a ≥ 3-linear
  sum?
- **Numerics first**: measure the actual window count against the heuristic density at
  `m ≈ b/τ` for b up to about 16.  An excess would be structure (and news); agreement is the
  conjecture's evidence.

Restate two numbers at the end of each lap: the node confidence, and the **BFR-bet** confidence
(probability that this lane's methods yield a statement about rationals near `K` itself, or a
restricted-digit Kloosterman bound of independent interest).  Stop the BFR thread when the bet is
below 1% with every route in the Maze, or when a route survives with frozen statements.

## Frozen 2026-10-05 late: merge `proof/stretch-bfr` first

Items 1-4 above are now declarations in `src/NormalNumbers/StretchBFR.lean` on branch `proof/stretch-bfr` (worktree `~/src/nn-bfr`, built green with root audits), with 3 Maze rows.  At the start of the next lap run `git merge proof/stretch-bfr` and resolve the import/waiver/Maze-list lines (both sides append).  It also waives `ev_expTest_mass_mid`, which the root barrier audit flagged as untagged: replace that waiver if you prefer a crux link.  Then grind `card_near_cantor_le` and `windowCount_of_inverseSum`, and extend the probe to shifted sets (`A ≠ 0`, `b' < b`) before trusting `InverseCantorSumBound`.
