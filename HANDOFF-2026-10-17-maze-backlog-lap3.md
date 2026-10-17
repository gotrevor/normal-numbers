# Maze backlog lap 3 — L1 integer-block expansion proved (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-16-maze-backlog.md` in order.  Parts 1–2 were already complete.
This lap advanced Part 3/L1 through its arithmetic and infinite-series crux.  The zero-window
and simple-normality contradiction remain, followed by L2 and the two Maze rows, so the kickoff's
terminal condition has not yet been reached.

## Concrete advance

Added `NormalNumbers.StonehamSumsBoundary` and proved:

- `prime_pow_dvd_stoneham_boundary_block`: for every prime `p ∤ b`, the proposed numerator
  `b^((p-1)p^j)-1` is divisible by `p^j`.  The proof uses Fermat to write
  `b^(p-1) = 1 + p*a`, then mathlib's elementary `pow_pow_modEq_one`; no bespoke LTE split is
  needed, including at `p = 2`.
- `stonehamBoundaryTerm_scaled_eq_block`: the paired term at odd level `2k+1`, scaled through
  its right endpoint `p^(2k+2)`, is exactly the natural-number coefficient
  `(b^((p-1)p^(2k+1))-1)/p^(2k+1)`.
- `stonehamBoundaryTerm_eq_pair` and `summable_stonehamBoundaryTerm`: the block term is exactly
  the pairing of two consecutive `α_{b,p}` terms against one `(p+1)α_{b,p²}` term, and the
  resulting series is summable.
- `stoneham_sub_succ_mul_eq_tsum_boundary`: the full L1 combination
  `α_{b,p} - (p+1)α_{b,p²}` equals the sum of these positive integer blocks.  The proof splits
  the `α_{b,p}` series into even and odd indices with `tsum_even_add_odd` and recombines the
  absolutely summable series.

The module is imported by the root `NormalNumbers` library.  No `sorry` or new hypothesis was
introduced.

## Verification

Narrow elaboration during development:

```text
lake env lean src/NormalNumbers/StonehamSumsBoundary.lean
```

completed successfully.  The final target/axiom gate and repository pre-commit build are recorded
in the commit containing this handoff.

## Current crux and next attack

Finish L1 by porting the head/tail proof from `StonehamSums.lean`:

1. Define the positive majorant
   `A_k = 1/(p^(2k+1) * b^(p^(2k+1)))` and prove
   `0 ≤ stonehamBoundaryTerm b p k ≤ A_k` plus a geometric shift bound for `A_{k+r}`.
2. At digit position `i` with `p^(2k+2) ≤ i < p^(2k+3)`, scale by `b^(i+1)`.
   Terms through `k` are integer blocks divisible by `b`; the tail beginning at `k+1` is in
   `[0,1)`.  This gives `digitOf ... i = 0`.
3. Copy the two-prefix frequency contradiction from `not_isSimplyNormal_stoneham_sum`, replacing
   the ratio `2/3` by the general window endpoints `p^(2k+2), p^(2k+3)` (prime gives `p ≥ 2`).
   This proves the ratified headline `not_isSimplyNormal_stoneham_sub_succ_mul`.

After L1, implement L2's cyclotomic block series and then add both audited Maze rows.
