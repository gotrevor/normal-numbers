# Maze backlog review lap 4 — L1 boundary theorem proved (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-16-maze-backlog.md` in order.  Parts 1--2 remain complete.  This
review lap independently reconstructed Part 3 from the ratified statements, source note,
checked-in Stoneham definitions, `StonehamSums.lean`, the Maze, and recent history before
continuing the uncommitted lap-3 block expansion.

The review found no statement drift: the `k`-th paired L1 block ends at `p^(2k+2)`, and the
next block begins at `p^(2k+3)`, so the required 0-indexed digit window is precisely
`[p^(2k+2), p^(2k+3))`.  This route reaches the frozen L1 headline without any additional
hypothesis.

## Concrete advance

The ratified theorem

```lean
not_isSimplyNormal_stoneham_sub_succ_mul
```

is now proved.  Its proof adds the following kernel-checked spine in
`NormalNumbers.StonehamSumsBoundary`:

- `stonehamBoundaryTerm_scaled_eq_shifted_block`: after any scale beyond its right endpoint,
  a paired term is an integer coefficient followed by a positive power of `b`;
- `stonehamBoundaryTerm_nonneg`, `stonehamBoundaryTerm_le_majorant`,
  `stonehamBoundaryMajorant_shift_le`, and `stonehamBoundaryMajorant_scaled_lt_half`: the
  remaining tail is positive, geometrically bounded, and strictly below one after scaling at
  every point of the gap;
- `stoneham_sub_succ_mul_mem_Ico`: the whole combination is in `[0,1)`;
- `digitOf_stoneham_sub_succ_mul_eq_zero`: every base-`b` digit in
  `[p^(2k+2), p^(2k+3))` is zero;
- the headline contradiction compares zero counts at the two endpoints.  The tolerance
  `1/(4b)` works uniformly: after multiplying by `4b`, the forced window would require
  `5p < 3 + 4b(p-1)`, the reverse of the limiting frequency bounds.

The proof has no `sorry` and the headline has exactly the standard trust-base axioms.

## Verification

```text
lake env lean src/NormalNumbers/StonehamSumsBoundary.lean
```

completed successfully.

```text
~/personal/bin/lean-green ~/src/nn-maze-backlog \
  --target NormalNumbers.StonehamSumsBoundary \
  --import NormalNumbers.StonehamSumsBoundary \
  --axioms NormalNumbers.not_isSimplyNormal_stoneham_sub_succ_mul
```

ended `FORMALIZE-TIER GREEN`; the axiom list was
`[Classical.choice, Quot.sound, propext]`.

The final repository gate

```text
~/personal/bin/lean-green ~/src/nn-maze-backlog \
  --import NormalNumbers \
  --axioms NormalNumbers.not_isSimplyNormal_stoneham_sub_succ_mul
```

also ended `FORMALIZE-TIER GREEN` after the full 10,858-job build, with the same axiom list.

## Current crux and next attack

Part 3/L1 is complete.  Continue in kickoff order with L2:

1. Expand
   `stonehamAlpha 3 7 - stonehamAlpha 9 7 + stonehamAlpha 27 7`
   termwise as blocks at right endpoint `3 * 7^(k+1)` (equivalently reindex the source note's
   `3 * 7^k` convention).
2. Prove `7^(k+1) | Φ₆(3^(7^(k+1))) = 3^(2*7^(k+1)) - 3^(7^(k+1)) + 1`; the expected
   elementary input is `x³ + 1 = (x + 1)Φ₆(x)` together with the prime-power lift from
   `7 | 3³ + 1`; no unsupported residue formula is assumed.
3. Bound the positive cyclotomic-block tail and prove the ternary zero window
   `(3 * 7^k, 7^(k+1)]`, then copy the endpoint-frequency contradiction.
4. Add the two audited Maze rows and update `MazeAudit` counts only after L2 is proved.

The kickoff is not complete until L2 and both rows land.
