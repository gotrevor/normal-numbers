# KICKOFF 2026-09-23 — formalize tonight's failures

Worktree `~/src/nn-failures`, branch `wip/failures-2026-09-23`.  Engine Opus/low.  Work in
`src/NormalNumbers/StonehamSixFailure.lean` (new helper files `src/NormalNumbers/StonehamSix*.lean`
are fine) and **append rows** to `src/NormalNumbers/Maze.lean`.  Never touch other files'
statements, `papers/`, `agent-mail/`, other KICKOFFs.

## Target 1: the four sorries (ratified statements, don't change them)

1. `stoneham23_digit_six_eq_zero`: the math is in the module doc.  For position `p = i+1` with
   `3^m < p ≤ 1.1·3^m`, `6^p·Σ_{k≤m}` is an integer divisible by 6 (both exponents `p−k` and
   `p−3^k` are ≥ 1), and `6^p·Σ_{k>m} < 1`, because `6^p ≤ 2^{2.85·3^m}` and the `m+1` term is
   `≤ 2^{−3^{m+1}}`, with a geometric tail.  Reuse `stonehamPartial` and the tail bounds in
   `Stoneham.lean`/`StonehamArith.lean`.  Pick `M` generously.
2. `not_simplyNormal_six_stoneham23`: suppose the limit is 1/6.  Compare `N₁ = 3^m` and
   `N₂ = 11·3^m/10`.  The zero count grows by `≥ N₂ − N₁ − 1` between them, so the ratio at `N₂`
   is `≥ (N₁/6 − o(N₁) + (N₂−N₁−1))/N₂ → (1/6 + 1/10)/(11/10) = 8/33 > 1/6`.  Contradiction.
3. `not_isNormal_six_stoneham23`: instantiate `IsNormal` at the word `[0]`.
4. `oddMultiplierLifting_of_timesThree`: take q = 1 and q = 3 (`Nat.cast_one`, `one_mul`).

## Target 2: Maze rows (append to `register`, follow the file's conventions exactly)

- `"alpha_{2,3} abelian-normal in base 6"`: `.refuted`, `.kernel`, with an `alias
  hall_stoneham_six_abelian := NormalNumbers.Failures.not_simplyNormal_six_stoneham23` in §2
  (add the import).  Reason: forced zero gaps (3^m, 1.16·3^m], so not even simply normal.
  Date 2026-09-23.
- `"x3 abelian lifting"`: `.parked`, `.frozen`, pointer `Failures.TimesThreeLifting`.  Reason:
  the hexSwap example does not refute it (3ξ is not abelian: probe z≈84 at L=1).  A dimension
  count makes a single multiplier implausible; the odd-multiplier version is open.
- `"uniform casting-out law (C1 draft)"`: `.falseAsStated`, `.cited`, pointer
  `branch wip/casting-out: CastingOut.not_castUniform_of_isNormal`.  Reason: a normal number's
  window digit sum mod b−1 has law `1/(b−1) + b^{−L}((b−1)[r=0]−1)/(b−1)`, not uniform.

Build: `lake build NormalNumbers.StonehamSixFailure NormalNumbers.Maze` (warm tree; never run
`lake exe cache get`).  Proof tier: `native_decide`/boosts fine.  Commit each green step.  Done
when `StonehamSixFailure.lean` is sorry-free and Maze builds with the three rows.
