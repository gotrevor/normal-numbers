# HANDOFF 2026-09-24 — failures kickoff DONE + the abelian separation closed

Branch `wip/failures-2026-09-23`, worktree `~/src/nn-failures`.  Full `lake build` green
(9171 jobs) at every commit below.

## 1. Scoped objective: `KICKOFF-2026-09-23-failures.md` — COMPLETE

`src/NormalNumbers/StonehamSixFailure.lean` is **sorry-free**; all four theorems
`[propext, Classical.choice, Quot.sound]`.

* `stoneham23_digit_six_eq_zero` — forced base-6 zeros on `[3^m, 11·3^m/10)` for `m ≥ 2`.
  Head `6^p·Σ_{k≤m} = Σ_j 2^{p−3^{j+1}}·3^{p−(j+1)}`, both exponents `≥ 1`, so `6 ∣` it;
  tail `< 1` from the integer margin `two_mul_six_pow_lt_two_pow : 2·6^p < 2^{3^{m+1}}`.
  **Reusable trick:** that margin is proved by raising both sides to the 10th power and
  quoting `6^10 = 60466176 < 67108864 = 2^26` against `10p ≤ 11·3^m`.  No `Real.log`, no
  `log₂ 6 ≈ 2.585` — one `norm_num` fact replaces the whole transcendental estimate.
* `not_simplyNormal_six_stoneham23` — two-scale contradiction at `N₁ = 3^m`, `N₂ = 11·3^m/10`,
  `ε = 1/100`.
* `not_isNormal_six_stoneham23`, `oddMultiplierLifting_of_timesThree` — immediate.
* `Maze.lean` carries the three required rows plus the new kernel alias
  `hall_stoneham_six_abelian`.

## 2. Then: `AbelianBinaryExample.lean` is sorry-free — the separation is unconditional

`exists_abelianNormal_not_normal` (some binary sequence is abelian-normal but not normal)
now has axioms `[propext, Classical.choice, Quot.sound]` with nothing open beneath it.  The
one open leaf was `isAbelianNormalTwo_xiBits`.

**The insight.**  `hexSwap` is *not* injective — `2` and `3` both map to `3` — so the nibble
law is genuinely non-uniform, and that is exactly what kills normality (`0011` has frequency
`5/64`).  What survives is sharper and is what abelian normality reads:

> `nibCount_binomial`: over **every** contiguous bit interval `[lo,hi) ⊆ [0,4)` of a nibble,
> the full nibble included, the one-count of `hexSwap d` is Binomial(`hi−lo`, 1/2) as `d`
> ranges over `{0,…,15}`.

Proper intervals: the four swaps `2↔3, 5↔4, 11↔10, 12↔13` move each digit inside its own
2-bit *quadrant* and its own 2-bit *residue class*, so every proper contiguous bit-window
stays uniform.  Full nibble: the swaps permute popcounts `{1,2}→{2,2}`, `{1,2}→{1,1}`,
`{2,3}→{2,2}`, `{2,3}→{3,3}`, preserving the multiset `{1,1,2,2,2,2,3,3}`.  One `decide` over
125 `(lo,hi,t)` triples.

**The assembly.**  `winCountK_binomial` (induction on `S`): peel the leading nibble, apply the
nibble law to its contiguous bit interval, the IH to the rest, convolve with Vandermonde
(`Nat.add_choose_eq`) over the antidiagonal — among the `16^S` hex words, exactly
`16^S·C(L,j)/2^L` have window one-count `j`, for **every** offset `r < 4`.  Then
`onesCount_xiBits` identifies the bit-window count with `winPc` of the hex block (take
`S = L/4 + 2`), and `tendsto_blockEvent` (base-16 normality of `c`) hands the density to the
i.i.d. uniform hex model.

Supporting infrastructure added in the same file and reusable: `swapBit`, `nibPc`, `nibCount`,
`winPc`, `winCountK`, `indicator_add_eq`, `sum_range_pow_succ_split` (leading-digit reindexing
of `range (b^(S+1))`), `sum_sum_indicator_add`, `winPc_cons`.

## 3. State of `src/`

The only remaining `sorry`s are the two DIRECTION.md designates as off-limits:
`PrimeLambertOscillation.lean:95` and `MahlerDriftOne.lean:380`.

## 4. NEXT

* `TimesThreeLifting` is PARKED/frozen — no proof and no refutation; the hexSwap example does
  not refute it (3ξ is not abelian: probe `z ≈ 84` at `L = 1`).  `OddMultiplierLifting` (~70%)
  now provably follows from it (`oddMultiplierLifting_of_timesThree`); the cheap next move is
  a literature sweep for the all-odd-multiplier statement, which may be classical.
* Consider promoting `exists_abelianNormal_not_normal` into `Headline.lean` / `STATUS.md` — it
  is now a finished unconditional theorem, not a campaign.
