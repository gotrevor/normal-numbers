# Maze backlog review lap 10 — full tied-depth Stoneham cancellation (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-16-maze-backlog.md` in order. Parts 1, 2, and 3/L1 remain
complete. Part 3/L2 remains open exactly at `StonehamThreeSevenPairwiseNormal`, after lap 7
corrected the earlier statement-faithfulness failure. This is hard but in-scope mathematics,
not an operator blocker.

## Adversarial review and route correction

The lap-9 handoff proposed isolating the tied newest pair and showing that every older kick has
strictly larger 7-adic valuation. That claim is false in the needed generality: lap 8 bounds the
newest cancellation loss by a fixed number `D`, which can exceed one, while the immediately
older cleared term gains only one factor of seven. Thus bounded newest loss does not by itself
create a strict minimum.

The correct mechanism is simultaneous phase comparison. For every `k ≤ K`, Euler's theorem
gives

```text
3^(n - m·7^k) ≡ 3^(n - m·7^K)  (mod 7^(k+1)).
```

After common-denominator clearing multiplies the depth-`k` term by `7^(K-k)`, every comparison
error is divisible by `7^(K+1)`. The full history is therefore congruent to the newest phase
times `G_K = 1 + 7 + ⋯ + 7^(K-1)`, and `G_K` is a 7-adic unit. This controls all older
kicks together, including the formerly problematic immediately older term.

## Concrete crux advance

`StonehamSumsBoundary.lean` now proves the complete tied-depth arithmetic chain:

- `stoneham_seven_phase_modEq`: the phase congruence above;
- `seven_pow_succ_dvd_weightedSum_sub`: the generic common-denominator summation step;
- `stonehamSevenGeom_not_seven_dvd`: the geometric coefficient is a 7-adic unit;
- `padicValInt_stonehamWeightedSum_le`: a newest-coefficient valuation bound survives the
  complete weighted history;
- `padicValInt_stonehamPairWeighted_le`: the two-family transfer theorem;
- `padicValInt_stonehamPairWeighted_le_one` and `_two`: full-history bounds for the exponent
  gaps occurring among `m = 1, 2, 3`, using lap 8's quadratic norms.

The last two theorems include every kick from depths `1` through `K`; they are not merely leading
term estimates. The parked Maze row and `MazeAudit` links now state and audit this sharper
checkpoint.

## Verification

The edited module check succeeded:

```text
lake env lean src/NormalNumbers/StonehamSumsBoundary.lean
```

The repository's real scoped gate was run exactly as follows:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-maze-backlog \
  --target NormalNumbers.MazeAudit \
  --import NormalNumbers.StonehamSumsBoundary \
  --axioms NormalNumbers.stoneham_seven_phase_modEq \
  --axioms NormalNumbers.padicValInt_stonehamPairWeighted_le_one \
  --axioms NormalNumbers.padicValInt_stonehamPairWeighted_le_two
```

It completed 10,470 jobs and ended `FORMALIZE-TIER GREEN`. All three audited declarations have
exactly `[Classical.choice, Quot.sound, propext]` as their axiom list. Reported `sorry`s are
pre-existing proof debt outside the edited module.

## Current blocker

`StonehamThreeSevenPairwiseNormal` is still open. The tied-depth numerator estimate is now
complete, but `StonehamStateDenLinearLower` still needs the unequal-depth case and the exact
connection from the integer weighted sums to the reduced denominator of the rational state.
This is not a `box stuck` condition.

## Next highest-value attack

1. Prove that for `m ∈ {1,2,3}` the two values `stonehamK 7 m n` differ by at most one.
2. Treat depths `K` and `K-1`. After clearing to denominator `7^K`, the phase-replaced numerator
   has shape `U = A·G_K + 7C·G_(K-1)`, hence

   ```text
   6U = 7^K(A+C) - (A+7C).
   ```

   Use phase congruence to control the error and apply the gap-one or gap-two quadratic-norm
   argument to the newest coefficient with one coefficient scaled by seven. Cover both depth
   orientations.
3. Rewrite the two-family `stonehamState` over the common denominator, include the fixed loss
   from clearing arbitrary rational coefficients, and derive `StonehamStateDenLinearLower` for
   exponent gaps one and two.
4. Feed those bounds to `stonehamCombination_mean_tendsto_of_linearLower`, clear rational
   coefficients, prove the three pairs, discharge `StonehamThreeSevenPairwiseNormal`, and only
   then restore the Maze row to `.refuted/.kernel`.
