# Stoneham sums normal — lap 2 (2026-10-16)

## Concrete advance

The target `src/NormalNumbers/StonehamSumsNormal.lean` still has exactly one sorry, the frozen
Theorem A declaration `isNormal_stonehamCombination`, but its load-bearing elementary denominator
infrastructure is now in Lean.

- Defined the exact truncated rational orbit state `stonehamState` and entry count `stonehamK`.
- Proved `le_stonehamK_iff`, characterizing the terms which have entered by time `n`.
- Proved paper Lemma 2 as `stonehamState_add_of_K_eq`: whenever all entry counts stay fixed,
  `S_(s+j) = b^j S_s` exactly.
- Defined the explicit common denominator
  `stonehamStateDen L c m n = L * ∏ i, c i ^ stonehamK c m i n` and proved:
  - `stonehamState_eq_int_div_den`: the state has an integer numerator over that denominator;
  - `stonehamState_den_dvd`: its reduced denominator divides the explicit denominator;
  - `stonehamStateDen_le`: the explicit denominator is at most `L * n^r`;
  - `stonehamState_den_coprime`: its reduced denominator is coprime to `b`;
  - `prime_dvd_stonehamState_den`: every prime in it divides `L` or one of the fixed `c i`.

Thus the easy/common-denominator, upper-growth, coprimality, fixed-smooth-support parts of paper
Lemma 3 are closed, and the exact kick-free dynamics needed by each long-piece Vandehey application
is closed.

## Verification

Run in this lap:

```text
lake env lean src/NormalNumbers/StonehamSumsNormal.lean
```

Result: success; the only warning is the one pre-existing disclosed sorry in
`isNormal_stonehamCombination`.

Repository gate:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-stoneham-sums \
  --target NormalNumbers.StonehamSumsNormal
```

Result: `✅ FORMALIZE-TIER GREEN` (8762 jobs).  `rg -n "sorry"
src/NormalNumbers/StonehamSumsNormal.lean` reports exactly line 360, Theorem A.

## Current blocker

The next route-decisive obligation is paper Lemma 3's lower bound for the *reduced* denominator.
For an active family `i`, a prime `ℓ | c i`, and `K = stonehamK c m i n`, one must formalize the
unique minimum valuation at the newest term and show

```text
padicValRat ℓ (stonehamState b L c m p n)
  ≤ padicValInt ℓ (p i) - K * padicValNat ℓ (c i).
```

The other families have nonnegative `ℓ`-valuation by pairwise coprimality.  Converting these local
bounds into the product estimate
`∏ i, c i ^ K_i(n) ≤ state.den * ∏ i, |p i|` yields the required polynomial lower bound.
This is hard but internal mathematics, not an operator/external blocker.

## Next highest-value attack

1. Prove a generic finite-sum lemma for a unique strict minimum of `padicValRat`; mathlib provides
   `padicValRat.add_eq_of_lt` and `padicValRat.lt_add_of_lt`.
2. Apply it to the newest term in one Stoneham family, then add the other pairwise-coprime families.
3. Convert the valuation inequalities to the product divisibility/lower bound for the reduced
   denominator.
4. After Lemma 3, prove the real tail estimate (Lemma 1), then the kick partition and Weyl assembly.

Do not revisit `vandeheyCor12_of_thm51`: it remains green and already discharged the uncertain
analytic input.
