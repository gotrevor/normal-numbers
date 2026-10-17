# Literal Bailey--Borwein pairs lap 12 -- Fourier loss and exact pair state (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-17-bb-literal-pairs.md` in order. The host gate remains
`sorry-free:src/NormalNumbers/StonehamPairsNormal.lean`. Neither headline statement,
`VandeheyThm51`, nor any Theorem A statement in `StonehamSumsNormal.lean` changed. The target
file itself is unchanged and its two original headline sorries remain.

## Concrete crux advance

`StonehamPairsDistinct.lean` now connects lap 11's exact literal-pair divisor to the rational
orbit state consumed by the analytic engine.

- `prime_pow_sub_padicValInt_dvd_mul_den` proves the generic multiplier-loss lemma:
  `p^E | q.den` implies `p^(E - padicValInt p h) | (h*q).den` for nonzero integer `h`.
  The proof uses reducedness of `q`: once `E > v_p(h)`, `p` divides the denominator and hence
  cannot divide the numerator, so the rational valuation identity gives the exact loss bound.
- `stonehamState_pair_one_eq` identifies the `Fin 2` state with coefficients
  `![h, sigma*h]` and family data `![c1,c2]`, `![1,1]` as `h` times the explicit signed pair of
  truncated Stoneham families.
- `prime_pow_sub_padicValInt_dvd_stonehamState_pair_one_den` packages those two facts into a
  reusable state-level transfer.
- `prime_pow_max_sub_padicValInt_dvd_stonehamState_pair_add_den_of_depth_ne` and its `_sub_`
  companion combine the transfer with lap 11's exact unequal-depth theorem. For both literal
  signs the actual Fourier state has denominator divisible by

  ```text
  p^(max(depth1, depth2) - padicValInt p h).
  ```

No new `sorry`, axiom, native computation, statement change, or heartbeat override was
introduced.

## Verification

Narrow check:

```text
lake env lean src/NormalNumbers/StonehamPairsDistinct.lean
```

It exited zero; only FORMALIZE-tier `letI` style suggestions were reported.

Real target/axiom gate:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-bb-pairs \
  --target NormalNumbers.StonehamPairsNormal \
  --import NormalNumbers.StonehamPairsNormal \
  --axioms NormalNumbers.StonehamPairsNormal.prime_pow_sub_padicValInt_dvd_mul_den \
  --axioms NormalNumbers.StonehamPairsNormal.stonehamState_pair_one_eq \
  --axioms NormalNumbers.StonehamPairsNormal.prime_pow_max_sub_padicValInt_dvd_stonehamState_pair_add_den_of_depth_ne \
  --axioms NormalNumbers.StonehamPairsNormal.prime_pow_max_sub_padicValInt_dvd_stonehamState_pair_sub_den_of_depth_ne
```

It completed 8,779 jobs and ended `FORMALIZE-TIER GREEN`. All four declarations print exactly
`[Classical.choice, Quot.sound, propext]`. The target reports only its two unchanged headline
sorries.

## Current blocker

The distinct-class branch now has a denominator divisor for the exact state at every sufficiently
large time, but it is not yet converted to the real power inequality
`StonehamStateDenPowerLower`.

The remaining distinct-class work is quantitative packaging:

1. prove the eventual entry facts `1 <= Nat.log c_i n` and the automatic
   `c_i^j <= n` hypotheses for all `j <= Nat.log c_i n`;
2. use `exists_prime_logSlope_ne_of_not_stonehamPairMulDep` and
   `eventually_natLog_depth_ne` to select the fixed prime and obtain the state divisor eventually;
3. lower-bound the selected maximum depth by a positive multiple of `log n`, absorb the fixed
   subtraction `padicValInt p h` and the finite initial segment into an arbitrary positive
   constant, and state the result as `StonehamStateDenPowerLower` for both signs;
4. feed it to `stonehamCombination_mean_tendsto_of_powerLower` and the Weyl wrapper.

After that the multiplicatively dependent/same-class branch remains: align `c_i = g^s_i` at
primitive `g`-depth and apply the already-proved never-silent/resultant machinery to the combined
tail.

## Next highest-value attack

Prove one real-growth lemma directly from `natLog_mul_log_base_error`: for `2 <= c`, prime `p`,
and positive `a = c.factorization p`, obtain constants `rho > 0`, `C > 0` such that

```text
n^rho <= C * p^(a * Nat.log c n - H)
```

for every `n` (absorbing the finite prefix), with fixed `H`. Then combine it with the new
state-divisor wrappers and `Nat.le_of_dvd` to produce the distinct-class
`StonehamStateDenPowerLower`. Avoid reintroducing a depth-gap estimate: the maximum of the two
depths already contains the needed logarithmic growth.
