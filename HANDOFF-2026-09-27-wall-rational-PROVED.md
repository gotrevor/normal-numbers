# Handoff: Wall 1949 PROVED — `isNormal_rat_mul_add` sorry-free and axiom-clean

**Date**: 2026-09-27 · **Branch**: `wip/wall-rational`
**Scope**: operator side quest, `sorry-free:src/NormalNumbers/WallRational.lean`.  MET.
The ratified statement `NormalNumbers.isNormal_rat_mul_add` was neither weakened nor renamed.

## Status: DONE

    #print axioms NormalNumbers.isNormal_rat_mul_add
    -- [propext, Classical.choice, Quot.sound]

`src/NormalNumbers/WallRational.lean` has **0 `sorry`s**; the new
`src/NormalNumbers/WallCrux.lean` has 0 too.  `lake build` green, 9274 jobs.
The `Maze.lean` row "Mahler block-occurrence analogue" (which cited Wall 1949) is repointed
from `.cited` to `.kernel`, re-exported as
`NormalNumbers.Maze.hall_mahler_block_occurrence` (axiom-clean).

## The mathematics that closed it

The old handoff recorded that Weyl does not linearise the crux (the Fourier test at frequency
`h` for `(x+M)/B` is the test at the *rational* frequency `h/B` for `x` — the same problem),
and planned a shift-average + Cauchy–Schwarz attack with a character sum over free digits.
That attack works, and a **telescoping identity makes it entirely elementary — no characters,
no Weyl, no measure theory:**

Choose `T` with `q := b^T ≡ 1 (mod B)` (Euler, iterated — `exists_period`; take `T > l`).
Then `divState_shift` collapses to

    r (n + T k) ≡ r n + blockVal b x n (T*k)   (mod B)

and, because `q ≡ 1 (mod B)`, **a base-`q` numeral is congruent to the sum of its base-`q`
digits**.  So the walk position after `k` shifts is literally the leading-`k`-chunk value
`w / q^(K-k) mod B` of the single depth-`T*K` digit block `w = blockVal b x n (T*K)`.
The unbounded-prefix quantity `r n` survives only as the walk's *starting point* `ρ`, and the
estimate is made uniform in `ρ` — that is the whole trick.  What remains is a finite count:
a random walk on `ℤ/B` driven by the base-`q` digits of a uniform `w < q^K`, jointly with a
tag read off one chunk.

## Architecture

**`src/NormalNumbers/WallCrux.lean` (new, self-contained, mathlib only).**  The finite engine.

* `sum_range_mul_split`, `sum_range_div_fiber` — radix splitting of `range (a*d)`
* `card_filter_mod_eq` (exact residue count, via `Nat.succ_div`), `nat_div_bounds`,
  `card_filter_addmod_approx` — `|#{s<M : s+ρ ≡ j} − M/B| ≤ 1`
* `chi`, `Psi` — the walk indicator and its shift average
* `sum_chi_eq` — **exact** first moment (one fiber reduction + one chunk split)
* `sum_chi_pair_eq` — **exact** off-diagonal pair correlation, via the 4-level split
  `u = ((s q + t) q^g + z) q + t'`; the only place `q ≡ 1 (mod B)` is used
* `pair_arith`, `chi_mean_approx`, `chi_pair_mean_approx` —
  `|E χ_k − τ| ≤ q^{−k}`, `|E χ_k χ_{k'} − τ²| ≤ 2(q^{−(k'−k−1)} + q^{−k})`, `τ = #S/(qB)`
* `geom_bound`, `sum_geom_inj`, `inner_sum_bound`, `l2_from_moments`
* `walk_L2_bound`, **`walk_L1_bound`**:
  `(q^K)⁻¹ ∑_{w<q^K} |Psi w − τ| ≤ √(30/K)`, uniformly in `ρ` and `j`

**`WallRational.lean` additions.**  The bridge and the assembly.

* `orbit_shift`, `blockVal_prefix` (shorter block = leading digits of a longer one, via
  `Int.floor_div_natCast`), `blockVal_split`, `blockVal_window`
  (`blockVal b x (n+m) l = (blockVal b x n L / b^(L−m−l)) % b^l`)
* `card_leadFilter`, `tagSet`, `card_tagSet` (`#S = b^(T−l)`), `exists_period`
* **`chi_eq_jointIndicator`** — the identification: along `n, n+T, n+2T, …` the joint event
  `(divState = j, next l digits = v)` *is* `WallCrux.chi` at `w = blockVal b x n (T*K)`
  with starting state `divState … n`
* `shift_sum_diff`, `jointInd`, `shiftAvg_eq_Psi`
* **`jointSum_approx`** —
  `|∑_{n<N} jointInd n − N τ| ≤ T*K + ∑_{n<N} ∑_{ρ<B} |Psi_ρ(W_n) − τ|`.
  The `ρ`-sum is what removes the dependence on the unbounded prefix: the right side is a
  fixed-depth block statistic, so `tendsto_blockAverage` evaluates its limit and
  `walk_L1_bound` bounds it by `B √(30/K)`
* **`tendsto_jointDensity`** — the ε-assembly: given ε pick `K > 30(3B/ε)²`, then
  `T*K/N < ε/3` and `(1/N)∑ F(W_n) < 2ε/3` eventually

## Chain to the headline (all machine-checked, unchanged from the previous handoff)

`tendsto_jointDensity` → `isNormal_add_int_div_coprime` (the depth-`k` b-adic cell of
`(x+M)/B` is a disjoint union of exactly `B` joint (state, block) classes) →
with `exists_smooth_coprime_split`, `isNormal_add_intCast`, `isNormal_intMul`,
`isNormal_div_pow` → `isNormal_rat_mul_add`.

## Notes for whoever picks this up

* Constants are deliberately loose (`30` in `walk_L1_bound`, `14`/`18` in
  `inner_sum_bound`/`l2_from_moments`).  Only `O(K^{-1/2})` matters.
* `WallCrux.walk_L1_bound` is stated abstractly (any `q ≥ 2` with `q ≡ 1 (mod B)`, any tag
  set `S ⊆ range q`).  It is reusable for any "automaton state × future digits" joint
  equidistribution over a coprime modulus, not just Wall's.
* `Maze.lean` now imports `NormalNumbers.WallRational`.
