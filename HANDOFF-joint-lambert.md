# HANDOFF — joint Lambert: SHARED BINARY TAIL proved

Date: 2026-09-27 (lap C).  Operator objective at the top of `DIRECTION.md`
(tail-control stage, authorized after `7dc2522`).

## Result

Both scoped targets are **proved, sorry-free**:

* `NormalNumbers.JointLambert.exists_joint_small_tail` — new
  `src/NormalNumbers/JointLambertTail.lean`, the frozen contract verbatim.
* `NormalNumbers.JointLambert.base_tail_le_half_binary_tail` — the base majorant, in the
  new `src/NormalNumbers/JointLambertTailBounds.lean`.
* plus `exists_joint_small_tail_all_bases`, the combined form the digit assembly will
  consume: one `n`, base-`b` tail `< ε/2` for **every** integer `b ≥ 2` at once.

```
#print axioms NormalNumbers.JointLambert.exists_joint_small_tail
#print axioms NormalNumbers.JointLambert.base_tail_le_half_binary_tail
#print axioms NormalNumbers.JointLambert.exists_joint_small_tail_all_bases
#print axioms NormalNumbers.JointLambert.sum_tau_progression_le
  -- all [propext, Classical.choice, Quot.sound]
```

`lake build` green; both modules in the root build (`src/NormalNumbers.lean`).  The four
frozen files are byte-identical to their pins (`git diff` empty): `JointLambertStatement`
vs `78e6048`, `JointLambertEncodingProof` vs `7f05cb2`, `JointLambertArithmetic` vs
`566586a`, `JointLambertPrimeSelection` vs `7dc2522`.  `AGP` and `PrimeIntervalSupply` are
unchanged and are still *hypotheses* — no new analytic input, no tail hypothesis.

## The contract, as proved

Given `hagp : AGP`, `hpis : PrimeIntervalSupply`, `c ≥ 2`, `a ≥ 2`, `r ≥ 1`, any real
`ε > 0` and any natural cutoffs `K`, `N`, there exist `k n : ℕ` with

* `K ≤ k`, `r < k`, `1 ≤ n`, `N ≤ n`;
* `c^(j+1) ∣ τ(n+j)` for every `j < k` with `j ≠ r`;
* `τ(n+r) = 2a` exactly;
* `∑' t, τ(n+k+t)/2^(k+t) < ε`.

`τ` is `SwingC2.tau`, honest divisor cardinality.  Summability is proved
(`summable_binary_tail`, `summable_tau_div`, `summable_base_tail`) so no `tsum` can mask a
divergent series.  And for every `b ≥ 2`,
`0 ≤ ∑' t, τ(n+k+t)/b^(k+t+1) ≤ (binary tail)/2`.

## How it is proved

### 1.  `JointLambertTailBounds.lean` — the elementary §3 layer

* `tau_le_two_mul_card_dvd_le`: divisor pairing at `H`.  For `0 < n ≤ H²`,
  `n.divisors ⊆ S ∪ S.image (n / ·)` with `S = {h ∈ [1,H] : h ∣ n}` (a divisor `d > H`
  has cofactor `n/d ≤ H`, else `n > H²`), so `τ(n) ≤ 2·#S`.
* `card_prog_dvd_le`: for `(h, A) = 1`, `h ∣ u+mA` and `h ∣ u+m'A` give `h ∣ (m−m')A`
  hence `h ∣ m−m'` (`Nat.Coprime.dvd_of_dvd_mul_right`), so the solutions lie in one
  residue class mod `h`; `m ↦ m/h` injects them into `range (M/h+1)`.
* `card_prog_dvd_eq_zero`: for `(u, A) = 1` and `(h, A) > 1`, `minFac (gcd h A)` would
  divide both `u` and `A`, so there are *no* solutions.  This is exactly where the
  coprimality of the progression is spent.
* **`sum_tau_progression_le`** — the §3 estimate
  `∑_{m<M} τ(u+mA) ≤ 2M(1+log H) + 2H` for `u > 0`, `(u,A)=1`, `H ≥ 1`,
  `u+mA ≤ H²` (`m<M`).  Double counting (`Finset.card_filter` + `Finset.sum_comm`) swaps
  `m` and `h`; then `M/h+1` per `h`; then `∑_{h≤H} 1/h = harmonic H ≤ 1 + log H`
  (`sum_inv_Icc_eq_harmonic` + mathlib `harmonic_le_one_add_log`).
* `tau_le_self`, `summable_affine_geometric`, `summable_tau_div`,
  **`tsum_tau_div_le`**: `∑' t, τ(N₀+t)/2^t ≤ 2N₀ + 2` — the crude far-range tool
  (`tsum_geometric_two` + `tsum_coe_mul_geometric_of_norm_lt_one`).
* `pow_eight_le_two_pow` (`k^8 ≤ 2^k` for `k ≥ 44`, by induction with
  `44(k+1) ≤ 45k` and `45^8 ≤ 2·44^8`) and **`poly_eight_le_two_pow`**:
  `m + C k^8 + C ≤ 2^k` once `k ≥ 2(6562C + m + 45)`, proved by splitting
  `2^k ≥ (2^{k/2})²` and using `k^8 ≤ (3·(k/2))^8 = 6561 (k/2)^8 ≤ 6561·2^{k/2}`.
  **This is what makes every "for `k` large" step proved rather than assumed.**
* `window_le_pow_six`, `base_tail_le_half_binary_tail`, and three non-vacuity anchors
  (`tau_small_values`, `sum_tau_progression_le_nonvacuous`,
  `tau_le_two_mul_card_dvd_le_nonvacuous`, all `decide +kernel`) kept as persistent tests.

### 2.  `JointLambertTail.lean` — the assembly

1. **`ε` first.**  `exists_pow_lt_of_lt_one` gives `m₀` with `(1/2)^m₀ < ε/2`.  The cutoff
   handed to `exists_joint_prime_candidates` is
   `K' = max(max K N, max (2(6562·6+(m₀+2)+45)) (2(6562·Cn+45)))` with `Cn = 320·2^m₀`.
   So `ε` is fixed *before* the prime-selection height, and the two thresholds are
   exactly the hypotheses of `poly_eight_le_two_pow`.
2. **Schedule bookkeeping.**  `U = 2^(k⁴)`, `X = U⁴`, `H = U³`, `Z = U⁶`, `L = 2^k`,
   `M = X/B + 1`.  `hHM : H ≤ M` (from `H·B ≤ U³·U = X`, `Nat.le_div_iff_mul_le`) — this
   is the whole reason for `X = U⁴`, `H = U³`.  `hnZ : R + mA + i ≤ Z = H²` for `i ≤ L`,
   from `A = QB`, `Q, B ≤ U`, `m ≤ X/B`, and `window_le_pow_six` (`U ≥ 4`).
3. **Near range `k ≤ j < L`.**  The coprimality clause `(R+j, A) = 1` supplied by
   `exists_joint_prime_candidates` feeds `sum_tau_progression_le` row by row with
   `u = R + (k+t)`.  Summing the rows against `2^{-(k+t)}` (geometric partial sum `≤ 2`)
   gives `∑_{m<M} near(m) ≤ S·(2/2^k)` with `S ≤ M(6k⁴+4)` — using `log H ≤ 3k⁴`
   (`log 2 ≤ 1`) and `H ≤ M`.
4. **Pigeonhole.**  `Finset.exists_le_of_sum_le` over the candidate set `C`
   (`#C ≥ M/(16k⁴) > 0`, the count proved last lap) gives a candidate `m` with
   `near(m) ≤ 320 k⁸ / 2^k ≤ (1/2)^m₀`, since `Cn·k⁸ ≤ 2^k`.
5. **Far range.**  `Summable.sum_add_tsum_nat_add D` (`D = 2^k − k`) splits the `tsum`
   exactly at `L`; the tail reindexes to `(1/2^L)·∑' i, τ((n+L)+i)/2^i ≤ 4Z/2^L`, and
   `2 + 6k⁴ + m₀ ≤ 2^k` makes that `≤ (1/2)^m₀`.
6. Total `< ε/2 + ε/2`.  `N ≤ n` comes from `N ≤ K' ≤ k ≤ 2^k < R ≤ n`.

## Exact next dependency

Tail control is discharged.  What remains for
`JointLambertDisjunctivity` — and it is **not** claimed here:

1. **The common-offset digit identity.**  Wire `c^(j+1) ∣ τ(n+j)` (`j ≠ r`, `j < k`) and
   `τ(n+r) = 2a` through `evenEncoding` (proved, `7f05cb2`) to the digit cylinders of
   *every* base simultaneously, with `c = lcm(bases)` entering through
   `divisor_count_dvd_of_dvd`.  The tail majorant just proved is the ingredient that makes
   the unprescribed slots harmless: `exists_joint_small_tail_all_bases` hands the assembly
   one `n` with a base-`b` tail below `ε/2` for every `b ≥ 2` at once, so the same offset
   pins the digit of `E_b` in all coordinates.  This is the next Lean target.
2. **Arbitrarily late occurrences** — already immediate: `K` and `N` are both arbitrary in
   `exists_joint_small_tail`.

Do **not** claim the full joint Lambert theorem: item 1 remains.

## Why this run is finished

The scoped objective is met: `exists_joint_small_tail` **and** the base-majorant corollary
are proved and axiom-clean, `grep -c sorry` is 0 in both new modules, and the four frozen
files are untouched.  The remaining `sorry`s in `src/` are the same pre-existing,
designated-open holes listed in the previous handoff (`SwingC2`, `SwingC1Log`,
`SwingC3Rotation`, `PairDecoupleProve` — a conjecture, not a gap — `MahlerDriftOne`,
`PrimeLambertOscillation`), all explicitly out of scope by the operator objective.  So the
repo-wide sorry gate is unsatisfiable here by construction; the host scoped predicate is
the one that should recognise completion.
