# HANDOFF c3-mrt 2026-09-25 — lap 37: the `K ≥ 3` coprimality obstruction is RESOLVED

**Branch** `wip/c3-mrt`.  Both green: `lake build` (9257 jobs) and
`lake build NormalNumbers.C3MrtJointModulus` (new chain tip).
Prior batons: `-lap36.md` (where this obstruction was found and flagged route-decisive),
`-lap35.md` (the Tao–Teräväinen discovery), `-lap34.md`, `-lap33.md`.

## The obstruction, and why it is not one

Lap 36 flagged: at `K = 2` the moduli of the consecutive integers `n+1, n+2` are automatically
coprime, so the joint progression has modulus `d_0 d_1` and the `1/(d_0d_1)` gain — the thing
that makes the tuple sum absolutely convergent (`pair_mass_le`) — is free.  At `K ≥ 3` it fails:
`n+1` and `n+3` can share the factor `2`, the joint modulus is only `lcm(d_i)`, and the gain
looked lost.  I marked completion confidence down to 55% pending this.

**It is resolved, and the gain survives.**  The key point: a *nonempty* joint progression forces
`gcd(d_i, d_j) ∣ i − j`, so every pairwise gcd is `≤ K`, and the total defect between `∏ d_i` and
`lcm(d_i)` is at most the product of all pairwise gcds.  Hence

    ∏_{i<K} d_i  ≤  lcm(d_i) · K^{K²}     (`prod_le_lcm_mul_pow`)

## New module `src/NormalNumbers/C3MrtJointModulus.lean` (sorry-free, trust-triple)

| name | content |
|---|---|
| `gcd_lcm_dvd_mul_gcd` | `gcd c (lcm a b) ∣ gcd c a · gcd c b` — the gcd/lcm distributivity, in the only direction needed, from `lcm a b ∣ a·b` + mathlib's `gcd_mul_dvd_mul_gcd` (mathlib has no distributivity lemma for this) |
| `gcd_finsetLcm_dvd` | `gcd c (lcm_{j∈s} d_j) ∣ ∏_{j∈s} gcd c (d_j)`, by induction on `s` |
| **`prod_dvd_lcm_mul_gcdProd`** | `∏_{i<K} d_i ∣ lcm(d_i) · ∏_{i<K}∏_{j<i} gcd(d_i,d_j)` — **exact**, by induction on `K` via `gcd_mul_lcm`.  No prime factorisations, no valuations |
| `gcd_dvd_sub_of_dvd_shift` | a nonempty joint progression forces `gcd(d_i,d_j) ∣ i − j` |
| **`prod_le_lcm_mul_pow`** | `∏_{i<K} d_i ≤ lcm(d_i) · K^{K²}` |

## Consequence for the named input — the one shape change this forces

The factor `K^{K²}` is a constant depending on `K` alone.  At `K = D_N ≍ log log log N` it is
`exp(O((log log log N)² · log log log log N)) = (log log N)^{o(1)}`, negligible against the
`D = 1` rung's `(log N)^{-a}`.  So:

> **`QuantDepthElliott`'s constant budget must be widened from `b^{κD}` to a general `C(D)`
> subject to `C(D_N) · η(N) → 0`.**

That is a change to the shape of a Prop **we** state (`C3MrtSchedule.lean`), not a new analytic
input, and the `log log log` schedule satisfies it with enormous room.  `weylLambertTwist_of_
quantDepthElliott`'s proof already only uses `Tendsto (fun N => llProxy N ^ m * η N) atTop (𝓝 0)`
for the relevant `m`, so the generalisation is a local edit there — but **do not touch it until
the `K`-fold assembly needs it**, and never weaken `weylLambertTwist_holds` or `conjC3`.

## NEXT

1. `tuple_mass_le`: `∑_{(d_i) ≤ Y} (∏_i ‖sqfW z_i (d_i)‖) / lcm(d_i) ≤ K^{K²} · ∏_i sqfWMass z_i`,
   restricted to tuples with nonempty joint progression (the others contribute `0`, by the
   `K`-fold analogue of `joint_progression_eq_empty_of_not_coprime`).  Combine
   `prod_le_lcm_mul_pow` with `Finset.sum_prod_piFinset`
   (mathlib, `Algebra/BigOperators/Ring/Finset.lean:161`) to split the tuple sum into a product
   of one-dimensional sums.  This is the `K`-fold `pair_mass_le`, and lap 37 is exactly what
   makes it true.
2. `multi_truncation_bound`: iterate `offset_truncation_bound_of_mass` `K` times.
3. `K`-fold CRT: the joint progression, when nonempty, is one class mod `lcm(d_i)` —
   `exists_joint_class` generalised; `prod_dvd_lcm_mul_gcdProd` is not needed for that, only
   `Nat.modCast`/CRT-for-lcm.
4. Then the per-tuple rung bound and the ε-chase, mirroring laps 29–33.

## Still refuted — DO NOT RETRY

Unchanged, plus: quantifying `F` outside the `K`-induction (lap 36); and **do not** attempt the
prime-valuation route to `prod_le_lcm_mul_pow` — the `gcd_mul_lcm` induction above is exact and
needs no factorisations.

## Confidence

* `K ≥ 3` assembly completable: **≈ 75%** (back up from 55%; the obstruction lap 36 found is
  resolved and cost only a `K`-dependent constant that the schedule absorbs).
* leaf TRUE ≈ 97%; leaf PROVABLE with known techniques ≈ 27% (up slightly: the last structural
  surprise on the `K`-fold path turned out benign).
