# HANDOFF twopoint — lap 30: the local (CRT) kernel of directive step 3

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointShiftLocal.lean` (sorry-free,
trust-triple), import added to `src/NormalNumbers.lean`.

`DIRECTION.md` step 3: "restricted to prime factors in `(J, z]` the summands are jointly
CRT-independent (primes `> K` divide at most one shift), variance `≍ log log z`".  This lap
proves the arithmetic kernel of that sentence — exactly, not up to constants.

## The advance
| result | content |
|---|---|
| `eq_of_dvd_two_shifts` | `r ≥ K`, `r ∣ a+k`, `r ∣ a+k'`, `k,k' < K` ⇒ `k = k'` |
| `card_filter_shift_dvd_le_one` | a prime `r ≥ K` divides **at most one** of the `K` forms `pn+1+k` |
| `card_solutions_eq_one` | `#{n < r : r ∣ pn+c} = 1` exactly, for `r` prime, `r ∤ p` (via `ZMod r` a field) |
| `sum_card_shift_hits` | the double count `Σ_{n<r} #{k<K : r ∣ pn+1+k} = K` |
| **`card_hit_eq`** | `#{n < r : ∃k<K, r ∣ pn+1+k} = K` **exactly**, for `r` prime, `r ∤ p`, `K ≤ r` |
| **`card_hit_pair_le`** | the pair uses at most `2K` of the `r` residues |

So for every prime `r > K` the `p`-side "uses" exactly a `K/r` fraction of residues and the two
sides together at most `2K/r`; and, crucially, on the hit residues only ONE of the `K` summands
`ω(pn+1+k)` sees `r`.  That is precisely the disjoint-support independence the variance read
needs: at primes in `(K, z]` the digit sum `Σ_k b^{−k−1} ω(pn+1+k)` is a sum over disjoint prime
supports, so its local contributions are genuinely independent (no shift shares a large prime).

## What this already tells us about the route (recorded, no re-derivation)
Total mass of primes in `(K, z]` used by the pair is `Σ_{K<r≤z} 2K/r ≍ 2K log(log z / log K)`.
With `K = K(M) ≍ log_b log M` (the cheapest schedule admitted by `pairDecorr_of_unweighted`,
lap 29) and `z` any power of `M`, that is `≍ log log M · log log M` — *divergent*.  The
independence is real but the large-prime part carries unbounded `ℓ¹` mass, so the small-prime
variance alone does NOT close the leaf by a triangle inequality.  This is the same shape as the
lap-26 finding for `PairDecoupleGrowing` and confirms it at the `2K`-form level: the obstruction
is a *cancellation* statement in the large primes, i.e. genuinely Elliott.

## The run so far
* lap 28 `92ede26` — `DelangeKernelTail` unconditional for `‖z−1‖<1`; `DelangeMean` reduced to one
  residue for `‖t‖_{ℝ/ℤ} < 1/6`.
* lap 29 `ab283df` — `pairDecorr_of_unweighted`: the peel weight drops at growing depth; the crux
  is an **unweighted** `2K(M)`-point Elliott correlation.
* lap 30 (this) — the exact local counts for those `2K` forms.

## Next
Assemble: state `MultiElliottGrowing`'s split at a prime cut `z` as a named `Prop` pair
(small-prime factor, large-prime remainder), prove the small-prime factor tends to `0` using
`card_hit_eq` + the existing `pairLocalFactor`/Mertens engine (`TwoPointGrowingCut.lean`,
`periodMean_pair_tendsto_zero`), and name the large-prime remainder as the sole residue.  That
would be the `2K`-form analogue of lap 26 and would pin the route's obstruction at the new,
weight-free surface.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%, provable with known techniques 3% (unchanged).
- Small-prime factor of `MultiElliottGrowing` provable in 1–3 laps: **60%**.
