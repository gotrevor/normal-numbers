# HANDOFF twopoint — lap 29: the peel weight DROPS at growing depth

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointDepthPeel.lean` (sorry-free,
trust-triple), import added to `src/NormalNumbers.lean`.

`DIRECTION.md` CURRENT DIRECTIVE (branch `wip/twopoint-avg`), mandated move **2**:
"Iterate the peel to `K ≈ log_b log M` … formalise that truncation first — it is the one
prerequisite every route needs."  **Done this lap.**

## The advance
At a FIXED depth `K` the exact factorisation `phase_pairTail_factor` leaves a unit-modulus weight
`peelWeightAt = e(t b^{−K}(θ_{pn+K} − θ_{qn+K}))`, and the leaf at fixed depth
(`MultiElliottWeighted`) is therefore a *weighted* correlation — not the object the literature
speaks about.  Letting the depth grow removes the weight:

| result | content |
|---|---|
| `abs_shiftPairTail_le` | `\|θ_{pn+K} − θ_{qn+K}\| ≤ (log₂(pn+K+1)+1) + (log₂(qn+K+1)+1)` |
| `norm_phase_pairTail_sub_digitTrunc` | pointwise weight-removal error `≤ 4π\|t\| b^{−K}·(carry bound)` |
| `peelBound b p q K M t` | the explicit uniform budget on `[0,M)` |
| `norm_fullMean_sub_le` | the same bound on the mean over `n < M` (monotonicity of `log₂`) |
| `MultiElliottGrowing b p q t K` | the **unweighted** `2K(M)`-point root-of-unity correlation |
| **`pairDecorr_of_unweighted`** | `PairDecorr b t` from `MultiElliottGrowing` + `peelBound → 0` |
| `tendsto_peelBound_id` | the schedule `K(M)=M` meets the budget — the criterion is NOT vacuous |

**Why this matters for the route.**  The crux is now stated with no `peelWeight` anywhere: a pure
Elliott-type correlation of `ζ^ω` along the `2K(M)` linear forms `pn+1+k`, `qn+1+k`, `k < K(M)`,
with `K(M)` free (any schedule with `b^{K(M)} ≫ log M` works; `K ≍ log_b log M` is the cheapest).
That is exactly the comparison surface against Tao 2016 / MRT 2015, and it is the prerequisite
directive step 3 (the sieve/variance read on the small-prime part) consumes.

## Also this run
Lap 28 (`92ede26`): `DelangeKernelTail` proved unconditionally for `‖z−1‖ < 1`
(`TwoPointDelangeTail.lean`), so for `‖t‖_{ℝ/ℤ} < 1/6` the 🟡 `DelangeMean` axiom rests on the
single residue `DelangeKernelMean`.

## Next (directive step 3)
Split `MultiElliottGrowing` at a prime cut `z`: for prime factors in `(K(M), z]` the `2K` forms
are pairwise CRT-independent (a prime `> K` divides at most one of `pn+1+k`, so the local factors
decouple), variance `≍ log log z`, giving `(log z)^{-c}` on the small-prime part.  The LARGE-prime
part is where it becomes Elliott.  A lap that pins that as `small-prime part alone suffices` or
`⟺ named open statement` is a success.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%, provable with known techniques 3% (unchanged).
- Directive step 3 (small-prime variance read) reachable in 2–4 laps: **50%**.
