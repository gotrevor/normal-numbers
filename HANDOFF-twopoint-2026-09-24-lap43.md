# HANDOFF twopoint — lap 43, 2026-09-25

Branch `wip/twopoint-avg`.  File `src/NormalNumbers/TwoPointMertensLower.lean` (appended only;
no existing statement touched).  Build green (8802 jobs); all three new declarations
`#print axioms`-clean.

## Crux this lap
The 🟡 `DelangeMean` axiom.  SESSION WRAP 4 named exactly one remaining brick for part II
(`tendsto_primeSum_div_log`, est. 70%).  It is now a theorem, and the whole of part II closes
with it.

## Landed
1. `sum_weight_tail_le` — the heavy primes (those with `N/p < M₀`) carry Mertens weight
   `≤ log(2M₀) + log 4 + 9`, an absolute constant in `N`.  Proof: the class avoids
   `primesLe (N/M₀)`, so its weight is the difference of the two-sided Mertens bracket
   (`mertens_upper` at `N`, `mertens_lower` at `N/M₀`), and `N ≤ 2M₀·(N/M₀)`.
   This is the one genuinely new ingredient: the argument `N/p` is *small* for the largest
   primes, which the Abel case (lap 37) never had to face.
2. `tendsto_primeSum_div_log` — **the brick**.  `S(N) → L ⟹ (Σ_{p≤N}(log p/p)·S(N/p))/log N → L`.
   `ε`-split at the threshold `M₀`, light primes bounded by `(ε/4)·W(N) ≤ (ε/2) log N` and
   heavy primes by `C₀·D` with `C₀` the finite head max; then `|W(N) − log N| ≤ 9`.
3. `exists_bound_of_tendsto`, `delangeKernelMean_of_converges` — **part II closes**.
   Chaining `tendsto_delangeT_div_log` (lap 37, `T/log N → 0`),
   `norm_delangeT_sub_primeSum_le` (lap 42, the `O(1)` replacement) and the new Toeplitz limit
   gives `(z−1)·L = 0`, hence for `z ≠ 1`, `‖z−1‖ ≤ 1`:

       (∃L, delangeS z → L)  ⟹  DelangeKernelMean z.

   So the residue is now **exactly** the Tauberian statement "`S` converges" — no value to
   identify, no constant to chase.

## What remains on `DelangeMean`
Only Wirsing's theorem proper: that `S(N) = Σ_{n≤N} kernel(n)/n` converges at all.  Every
elementary reduction beneath it is machine-checked (Levin–Fainleib identity, restriction removal,
Abel summation, Mertens both halves, the `S^{(p)} → S` replacement, both Toeplitz limits).
Refuted routes recorded in WRAP 4 (Rankin; a real Gronwall on `‖S‖`) still stand.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%, provable with known techniques 3% (unchanged; no C1 work
  this lap — C1 is pinned as an equivalence, WRAP 4 part A).
- Part II of the Wirsing step: **done**, not an estimate.
- Full `DelangeKernelMean` (convergence of `S`): 15%.

## Next
Attack convergence of `S` directly.  The lever not yet used: `delangeS_mul_log` is an *identity*,
and part II now says its right-hand side is `(z−1)·(Toeplitz average of S)·log N + O(1)`.  So
`S` satisfies an exact self-averaging equation `S(N) = (z−1)·A_N(S) + Abel_N(S)/log N + O(1/log N)`
where both `A_N` and `Abel_N` are regular averages.  Lap 35 refuted a *real-valued* Gronwall on
`‖S‖` (fixed point `θ ≈ u`), but the complex phase of `z−1` was discarded there; the next probe is
whether the two averages' combined multiplier `(z−1) + 1` can be exploited as a genuine complex
contraction on a suitable weighted norm.
