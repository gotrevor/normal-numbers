# HANDOFF twopoint — lap 34: the Levin–Fainleib working inequality, explicit

Branch `wip/twopoint-avg`.  Extends `src/NormalNumbers/TwoPointDelangeLF.lean` (sorry-free,
trust-triple).

## Crux
`DelangeKernelMean z : Σ_{n≤N} h_z(n)/n → 0` — the last dischargeable residue of the 🟡
`DelangeMean` axiom.

## The advance
Lap 33 gave the exact LF identity with the awkward coprimality restriction `p ∤ m` in the inner
sum.  That restriction turns out to be **free**: it is one more application of the same prime step.

| result | content |
|---|---|
| `delangeS`, `delangeA`, `delangeSrestr`, `delangeT` | the four sums, named (`delangeKernelMean_iff`: the residue is literally `delangeS z N → 0`) |
| **`delangeSrestr_rec`** | `S^{(p)}(M) = S(M) − ((z−1)/p)·S^{(p)}(M/p)` — an EXACT recursion, not an estimate |
| `norm_delangeSrestr_le` | hence `‖S^{(p)}(M)‖ ≤ ‖S(M)‖ + (u/p)·A(M)` |
| **`norm_delangeT_le`** | `‖T(N)‖ ≤ u · Σ_{p≤N} (log p/p)·(‖S(N/p)‖ + (u/p)·A(N/p))` |

`norm_delangeT_le` is the Levin–Fainleib working inequality with **no `O(·)` and no hidden
constant** — every quantity is a named sum in the file.  The error term is genuinely secondary:
`Σ_p log p/p² < ∞`, so it contributes `O(u²·A(N))` against a main term of size `u·log N·‖S‖`.

## What remains for `DelangeKernelMean`
1. **Partial summation** `T(N) = S(N) log N − Σ_{n≤N} (h(n)/n)·log(N/n)` (or its integral form) —
   this converts `norm_delangeT_le` into a Gronwall-type recursion for `‖S‖`.
2. **Mertens** `Σ_{p≤N} log p/p = log N + O(1)` — in `src/PNTPort/`, needs porting to this shape.
3. **The induction**: with `u < 1` the recursion `‖S(N)‖ log N ≲ u log N · max_{p} ‖S(N/p)‖ + …`
   contracts, giving `‖S(N)‖ ≪ (log N)^{u−1+ε}`... the standard Wirsing endgame.

Steps 1–2 are each a lap; step 3 is the substantive one.

## Run to date
lap 28 `92ede26` · lap 29 `ab283df` · lap 30 `2d4d2c3` · lap 31 `6775ae3` · lap 32 `f29262a` ·
lap 33 `3019208` · lap 34 (this).

The C1 crux itself is *measured*: `pairDecorr_iff_unweighted` (lap 31) pins it as equivalent to an
unweighted growing-length natural-density Elliott correlation along dilates, and lap 32 shows
neither the depth nor the weight can be traded away.  That satisfies the kickoff's success
criterion; the remaining dischargeable debt is `DelangeMean`, which this and lap 33 attack.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3%.
- `DelangeKernelMean` for `‖z−1‖<1` closable in 3–6 laps: **35%**.
