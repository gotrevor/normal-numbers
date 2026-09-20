# PROBE 2026-09-20 — frozen node N1a′ `SmoothRoughDecoupling` (G4WiringRough.lean)

Script: `probes/rough_decoupling.py` (pure stdlib; no numpy on the box).  `y ∈ {2,3,5}`,
`h ∈ {1,3,5}`, `N = 2^12 … 2^21`, `J = windowJ N`.  Reported: the **relative** errors
`rel1 = ‖W − S·R‖ / ∏‖full_j‖` (window half) and `rel2 = ‖∏full − ∏smooth·∏rough‖ / ∏‖full_j‖`
(site half), which the node bounds by `C / log N`.

## Verdict: SUPPORTED, no refutation.  The wiring's case (`y = 2`) is the cleanest.

Both relative errors decay monotonically in `N` in every one of the nine cells.  Multiplying by
`log N` gives a near-constant:

| cell | `rel1·logN` (N = 2^12 → 2^21) | `rel2·logN` |
|---|---|---|
| y=2 h=1 | 0.74 → 0.86 | 1.00 → 1.11 |
| y=2 h=3 | 1.70 → 1.42 | 1.36 → 1.41 |
| y=2 h=5 | 0.003 → 0.006 | 2.54 → 3.00 |
| y=3 h=1 | 1.60 → 1.87 | 1.91 → 2.16 |
| y=5 h=5 | 8.5 → 11.9 | 5.6 → 7.3 |

Local exponents `α` in `rel ≍ (log N)^{-α}` over the whole range: 0.73 / 0.82 (y=2,h=1),
1.32 / 0.94 (y=2,h=3), 0.70 (y=2,h=5 site half).  They **bracket 1** with the scatter one
expects from second-order terms at `log N ∈ [8.3, 14.6]`; nothing here distinguishes
`C/log N` from `C/(log N)^{0.9}`, and nothing suggests a floor.  The constants grow with `y`
and `|h|` (the `y = 5, h = 5` cell has `C ≈ 12`), which is why only the `y = 2` column matters:
`crtConstantSched_of_roughAt` fixes `y = 2`.

## What the probe *taught*, beyond the verdict

The site half at `y = 2` is not an asymptotic statement at all — it is an **exact algebraic
identity plus a scale-smoothness estimate**.  With `ζ = e(h 4^{-j})`, `r(n) = e(h ω_{>2}(n+j) 4^{-j})`,
and `Se`, `So` the sums of `r` over `n + j` even / odd in `[N, 2N)`, for even `N`:

    fullSiteMean − smoothSiteMean · roughSiteMean = (ζ − 1)(Se − So) / (2N).

Two consequences:

1. **The `J`-sum converges.**  `‖ζ_j − 1‖ ≤ 2π|h| 4^{-j}`, so the per-site relative errors are
   geometrically small in `j`; the telescoped product error is `O(1/log N)` *uniformly in `J`*,
   which is exactly the uniformity the frozen node asserts.  (A `J`-independent constant looked
   like the risky part of the statement; it is not.)
2. **`Se − So` is a scale difference, not an oscillation.**  `ω_{>2}` ignores the factor 2, so
   `r(2m) = r(m)` and `Se(I) = R(I/2)` where `R(I) = ∑_{m ∈ I} r(m)`; hence
   `Se − So = 2R([N/2,N)) − R([N,2N))`.  The site half at `y = 2` is therefore *equivalent* to

       |2R([N/2, N)) − R([N, 2N))| ≤ C / log N · |R([N, 2N))|,

   i.e. **the rough site mean is scale-smooth**: its mean over `[N/2,N)` and over `[N,2N)` agree
   to relative accuracy `1/log N`.  For a Selberg–Delange mean `≍ c(log N)^{z−1}` that is the
   derivative bound `(1 + log 2/log N)^{z−1} = 1 + O(1/log N)` — far weaker than the
   Halász/SD input `RoughIndependence` needs, and a strictly more classical node.

## Next attack

Formalise the identity (elementary, `N` even) and split `SmoothRoughDecoupling`'s site half into
`RoughScaleSmoothness`.  The window half has the same shape with the parity of the whole
`J`-tuple in place of a single site.
