# HANDOFF cantorbad lap 10 (2026-10-06)

Branch `proof/cantor-bad-normal`.  Headline unchanged; build green.  Crux still `aliveOffMix_resLaw`.

## Done
- PROVED `pow_phase_recur`: e(a bᵐ/n) eventually periodic in m.  With `periodic_phase_sum` /
  `riesz_three_shift`: bounded-period obstacle families (3-free denominator | 3^ℓ±1) regain base-3
  coherence on a positive density of m even for 3 ∤ b.
- Probe `scripts/cantorbad_mscan.py` (+ `_groups`): L=12,S=4,b=2: median .003, outliers m=184 (.128),
  185, 111, driven by denominators 244, 364, 730, 1093.  Recorded in `ObstaclePairCorrelation` docstring.

## Next
1. State as a node: share of bounded-period families in obstPairs / dead mass → 0 (heuristic 2^{-L/2}).
2. Poisson over p mod q: μ_K-weighted obstacle Fourier sum at ξ ≈ Σ_n μ̂_K(n)·τ_Q(n+ξ); state and test
   whether Cassels + divisor averaging over ξ = h(bᵐ−bᵐ') controls AliveOffMix.
3. Per-depth AliveOffMix decomposition (lap 9 Next 1) remains open.
