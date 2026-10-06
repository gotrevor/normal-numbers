# HANDOFF cantorbad lap 10 (2026-10-06)

Branch `proof/cantor-bad-normal`.  Headline unchanged; build green.  Crux still `aliveOffMix_resLaw`.

## Done
- PROVED `pow_phase_recur`: e(a bᵐ/n) eventually periodic in m.  With `periodic_phase_sum` /
  `riesz_three_shift`: bounded-period obstacle families (3-free denominator | 3^ℓ±1) regain base-3
  coherence on a positive density of m even for 3 ∤ b.
- Probe `scripts/cantorbad_mscan.py` (+ `_groups`): L=12,S=4,b=2: median .003, outliers m=184 (.128),
  185, 111, driven by denominators 244, 364, 730, 1093.  Recorded in `ObstaclePairCorrelation` docstring.

- PROVED `obstacle_phase_crt` (CRT split: q'-part × 3-adic part).
- Node `PeriodicFamilyShare` (believed false: preperiodic families' pair share .18–.56 at L=12).
- Node `ThreeAdicWindowAvg` (70%): averaged Riesz product of hbᵐ's low-digit windows; probe b=2,5,7 ≈ (2/π)^M, b=3 ≡ 1.

## Next
1. Prove shallow case of `ThreeAdicWindowAvg` (3^j ≤ N: bᵐ equidistributed in its subgroup mod 3^j over full periods).
2. Wire: preperiodic-family obstacle pair sums ≤ (q'-part) × ThreeAdicWindowAvg, toward ObstaclePairCorrelation/AliveOffMix.
3. Poisson/divisor reformulation (Σ_n μ̂_K(n) τ_Q(n+ξ)) still unstated.
