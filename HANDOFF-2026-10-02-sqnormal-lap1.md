# HANDOFF — explicit-square lane (row 3), lap 1 — 2026-10-02

Branch `proof/sqnormal`, HEAD `402922d4` (green). No uncommitted edits.
Lane/operator scope: `src/NormalNumbers/ExplicitSquareNonNormal.lean` row 3 only (frozen statements;
ignore DIRECTION.md). Done = `#print axioms exists_computable_normal_sq_not_normal` has no sorryAx.

## Done this lap (all sorry-free)
- `sqrt_bakerBanaji_hyp` (frozen file).
- `ae_isNormal_of_polyDecay` (frozen file) via new `DecayAeNormal.lean`
  (`second_moment_le`, `ae_tendsto_weyl`, `ae_isNormal_two_of_decay`).
  ⇒ `exists_sqrt_normal_sq_not_normal` axiom-clean modulo the BB hypothesis.
- `Derandomize.lean`: `exists_primrec_avoid` (computable conditional-expectation greedy avoiding
  clopen bad events with Primrec tail modulus), `coins_pre` (prefix-event mass = count/2^n).
- `HatFourier.lean`: hat/plateau Fourier coefficients, `norm_plateau_coeff_le` ≤ 2/(ρπ²n²).
- `VisitDeviation.lean`: `mean_sub_coeff_le`, `prob_mean_dev`, `visit_deviation`
  (μ{2ρ+t < |V/N − (c−a)|} ≤ 2·(2/(3ρ))/t·√((N+K)/N²)).
- `ComputableNormal.lean`: Primrec bad tests `badT`/`depth` (level n, N=n^10, blocks 2^ℓ ≤ n,
  tol 3/(4n)), `orbit_mem_iff`, `Vc_eq`.

## Open (next attacks, in order)
1. `ComputableNormal.exists_computable_normal_of_digits` (sorry). Plan: K from C,δ; natural
   c₁ ≥ (64/3)√(1+K); per block ≤ c₁/n³ (visit_deviation, ρ=t=1/(4n), (N+K)/N² ≤ (1+K)/N);
   #blocks ≤ 2n ⇒ dens j [] ≤ 2c₁/n² (coins_pre + Vc_eq + union bound); n = j+n₀, n₀ = 8c₁+2;
   J k = 2c₁·8^(k+1); tails via Σ_{n>M} 1/n² ≤ 1/M. Avoidance ⇒ for n ≥ max(n₀,2^ℓ),
   |V(n^10)/n^10 − 2^-ℓ| ≤ 3/(4n) ⇒ subseq limit ⇒ all N by
   `tendsto_div_of_monotone_of_exists_subseq_tendsto_div` (c n = n^10) ⇒ `equidistributed_of_badic`
   ⇒ `isNormal_iff_equidistributed_orbit`. Needs `IsProbabilityMeasure coins` instance.
2. `exists_computable_isNormal_sqrt_of_polyDecay` (frozen): G = √∘cantorReal (coins defeq
   coinMeasure), Φ m p = Nat.sqrt(Σ_{i<2m} cd(p,i)·2^(2m−1−i)); need ⌊√y·2^m⌋₊ = Nat.sqrt⌊y·4^m⌋₊
   and ⌊y·2^n⌋ from digits (see Bridge.floor_realOfDigits_mul_pow, private — re-prove/expose).
Gotchas: `lake env lean` has autoImplicit on, real build off — check with `lake build <mod>`.
Primrec: annotate every `have` type explicitly; `attribute [local irreducible]` defeats whnf timeouts.
