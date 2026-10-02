# HANDOFF — ζ_Y campaign, lap 1 (2026-10-02)

Branch `proof/zeta-y`, HEAD `bf90f08f`, tree clean, build green.

## Done (all axiom-clean modulo the cited hypothesis `VandeheyThm51`)
- `exists_unbounded_zetaY` **PROVED** (`GrowingLocalizedLogWitness.lean`).
- Crux N8, all pieces:
  - `Exponent.lean`: a Lemma 6.3 replacement with no constant `c`.  It uses the invariant
    `F_k = (ν_k−γ_k)(2^{k+1}−1)` and proves `vandehey_window_bound`.
  - `Cost.lean` (`constPair_sum_le`), `M.lean` (`bigM_two_le`, LTE),
    `CostBound.lean` (`nine_costX_le`: `≤ 2^{60(π+2)^4}`).
  - `Block.lean`: `block_bound`, one clean block.
- N1 `card_smooth_le` and `le_of_primeCounting` (`Z ≤ 17(π+1)²`) in `Count.lean`.
- N2/N6 `two_pow_mul_xS_sub`, `Rs_shift` (`Tail.lean`).
- N3–N5 `Rs_eq`, `three_not_dvd_Tnum`, `den_bounds` (`Arith.lean`).
- N9 deterministic: `main_bound` (`Assembly.lean`).
- N9 analytic core at one scale: `saving_beats_cost` (`Weyl.lean`).
- `Asymp.lean`: `eventually_poly_le_exp`, `eventually_poly_le_two_pow`.

## Next (only `zetaY_isNormal` remains)
1. `weyl_Rs`, in `Weyl.lean`.  Statement: for each `h ≠ 0` and `δ > 0`, eventually
   `‖Σ_{n<N} e(h R_n)‖ ≤ δN`.  Use `L = log₂N`, `ℓ = log₂L`, `g = (ℓ+1)^3`, `G = 2^g`,
   `H = N/G`, `B = L+1`, `z = Z N`.  Feed `main_bound`; its `hk` comes from
   `saving_beats_cost` plus `2 ≤ δH/4`.  Facts to supply:
   - `π ≤ ℓ+1`, from growth and `log N < (L+1) log 2 ≤ 2^{ℓ+1}`;
   - `2^π ≤ (log N)^{1−ε}`, via `Real.rpow_logb`;
   - `k ≤ π+3`, from `π(g+1)+g ≤ L`;
   - `H ≥ 2^{L−g}`;
   - `Ψ ≤ (L+1)^π`, via `card_smooth_le`;
   - the polynomial inequalities, via `eventually_poly_le_two_pow` with a constant that absorbs
     `c` (`2^c ≥ 81h⁴+6|h|+2`) and `c'` (`2^{c'} ≥ 12/δ`).
   Take `ε ≤ 1` WLOG (`min ε 1`).
2. The orbit transfer: `orbit 2 x n = fract(x 2^n)` and
   `|e(h x 2^n) − e(h R_n)| ≤ 4π|h|/(n+1)`.  Use `norm_ePhase_sub` and `two_pow_mul_xS_sub`,
   and split at `√N`.  Then apply `equidistributed_of_weyl` and
   `isNormal_iff_equidistributed_orbit`.
3. Instantiate `S = Retained Y`, `Z = Y`.  `zetaY Y = xS (Retained Y)` should be `rfl`
   (both use Classical).
