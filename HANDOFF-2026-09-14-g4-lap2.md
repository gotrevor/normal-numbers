# HANDOFF 2026-09-14 — G4 disjunctivity, lap 2 (crux B: spectral half PROVED)

HEAD `d0e4a44` on `wip/g4-disjunctivity`.  Lap 1 handoff: `HANDOFF-2026-09-14-g4.md` (still
accurate for `PrimeLambertFour`, `G4SeparatingTest`, `G4Wiring`).  Build:
`lake build NormalNumbers.G4Wiring NormalNumbers.G4Tensor NormalNumbers.G4DetMonotone`.
DIRECTION.md: attended override records the prior campaign COMPLETE; the 2026-09-14 G4 kickoff
is the attended objective.  All headline declarations below print
`[propext, Classical.choice, Quot.sound]`.

## Proved this lap (crux B, the spectral content of §4B)

* `G4Spectral.lean` — **log moments of the 1-D spectrum**: `lam_ge` (Jordan:
  `λ_j ≥ 4((j+1)/(s+1))²`), `log_lam_le/ge`, `sq_log_le_sixteen_sqrt` (`log² y ≤ 16√y`),
  `sum_inv_sqrt_le` (`∑_{m≤s} m^{-1/2} ≤ 2√s`), `sum_sq_log_ratio_le`,
  **`sum_sq_log_lam_le' : ∑_j log² λ_j ≤ 520 s`** (`s ≥ 1`).
* `G4Tensor.lean` (new) — `det_of_orthogonal_eigenbasis` (`det M = ∏ μ` from an orthogonal
  non-null eigenbasis), `tensorGram K s = T_s^{⊗K}` on `Fin K → Fin s`, product sine eigenvectors
  `tensorVec` with `tensorGram_mulVec_tensorVec`, `tensorVec_orthogonal`, `tensorVec_self_pos`,
  **`det_one_add_tensorGram : det(1 + T^{⊗K}) = ∏_j (1 + ∏ᵢ λ_{jᵢ})`**, `prod_lam = s+1`,
  `sum_log_lam = log(s+1)`, exact tensor moments `sum_pi_linear`, `sum_pi_sq`
  (`s²∑X² = K s^{K+1} L₂ + K(K−1) s^K L₁²`), `log_one_add_le_log_two_add_abs_log`,
  `sum_abs_le_sqrt_card_mul_sum_sq` (Cauchy–Schwarz), the general bound
  `log_det_one_add_tensorGram_le` (`≤ s^K (log 2 + √(Kμ₂ + K(K−1)μ₁²))`), and
  **`log_det_one_add_tensorGram_le' : log det(1 + T_{K²}^{⊗K}) ≤ (K²)^K (log 2 + 23√K)`**
  for `K ≥ 1`.  This is the draft's `O(r√K)`; the mean-zero cancellation `μ₁ = log(s+1)/s` is
  exactly what beats Hadamard's `O(rK)`.
* `G4DetMonotone.lean` (new) — `det_le_det_add_vecMulVec_self` (matrix determinant lemma,
  `N ≻ 0 ⟹ det N ≤ det(N + uuᵀ)`), `det_le_det_add_sum_vecMulVec`,
  `transpose_mul_self_eq_sum_vecMulVec`, and
  **`det_one_add_submatrix_mul_transpose_le : det(1 + A_G A_Gᵀ) ≤ det(1 + AAᵀ)`** for
  `A_G = A.submatrix e id`, `e` injective — the "principal row restriction" bound §4B asks for.

Nothing refuted.  No axioms, no sorries in any G4 file.

## Still open on B (geometry, not spectrum)

1. Identify `A = D_s^{⊗K}` as a concrete `Matrix (Fin K → Fin s) (Fin K → Fin (s+1)) ℝ` and
   prove `A * Aᵀ = tensorGram K s` (`Fintype.prod_sum`, same pattern as `tensorVec_dotProduct`).
2. Ellipsoid volume: the side-`η` box in `ℝ^{H+g}` lies in the ball of radius `η√(H+g)`; image
   under `L = [A_G, I_g]` has volume `ω_g (η√(H+g))^g √det(I + A_G A_Gᵀ)` (via
   `MeasureTheory.Measure.addHaar_image_linearMap` and `LL^T = I + A_G A_Gᵀ`).  Combine with
   `det_one_add_submatrix_mul_transpose_le` + `log_det_one_add_tensorGram_le'`.
3. Torus projection `vol_𝕋(π S) ≤ vol(S)`, covering of `C^H` by cylinders (`d' < 1`), and the
   union over good coordinate sets `G` (`≤ 2^r`) to reach `PropB δ₁` in `G4Wiring`.

## Next attacks (in order)

B-geometry items 1–3 above; then Jackson (`PropJackson`: product Fejér² kernel, first moment
`O(1/D)` in `dAv`, ℓ¹ budget `(2D+1)^r`); then A (transport) and D (remainders); C last.
