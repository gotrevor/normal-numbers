# HANDOFF 2026-09-14 — G4 disjunctivity, lap 2 (crux B: all inputs proved; assembly next)

HEAD `58da5c8` on `wip/g4-disjunctivity`.  Working tree clean.  Not pushed (host pushes).
Lap 1 handoff: `HANDOFF-2026-09-14-g4.md` (still accurate for `PrimeLambertFour`,
`G4SeparatingTest`, `G4Wiring`).  DIRECTION.md: attended override records the prior campaign
COMPLETE; the 2026-09-14 G4 kickoff is the attended objective — do not edit DIRECTION.md.
Build: `lake build NormalNumbers.G4Wiring NormalNumbers.G4TubePiece
NormalNumbers.G4TorusProjection NormalNumbers.G4Covering`.  Every headline declaration below
prints `[propext, Classical.choice, Quot.sound]`; no sorries in any G4 file.

## Proved this lap (crux B, §4B) — commits `8569081` … `58da5c8`

* `G4Spectral.lean` — log moments: `lam_ge` (Jordan), `sq_log_le_sixteen_sqrt`,
  `sum_inv_sqrt_le`, **`sum_sq_log_lam_le' : ∑_j log² λ_j ≤ 520 s`**.
* `G4Tensor.lean` — `det_of_orthogonal_eigenbasis`; `tensorGram K s = T_s^{⊗K}`, product sine
  eigenvectors, **`det_one_add_tensorGram`**; `prod_lam = s+1`, `sum_log_lam`; exact tensor
  moments `sum_pi_linear`, `sum_pi_sq`; **`log_det_one_add_tensorGram_le'`:
  `log det(1 + T_{K²}^{⊗K}) ≤ (K²)^K (log 2 + 23√K)`** (`K ≥ 1`).  Also `diff s` (`D_s`),
  `diff_mul_transpose : D Dᵀ = gram`, `tensorDiff K s = D^{⊗K}`, **`tensorDiff_mul_transpose`**.
* `G4DetMonotone.lean` — matrix determinant lemma (inequality form), finite iteration,
  **`det_one_add_submatrix_mul_transpose_le : det(1 + A_G A_Gᵀ) ≤ det(1 + AAᵀ)`**.
* `G4Ellipsoid.lean` — **`volume_eball_le`** (Gaussian comparison, `vol(ball_R) ≤ (√(2πe/g)R)^g`,
  no Gamma), contraction `dotProduct_mulVec_self_le`, `sqrtGram = CFC.sqrt(LLᵀ)`,
  `image_subset_sqrtGram_image`, **`volume_image_le`**, `closedBall_subset_eball`.
* `G4TubePiece.lean` — `augmented A = fromCols A 1`, `LLᵀ = 1 + AAᵀ`,
  **`volume_tubePiece_le`**: for `A = D_{K²}^{⊗K}`, injective `e : Fin g → (Fin K → Fin K²)`,
  `vol([A_G, I_g] '' cube) ≤ exp(½ r(log 2 + 23√K)) · (√(2πe (H+g)/g))^g`.  (Draft (5.3).)
* `G4TorusProjection.lean` — `torusProj`, `measurePreserving_torusProj` (from `(0,1]^g`),
  `preimage_image_torusProj`, **`volume_image_torusProj_le : vol(π''S) ≤ vol S`** (S measurable
  with measurable image, e.g. compact).
* `G4Covering.lean` — `orbit_add`, `block`, `orbit_expansion`, `block_ne_of_omit`,
  `admissible`/`card_admissible = (B−1)^M`, **`orbitClosure_subset_cylinders`**: an orbit
  omitting `[w/4^ℓ,(w+1)/4^ℓ)` has closure covered by the admissible closed cylinders of
  length `4^{−ℓM}`.  (Draft (4.4) in finite form.)

Nothing refuted.  Route decisions recorded in file docstrings: ellipsoid instead of zonotope;
Gaussian comparison instead of `ω_g` (the sup-cube bound for the ball would lose
`exp(O(g log H))` and break the budget — do not use it).

## Open

`PropA`–`PropD`, `PropJackson`, the §5 schedule, and the **B assembly** to `PropB`:
1. Choose the cylinder `[w/4^ℓ,(w+1)/4^ℓ) ⊆ [a,c)` strictly inside the omitted interval.
2. `C^H ⊆ ⋃_{b : Fin H → admissible} ∏ π(cyl b)`; each product cylinder is
   `center + [−h,h]^H`, `h = ½·4^{−ℓM}`, choose `M` with `4^{−ℓM} ≤ η`.
3. `y ∈ tube ⟹ ∃ G, |G| ≥ (1−ε)r, y_G ∈ π_g(c_G + η[A_G,I_g] cube)`; count `≤ 2^r` sets `G`;
   projection `𝕋^r → 𝕋^G` preserves measure of `B × 𝕋^{Gᶜ}`.
4. Sum: `vol(tube) ≤ 2^r (B−1)^{MH} η^g exp(½ r(log2+23√K)) (√(2πe(H+g)/g))^g` with `η^g` from
   `addHaar_smul`; then the arithmetic at `η = 2^{−K/4}`, `s = K²`, `r/H → 1`, `d < d' < 1`,
   `ε` small (`G4Wiring.PropB`).  Note `A` in `Frame` is over `ℤ`; `tensorDiff` is over `ℝ` —
   identify via `Matrix.map`.

## Next attacks (in order)

B assembly (above) → Jackson (`PropJackson`: product Fejér² kernel, first moment `O(1/D)` in
`dAv`, ℓ¹ budget `(2D+1)^r`) → A (transport) → D (remainders) → C.
