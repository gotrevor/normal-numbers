# HANDOFF — Manai P/Q lane, lap 1 (2026-10-03)

Branch `proof/manaiq`, HEAD = the commit adding this file.  Tree clean.  Scope:
`sorry-free:src/NormalNumbers/ExplicitPQ.lean`, headline `exists_computable_PQ`.

## Done this lap (all in ExplicitPQ.lean unless noted)
* PROVED: `pushFourier_le_of_deriv2_lower_unif`, `exists_isBranch`, `wPoly_ne_zero_of_not_affineIn`
  (via `wronsk_const`), `branch_spec` (via `branch_expand`), `analyticOnNhd_GP` (`analyticAt_brInv`,
  `isOpen_image_Ioi`, `brInv_spec`), `measurable_GPfam`, `GP_bounds` (`cs`, `abs_aeval_deriv_le`),
  `deriv2_GP_lower` (`clampW`, complex factorisation of W_P), `decay_GPfam` (`degBoundQ`,
  `polyOfCodeQ_bounds`, `integral_ee_GPfam`); calculus `hasDerivAt_Xf`, `hasDerivAt_GP`, `deriv2_GP_eq`.
* The a.e. headline `exists_PQ_of_analytic` rests only on proved leaves.
* **REFUTED** frozen leaf `approx_GPfam`: `not_approxGPfamClaim` (Q = X + 512(X−1)⁹, u = 0, P = X,
  D = 4).  `approx_GPfam` still carries its `sorry` (docstring marked FALSE) because
  `exists_computable_isAbsNormal_GP` uses it.
* New module `PQGrid.lean`: `evP/evM` + `evP_sub_evM`, `gcount_eq` (monotone count = clamped floor),
  `pmulEq_iff`, `affTest/affFail` (primrec list test for affine dependence).

## Remaining sorries in ExplicitPQ.lean
`approx_GPfam` (FALSE), `exists_computable_approx_xPQ`.

## Next (plan is in PENDING_WORK.md top entry)
1. `affFail lQ (u+1) (u+2) l (len l + len lQ + 1) = 0 ↔ AffineIn (polyOfList l) Q` (dQ ≠ 0 from c ≠ 0).
2. Grid: C(j) := σQ((u+1)+j/2^T) ≤ σ w_lo as an ℕ inequality via evP/evM of lR = σQ list; show
   C j ↔ j ≤ (x_lo − u − 1)2^T; f = gcount C 2^T; |x̃ − x_lo| ≤ 2^{-T}; T = 2D+2.
3. New family GPfam2 = (G_P + H₂)/(2 H₂ S_i), H₂ = Σ|l_j|(u+2)^{len}+1, S_i = (|c|+1)(len+1) on the
   chosen list; approx2 (Num with truncated sub), decay2 (copy decay_GPfam with H := H₂ S_i),
   measurable2; rewire `exists_computable_isAbsNormal_GP` (statement unchanged).
4. Then delete the false `approx_GPfam` theorem (keep `ApproxGPfamClaim` + refutation) and prove
   `exists_computable_approx_xPQ` from the grid count with computable `e`.
