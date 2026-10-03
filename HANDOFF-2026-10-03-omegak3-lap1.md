# HANDOFF 2026-10-03 — Ω_k (k ≥ 3) lane, lap 1

Branch proof/omegak3. Scope: `sorry-free:src/NormalNumbers/ExplicitOmegaK.lean`
(headline `exists_computable_mem_Omega`). Tree clean (scratch/ untracked, disposable).

## Done this lap (all green, committed)
* `deriv_Gk_le`, `deriv2_Gk_lower` (ℂ factorisation of `qPoly.divX`, clamp `tauK`),
  `card_near_cylinders_le` (via `psiL_eq_phi`, open-interval floor count).
* `pushFourier_le_of_deriv2_lower` (the cylinder cut): helpers `pushFourier_cut_split`,
  `good_cylinder_bound`, `exists_pow4_bracket`, `inv_two_pow_le`, `a_rpow_neg_le`.
  NB δ = min(ε,η)/2 (docstring's min(η/2,ε/2) silently assumed ε ≤ η).
  `#print axioms polyDecay_Gk` = trust base only.
* `decay_Gfam` (hgt ≤ hgtBound i = encode(decode i)+1, primrec via `Primrec.encdec`).
* `exists_computable_absNormal_family` — new file `FamilyDerandomize.lean`: test j checks all
  i ≤ j at level M_i(j+8), M_i = (c₁ i+1)4^{i+2}; `normal_of_good_AP`.
* `OmegaKApprox.lean`: `cantorReal_mem_prefix` (yN p / 2^{2D+1}, width 4^{-D}/6),
  `cantorReal_le_two_thirds`, primrec `iroot` (+ bounds), primrec `toNat`/`negPart`/`natAbs` on ℤ.

## Remaining: ONE sorry — `approx_Gfam`
Plan (see last report): coefficient list `cl i` = decoded l if (Σ natAbs (l.drop 1) ≠ 0 ∧
Σ natAbs (l.drop k) = 0) else [0,1]  (prove ↔ `1 ≤ natDegree < k` via
`natDegree_le_iff_coeff_eq_zero`); H = Σ natAbs (= hgt, prove). Y = yN p, D = |p|,
T = D+k+3, X = iroot k (Y·2^{Tk−2D−1}), x̃ = X/2^T. S± = Σ_j a_j^± X^j 2^{T(K−j)} (K = length).
R = (S/2^{TK} + H)/(2H); A = max(0, R − δ), δ = 4^{-D}/3 + 2^{-D}/8; Ψ = toNat-numerator·b^m / Den
(Nat div). Errors: prefix via MVT + `deriv_Gk_le` (|ΔGfam| ≤ 4^{-D}/3); root via
`abs_pow_sub_pow_le_unit` (≤ k·2^{-T}/2 ≤ 2^{-D}/8). Then 2δ ≤ 2^{-D}.
Then `#print axioms exists_computable_mem_Omega` and `box done`.
