# HANDOFF — 2026-08-25 · B6 Tier-2 FULL + image-Khinchin crux isolated

Branch `master`, HEAD `2da5641`, build 🟢 8760, working tree clean.

## State of the expedition (all real `#print axioms`)
- **B5′ (10 headlines)** + **B6 single-map** (`exists_cfNormal_and_affine_cfNormal`):
  proven, trust-triple `[propext, Classical.choice, Quot.sound]`. Unchanged.
- **B6 Tier-2 general family — NEW this run, DONE + axiom-clean** (`src/NormalNumbers/CFAffineFamily.lean`):
  - `exists_cfNormal_and_affine_family_cfNormal` (`q>0, r≥0`) and
  - `exists_cfNormal_and_affine_family_cfNormal'` (**full generality: any real `r`, `q>0`** —
    the faithful Vandehey §7 Tier-2 statement). Both trust-triple.
  - Crux proved: `volume_notCFNormal_univ` (non-CF-normal set is Lebesgue-null on ALL of `ℝ`).
    `[0,∞)` half by integer-shift covering; `(-∞,0)` half by the `inv`-involution identity
    `gaussMap⁻¹(Z)∩Iio0 = inv''(Int.fract⁻¹Z∩Iio0)` + differentiable-image-of-null.

## The ONE open obligation (image-Khinchin stretch, in `src/NormalNumbers/CFAeKhinchin.lean`)
Goal `ae_khinchinTypical : ∀ᵐ x ∂γ, KhinchinTypical x` — the co-null set to intersect into the
family witness so the B6 witness is also Khinchin-typical.

**`ae_khinchinTypical` is fully ASSEMBLED and reduced to ONE disclosed sorry**, `ae_tail_average_tendsto`
(`CFAeKhinchin.lean:226`). Everything else is trust-triple:
- `ae_digitCount_tendsto` (bounded-part leaf, = `ae_orbit_freq [a]`)
- `integral_logTailFn_zero` (`∫ logTailFn 0 dγ = log K₀`)
- `logTailFn_zero_ae_eq` (`logTailFn 0 = log(cfDigit·0)` a.e.)
- the assembly of `ae_khinchinTypical` itself (pointwise digit identity + `khinchinTypical_iff_log_tendsto`)

**The g-direct insight**: `logTailFn 0 = log(cfDigit·0) = g` a.e., `g ≥ 0` (Birkhoff sum monotone),
`∫ g = log K₀`, so `ae_khinchinTypical ⟸ ae_tail_average_tendsto 0` alone (no `K`-split, no bounded
part needed).

## NEXT STEPS (hardest-first) — prove `ae_tail_average_tendsto K`
`∀ᵐ x, logBirkhoffSum K n x / n → ∫ logTailFn K dγ`. Route (mirrors `ae_orbit_freq`):
1. **`variance_logBirkhoffSum_le K n`**: `|∫(logBirkhoffSum K n)² dγ − (n·∫logTailFn K)²| ≤ C_K·n`.
   - Second moment `= Σ_{j,j'<n} ∫ logTailFn K(Tʲ·)·logTailFn K(Tʲ'·) dγ`.
   - Per-gap correlation `|Cov(f,f∘Tᵐ)| ≤ (9/10)^{m∸1}·4·(Σ_{a>K} log a·γ([a]))·(Σ_{b>K} log b·|[b]|)`
     from **`abs_cov_two_cyl_le`** (`CFAeKhinchin.lean`, landed) + the two summability constants
     **`summable_logMul_vol_cfCylinder`** and `summable_gaussKuzmin_log` (both landed; plus
     `summable_sqLog_gaussMeasure_cfCylinder` for the `∫g²<∞` / diagonal `m=0` term).
   - The `f = logTailFn K = ∑'ₐ log a·1_{[a]}` disjoint-cylinder tsum expansion is the heavy
     bookkeeping (use `logTailTerm_tsum_ae_eq` + `integral_tsum` templates already in `CFLogTail`).
   - Fold with `sum_range_dist_le` / `geom_trunc_sum_le` (reuse `variance_blockCount_le`'s pattern) ⇒ `≤ C·n`.
2. **Chebyshev + Borel–Cantelli** on `p=(k+1)²` + **monotone gap-squeeze** (`logBirkhoffSum K n x` ↑ in n
   since `logTailFn K ≥ 0`) — copy the `ae_orbit_freq` skeleton (`CFAeNormal.lean:81`).
3. Then `ae_khinchinTypical` becomes axiom-clean automatically.
4. **Graft**: intersect the `ae_khinchinTypical` co-null set into
   `exists_cfNormal_and_affine_family_cfNormal'` (one more null set in the `BadAll` union) ⇒
   image-Khinchin headline: witness `x` CF-normal + all affine images CF-normal + `x` Khinchin-typical.

## Bricks already landed for step 1 (all axiom-clean, in `CFAeKhinchin.lean`)
`gaussMeasureReal_pair_shift₂`, `abs_cov_two_cyl_le`, `summable_logMul_vol_cfCylinder`,
`summable_sqLog_gaussMeasure_cfCylinder`, `sq_log_le_sixteen_sqrt`, `gaussMap_mem_Ico01`,
`isCFNormal_of_gaussMap`, `volume_notCFNormal_*`.

Detail + route rationale in `PENDING_WORK.md` (top entries). DIRECTION.md CURRENT DIRECTIVE
(measure-route B6) is fully discharged and exceeded; the schedule REFUTED sorries remain
directive-forbidden dead code (untouched).
