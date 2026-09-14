# HANDOFF — entropy grind lap 34 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  `lake build` green, **8969 jobs**.  New module
`src/NormalNumbers/G4EntropySpectralLower.lean`, sorry-free, `#print axioms` clean (trust
triple only).  No pre-expedition file edited; `entropy_E1`, `G4Tensor`, `G4Spectral` untouched.

## What was proved: the wall is a theorem, not a measurement

Laps 32–33 *measured* `δ_K ≍ √K` and recorded the verdict "beating the order requires
cancellation across `j` in `∑_j log(1 + Λ_j)`".  This lap proves **there is no cancellation to
be had**:

```
log_det_one_add_tensorGram_ge     (s ≥ 25, K ≥ 1)
    (s:ℝ)^K * √K / 300000  ≤  log det (1 + T_s^{⊗K})

log_det_one_add_tensorGram_sq_ge  (K ≥ 5)
    ((K:ℝ)^2)^K * √K / 300000  ≤  log det (1 + T_{K²}^{⊗K})
```

against the upper bound `log_det_one_add_tensorGram_le_twelve`
(`≤ (K²)^K (log 2 + 12√K)`).  So the quantity `entropy_E1`'s deficit is built from is
**`Θ(s^K √K)`**: the `√K` is a property of the object, and no refinement of the spectral/cover
route — not a sharper per-term inequality, not a smarter grouping — can push the expedition's
word-length ceiling `ℓ = o(√K)` any further.  The only remaining lever named by laps 32–33 is
therefore closed as well: cancellation across `j` does not exist at this order.

## How (a fourth-moment / Khintchine argument, entirely finite)

| declaration | role |
|---|---|
| `posPart_le_log_one_add` | `(log Λ)^+ ≤ log(1+Λ)` — the determinant dominates the positive part |
| `sum_sq_cube_le` | `(∑X²)³ ≤ (∑\|X\|)²(∑X⁴)`, two Cauchy–Schwarz steps (`B² ≤ AD`, `D² ≤ BC`) |
| `sum_abs_ge_sq_mul_sqrt` | Paley–Zygmund form `∑\|X\| ≥ (∑X²)√((∑X²)/(∑X⁴))` |
| **`sum_pi_quad`** | the **exact** fourth moment for a centered one-site weight: `s²∑_j X_j⁴ = K s^{K+1}∑ℓ⁴ + 3K(K−1)s^K(∑ℓ²)²` |
| `two_le_lam`, `sum_sq_log_lam_ge` | half the eigenvalues are `≥ 2`, so `∑ log²λ ≥ (log²2)s/2` — the second moment from BELOW (new; everything before bounded it above) |
| `quad_log_le_sqrt`, `sum_sqrt_ratio_le`, `sum_quad_log_lam_le` | `∑ log⁴λ ≤ 4194304 s` (`log⁴y ≤ 4096√y` plus `∑ m^{-1/2} ≤ 2√s`) |
| **`sum_abs_pi_ge`** | the generic bound: centered `ℓ` with `c s ≤ ∑ℓ² ≤ U s`, `∑ℓ⁴ ≤ M s` gives `∑_j\|X_j\| ≥ c√(c/(M+3U²))·s^K·√K` |
| `logLamC`, `sum_logLamC`, `mu_le` | the centering `ℓ̃ = log λ − log(s+1)/s`; `∑ℓ̃ = 0` exactly, and the shift is `≤ (log2)/2` for `s ≥ 25` |

**The structural point** (this is where the `√K` comes from, and why it cannot be removed):
the fourth moment of `X_j = ∑_i ℓ(j_i)` is only `O(K²)` times the *square* of the second
moment — the `3K(K−1)(∑ℓ²)²` term of `sum_pi_quad` — so the Paley–Zygmund ratio
`(∑X²)³/(∑X⁴)` is of order `K`, and `∑_j |X_j| ≳ s^K√K`.  Centering is what makes this a
lower bound for the determinant: `∑_j X̃_j = 0` **exactly**, so `∑_j (X̃_j)^+ = ½∑_j|X̃_j|`,
and the centering shift `K log(s+1)/s ≥ 0` only helps (`(log Λ_j)^+ ≥ (X̃_j)^+`).

Constants are generous (`1/300000` against an upper constant `12`); the order is the content.

## §6 (same lap): the two-sidedness, stated where the cover consumes it

- `tensorGram_cover_constant_ge` — `entropy_cover_bound` consumes `hLg : Lg ≤ (K²)^K(log2+23√K)`;
  **any** bound of the constant shape `Lg ≤ (K²)^K · C` forces `C ≥ √K/300000`.  The growing
  term in that hypothesis is not an artifact of how it was proved.
- `log_det_normalized_two_sided` — for `K ≥ 5`,
  `1/300000 ≤ log det/((K²)^K √K) ≤ log2/√K + 12`.
- `tendsto_log_det_div_atTop` — `log det/(K²)^K → ∞`.

## Next bounded test

1. **Sharpen the constants** (optional, low value): the `4096` in `quad_log_le_sqrt` and the
   `520` in `sum_sq_log_lam_le'` are both ~100× lossy; the true `c` is `≈ 0.2` not `3·10^{-6}`.
   Not worth a lap unless a downstream statement needs a numeric constant.
