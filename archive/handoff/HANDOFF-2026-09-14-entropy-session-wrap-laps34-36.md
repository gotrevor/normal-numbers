# HANDOFF — entropy session wrap, laps 34–36 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  **HEAD** `ca877f9`.  Working tree **clean**.  `lake build` green,
**8970 jobs**.  Every declaration added this session is sorry-free and `#print axioms` clean
(trust triple only).  No pre-expedition file edited; `entropy_E0`/`entropy_E1`, `G4Tensor`,
`G4Spectral`, `G4EntropyTiling`, `G4EntropyRender` all untouched (added to, never changed).
`isDisjunctive_four/two/base` and `primeSumAtBase_eq_primeLambertAtBase` unchanged.

## Two threads advanced, both closed at their stated goal

### 1. The `√K` wall is now a theorem (laps 34, 34b) — `G4EntropySpectralLower.lean`

Laps 32–33 *measured* `δ_K ≍ √K` and recorded "beating the order needs cancellation across `j`
in `∑_j log(1+Λ_j)`".  That cancellation **does not exist**:

```
log_det_one_add_tensorGram_ge     (s ≥ 25, K ≥ 1) :  s^K √K / 300000  ≤  log det (1 + T_s^{⊗K})
log_det_one_add_tensorGram_sq_ge  (K ≥ 5)         :  ((K²)^K √K)/300000 ≤ log det (1 + T_{K²}^{⊗K})
log_det_normalized_two_sided      (K ≥ 5)         :  1/300000 ≤ log det/((K²)^K √K) ≤ log2/√K + 12
tensorGram_cover_constant_ge      (K ≥ 5)         :  Lg ≤ (K²)^K·C  ⟹  C ≥ √K/300000
tendsto_log_det_div_atTop                         :  log det/(K²)^K → ∞
```

so the quantity `entropy_E1`'s deficit is built from is `Θ(s^K √K)` and the growing term in
`entropy_cover_bound`'s hypothesis is structural.  **The expedition's word-length ceiling
`ℓ = o(√K)` is a property of the object, not of the estimate.**

Method (all finite, no probability library): `(log Λ)^+ ≤ log(1+Λ)`; centering the one-site
log-spectrum makes `∑_j log Λ̃_j = 0` exactly, so `∑_j (log Λ̃_j)^+ = ½∑_j|log Λ̃_j|` and the
centering shift only helps; two Cauchy–Schwarz steps give `(∑X²)³ ≤ (∑|X|)²(∑X⁴)`; and the
**exact fourth moment** `sum_pi_quad` — `s²∑_j X_j⁴ = K s^{K+1}∑ℓ⁴ + 3K(K−1)s^K(∑ℓ²)²` — makes
`(∑X²)³/(∑X⁴)` of order `K`, which is the `√K`.  New spectral input: `two_le_lam` —
half the Gram eigenvalues are `≥ 2`, the **first lower bound** on the spectrum's second
log-moment (everything before bounded it above).

### 2. All positions, not one tiling (laps 35, 36) — `G4EntropyOffset.lean`

The directive's endpoint (met laps 29–31) counts a word among the **aligned** blocks.  Normality
counts it at **every** position.  Now proved, abstractly, for any `FinLaw`:

```
abs_posAvg_sub_le  (0 < ℓ ≤ m, per-coordinate deficit δ) :
  | avg over (α, p < m−ℓ+1) of Pr[ the ℓ-block at position p = w ] − 2^{−ℓ} |
      ≤ 2 √(log 2 · ℓ δ / (m − ℓ + 1))
```

— the same bound as the aligned version to within `1 + o(1)`.  The reduction is loss-free:
`H₂_lowTuple_ge` (dropping the top `r` bits costs `≤ |A|·r`, and the maximum drops by exactly
`|A|·r`, so the truncated law keeps the **same** deficit on `m − r` bits) ⇒
`abs_avg_block_prob_offset_le` (the offset-`r` tiling = the aligned tiling of the truncated
window) ⇒ `fullCoord_lowTuple_eq` + `posEquiv` (the offset classes tile the positions exactly,
`(r,j) ↔ r + jℓ`) ⇒ a weighted average.  Also new: `abs_avg_block_prob_tile_opt` (the abstract
`t`-optimized tiled capacity bound) and `FinLaw.prob_singleton_map_map`.

## Next session — the bounded next test

Render thread 2 at the schedule, mirroring `G4EntropyTiling`'s last three theorems:

1. `posFreq i ℓ x w := posAvg (kk i) ℓ (jointLawAt i x) w`, then
   `abs_posFreq_sub_le_of_deficit` and the `E0` / `entropy_E1` instances.  Mechanical: the
   deficit hypothesis is *verbatim* the one `abs_blockFreqT_sub_le_of_deficit` takes, and
   `abs_avg_block_prob_tile_opt` is already the abstract form of that proof.
2. Digit rendering: `G4EntropyRender.blkAt_blockVal_min` is stated for `blkAt m ℓ j`
   (`= posAt m ℓ (jℓ)`); the general-`p` version is the same proof with `(j+1)*ℓ ↦ p + ℓ`.
3. Endpoint `tendsto_occursCountP_primeLambertFour`: every finite binary word occurs with
   frequency `2^{−|w|}` among **all** positions of `G₄`'s sampled windows — strictly stronger
   than lap 31's aligned version, and the exact predicate `isDisjunctive_two` uses.

## Lean gotchas harvested this session (all verified)

- **Never let the elaborator unify two `FinLaw.map`s up to beta.**  `exact` against a
  beta-equivalent-but-not-syntactic map argument times out at `isDefEq` even at 10⁶ heartbeats:
  it whnfs through the `Finset.filter` in `map`'s mass function and hence through
  `Fintype.decidablePiFintype` on `A → Fin (2^m)`.  Fix: `FinLaw.H₂_map_congr_comp`, which takes
  the composition **pointwise** (`hF : ∀ ω, F ω = g (f ω)`, discharged by `fun z => rfl`).
- `rw [← abs_of_nonneg h]` rewrites *every* occurrence, including the ones you needed bare.
- `Sigma.ext` leaves an `HEq`; close it with `Fin.heq_ext_iff (by simp only [Fin.val_mk]; rw [h])`.
- Nat `%`/`/` by a *variable* is beyond `omega`: supply `Nat.div_add_mod`, `Nat.le_div_iff_mul_le`,
  `Nat.add_mul_div_right`, `Nat.add_mul_mod_self_right` explicitly, then `omega` finishes.
- `(z % 2^a)/2^b % 2^c = z/2^b % 2^c` for `b + c ≤ a`: via `Nat.mod_mul_right_div_self` twice
  plus `Nat.mod_mod_of_dvd`.
- An empty `Fin (X)` with `hzero : X = 0` in context: `have : IsEmpty (Fin X) := by rw [hzero];
  infer_instance` — `▸`/`rw` on `c.2.isLt` fails (motive not type correct).
- `Real.tendsto_sqrt_atTop` is the `atTop → atTop` form (`Filter.Tendsto.sqrt` is the `nhds` one).
- `linear_combination c * h` closes the induction steps that `nlinarith` refuses when the
  hypothesis must be multiplied by a symbolic factor (`sum_pi_quad`'s `6(∑ℓ²)·hQ2 + s·ih`).
