# HANDOFF — entropy grind lap 33 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  `lake build` green, **8968 jobs**.  New module
`src/NormalNumbers/G4EntropySpectral.lean`, sorry-free, `#print axioms` clean.  `G4Tensor` (a
pre-expedition file) was **not** edited; `entropy_E1` was **not** re-proved.

## The probe lap 32 asked for, executed

| declaration | statement |
|---|---|
| `log_one_add_le_log_two_add_posPart` | `log(1+Λ) ≤ log 2 + (log Λ)^+` — sharpens the `\|log Λ\|` in use, exactly for `Λ ≤ 1` |
| `sum_log_tensorLam` | the exact first moment: `∑_j log Λ_j = K s^{K−1} log(s+1)` |
| `log_det_one_add_tensorGram_le_pos` | the determinant bound with the fluctuation **halved** plus that explicit mean term, via `(x)^+ = (\|x\|+x)/2` |
| **`log_det_one_add_tensorGram_le_twelve`** | at `s = K²`, `K ≥ 4`: `log det(1+T_{K²}^{⊗K}) ≤ (K²)^K(log 2 + 12√K)` — against the `23√K` in use |

**Answer: the constant nearly halves; the order does not move.**  `23√K → 12√K` propagates to
the cover floor `92√K → 48√K` and would let `entropy_E1` run at `δ_K ≈ 25√K` instead of `50√K`
— a factor-2 gain in the word-length ceiling's constant, nothing more.

Why the order is untouched, now visible in the proof: the gain is exactly the `1/2` in
`(x)^+ = (|x|+x)/2` plus the mean `∑_j log Λ_j = K s^{K−1} log(s+1)`, which at `s = K²` is
`(K²)^K·O(log K/K)` — negligible beside `√K`.  The log-spectrum is centred, so about half the
tensor eigenvalues exceed `1` by `e^{Θ(√K)}` and the `√K` is a genuine CLT-scale spread.

**Recorded verdict (lap 32 + 33): `δ_K ≍ √K` is a wall of the spectral/cover route as built.**
Beating the *order* requires cancellation across `j` in `∑_j log(1+Λ_j)` — i.e. not bounding
each term — which is a different estimate, not a tighter constant.  §5's quantitative thread is
therefore closed: the expedition's word-length ceiling is `ℓ = o(√K)`, with the constant
improvable by a factor 2 and the order not improvable on this route.

## Where the campaign stands

- §2/§3/§4: closed (laps 1–14).  §6: `T_E`/`T_S`/`T_mix` refuted, positive branch closed as a
  characterization (laps 8–22).
- §5: **closed positively** — `tendsto_occursCountT_primeLambertFour` (every finite binary word
  occurs with its correct frequency `2^{−|w|}` among the aligned, disjoint sampled blocks of
  `G₄`), `tendsto_blockFreqT_of_capacity` (the sharp `ℓ = o(m_K/δ_K)` form, any `x`, any
  deficit), with the full digit rendering (laps 24–31) and the deficit wall measured (32–33).

## Next bounded test

Nothing in §5 is open.  The remaining named obligation in `PENDING_WORK` is the optional
general-`x` digit rendering of `blockFreqT` (`blockFreqT_eq_digits` already is general in `x`;
only the `OccursAt` corollary is stated for `G₄`).  Beyond that the campaign's own §8 outcome
conditions are met.
