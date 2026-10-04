# HANDOFF 2026-10-04 — cantorexp lap 1

Branch `proof/cantorexp`, HEAD `cf921653`, tree clean.  Scope: sorry-free
`src/NormalNumbers/CantorExactExponent.lean` (frozen statements untouched; Stretch file untouched).

## Done this lap
New generic file `src/NormalNumbers/CantorExpGeneric.lean` (any `free`):
head/tail split `hd`/`tl`/`pt_split`, separation `sep`/`agree_of_close`, sharp Frostman
`ball_le` (mass ≤ 2^{-F(n)}), sharp count `card_near_le'` (3·2^{F(m)}), window counts `fc`
(+ `fc_mono/add/le/of_free`, `freeCount_sub`, `coins_zero_window`), `hd_zero_ext`,
`digits_zero_of_dvd`, `pow_dvd_of_eq` (3-adic step), and the **prefix test** `hitB free m L`
(prefix length `L+1`): `hitB_of_near` (fires if `|x − pp/q| ≤ 2·3^{-(L+1)}`),
`near_of_hitB`, masses `hit_mass_bc` (≤ 6·3^m·2^{-fc(m+1, L-2)}) and `hit_mass_tri`
(next to a run `[a,E)` with `m+a+2 ≤ E`, `m+a+3 ≤ L`: ≤ 2^{-fc(m, L)}).

In `CantorExactExponent.lean`: schedule facts section, `cantorExpReal_trunc`,
`liouvilleWith_of_ne`, `window_core` (uniform in σ ∈ [μ₀, μ₀+1]); proved leaves
`expForced_recur, liouvilleWith_cantorExpReal, ae_frequently_two, abs_sub_ge_of_near,
coins_ball_le, card_near_le, window_freeCount_ge, summable_bc_of_threshold_lt,
freeCount_window_le_of_run, le_freeCount_exp`.

## Remaining (5)
`exists_exponent_tests` (crux), `ae_not_liouvilleWith`, `exists_computable_normal_avoid`,
`ae_isNormal_of_coprime_three`, `not_isNormal_of_three_dvd_of_small`.

## Plan for `exists_exponent_tests` (decided)
* `s = Nat.sqrt m`, `τ_m = μ₀ + 1/(s+1)`, `L m = (num·(s+1)+den)·m / (den·(s+1))` (= ⌊τ_m m⌋).
* `bad' j p = decide (J₀ ≤ j) && hitB (expFree μ₀) j (L j) p`, `d' j = L j + 1`; `J₀` from an
  `∀ᶠ m, mass ≤ 1/(m+1)²` lemma (non-constructive constant is fine).
* Mass per scale: `k` = max with `a_k + m + 3 ≤ L`.  Tri case (`m+a_k+2 ≤ E_k`): for `m ≥ E_{⌈μ₀⌉}`
  have `k > ⌈μ₀⌉`, so `[m,a_k)` free (gap k−1) and `fc m L ≥ (ε m − 2)/μ₀`; need
  `2^{-(√m−3)/μ₀} ≤ 1/(m+1)²` eventually (use `CantorLiouville.ev_log_le`).  BC case: apply
  `window_core` with σ = μ₀ at `(m+1, L−2)`; mass ≤ 6·2^C·ρ^m, ρ = 3·2^{-(μ₀−2)} < 1
  (`rho_lt_one`); `tendsto_pow_const_mul_const_pow_of_abs_lt_one`.
* Avoidance ⇒ HasIrrExponent: x ≠ any `hd a/3^a` (else test fires at all m ≥ a with q=3^m),
  lower bound by `liouvilleWith_of_ne`; upper: for τ > μ₀, hit `p/n` with `3^m ≤ n < 3^{m+1}`,
  `0 ≤ p ≤ n`, `C/n^τ ≤ 2/3^{L+1}` eventually ⇒ `hitB_of_near` contradiction.
* Primrec: `expRunStart` via `Primrec.nat_rec₁` (pattern `CantorLiouville.primrec_runStart`),
  `expRunEnd μ₀ a = (num·a + den − 1)/den`, `expFree` via indicator sum (pattern `isFree_eq`),
  `hitCnt` nested `primrec_sum_map`.
* `ae_not_liouvilleWith` then follows from the tests + Borel–Cantelli (or reprove directly).

## Normality leg
Generalize `CantorLiouville` Computable section (`clDig/clNum/clA/clΨ/clA_bounds/clW/cl_ev`)
to `free = expFree μ₀`; `cl_ev` needs only `√M/2 ≤ F(M)` eventually (from `le_freeCount_exp`).
Then `CantorLiouvilleAll.exists_computable_normal_sched_family` with `bad'`.
`ae_isNormal_of_coprime_three`: copy `CantorLiouvilleAll.ae_isNormal_of_coprime_three` with free swapped.

## Build gotcha
Box throws transient "Too many open files"/missing `.olean.server`; scripts in
`/tmp/claude-1000/{chk,bld}.sh` retry.  Pre-commit hook runs the full build (10760 jobs).
