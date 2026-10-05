# HANDOFF 2026-10-05 — cantorexp lap 2

Branch `proof/cantorexp`.  `src/NormalNumbers/CantorExactExponent.lean` is **sorry-free**; both
headlines `exists_computable_mem_cantorSet_irrExponent_normal` and
`exists_mem_cantorSet_irrExponent_normal` depend only on `propext, Classical.choice, Quot.sound`.
Frozen statements untouched; `CantorExactExponentStretch.lean` untouched (open node).

## What closed the crux (`exists_exponent_tests`)
* Test depth `expL μ₀ m = ⌊μ₀ m⌋ + ⌊√m⌋`, test `expTest = hitB (expFree μ₀) m (expL μ₀ m)`.
* `expTest_mass_le`: deterministic bound `6·2^C·ρ^m + 2^{-(√m−2)/μ₀}` — run index `k` = first with
  `L < a_{k+1}+m+3`; BC case via `window_core` (σ = μ₀) + `hit_mass_bc`; triangle case via
  `hit_mass_tri` + `fc_tri_ge` (free count `≥ (s−2)/μ₀` from `[max(m,prevEnd k), a_k)` and
  `[E_k, min(L, a_{k+1}))`).  `ev_expTest_mass` makes it `≤ 1/(m+1)²` eventually.
* `hasIrrExponent_of_avoid`: Liouville hits at `n` fire scale `log₃ n`; vanishing tails fire all scales.
* Primrec: `expRunEnd_eq` (ceil = `(num·a+den−1)/den`), `nat_rec` for starts, generic `primrec_hitB`.
* `ae_not_liouvilleWith` = Borel–Cantelli on the same tests.
* Normality: `summable_sched_bound_gen`, `ev_sqrt_le_freeCount_exp`, `eA/eΨ/eW` + `e_ev` feed
  `CantorLiouvilleAll.exists_computable_normal_sched_family`.
* `not_isNormal_of_three_dvd_of_small` via `fract_lt_of_mem_run_exp` and `n ≥ 2a_k`.

## Next
Nothing open in scope.  The stretch range `2 < μ₀ ≤ 2 + log₂ 3` remains the open node.
