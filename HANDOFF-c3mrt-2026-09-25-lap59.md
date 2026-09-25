# HANDOFF c3-mrt 2026-09-25 lap59 — obligation A, brick 4a: the class-indexed log rung is PROVED

**New file** `src/NormalNumbers/C3MrtProgChase.lean` (chain tip:
`lake build NormalNumbers.C3MrtProgChase`, 8990 jobs).  Sorry-free, 4 declarations, trust triple.
`lake build` green (9257).  Every declaration landed first try.

## Result

**`progression_log_rung_class`** — for every `K ≥ 1`, every modulus `Mo ≥ 1` and every residue `r`,
on `KPointLogElliott K` + `TwistedPrimeSumSavingAllLevels` ALONE:

    ∀ ε > 0, ∃ C N₀, ∀ N ≥ N₀,
      ‖∑_{n < N, n ≡ r (Mo)} harmW n · ∏_{i<K} z_i^{ω(n+i+1)}‖ ≤ C + ε·log N .

That is obligation A in *class-indexed* form.  Ingredients:

* `progLcm_le_mul_pow` — `lcm(Mo, lcm d) ≤ Mo·Y^K`, the only arithmetic that changed.  The
  threshold `N₀ = Y^K·A^I + Y^K + 2` becomes `Mo·Y^K·A^I + Mo·Y^K + 2`; `Mo` is quantified before
  `N`, so the budget `K^{K²}` and the truncation are untouched.
* `multi_correlation_of_uniform_rung_prog` — the ε-chase over the class (lap 49 transcribed).
* `rung_multi_uniform_prog` — the uniform rung over the progression-admissible
  `Fintype.piFinset (range (Y+1)) ×ˢ range (Mo·Y^K + 1)`, via `nondegenerateForms_prog` (lap 56).

## NEXT — brick 4b, the weight bridge (then obligation A is a theorem)

`ProgressionLogRung K` (as stated in `C3MrtNatural`) uses the **progression-variable** weight
`(m+1)⁻¹` on `∏ z_i^{ω(Mo·m + r + i + 1)}`, whereas brick 4a delivers the **class** weight
`harmW n = (n+1)⁻¹` on `∏ z_i^{ω(n+i+1)}` over `n ≡ r (Mo)`.  The bridge:

    (m+1)⁻¹  −  Mo·(Mo·m + r + 1)⁻¹  =  (r + 1 − Mo) / ((m+1)(Mo·m + r + 1)) ,

whose absolute value is `≤ Mo/(m+1)²`, and `∑_m (m+1)⁻²` converges — `sum_inv_sq_le`
(`C3MrtRungTwo:372`) is already in the repo for exactly this.  So

    ∑_{m<J} (m+1)⁻¹ G m = Mo · ∑_{n<N, n≡r} harmW n · G((n−r)/Mo) + O_Mo(1) ,

an `N`-independent error.  Scaling `ε ↦ ε/Mo` absorbs the factor `Mo`, so brick 4a gives
`ProgressionLogRung K` outright.  (`class_sum_reindex`, lap 53, does the index bookkeeping.)

After that the ledger's only open item is `LogToNaturalCorrelation` (the log-Chowla ⇏ Chowla
barrier) plus the `D`-uniformity/rate bookkeeping pinned in lap 40.
