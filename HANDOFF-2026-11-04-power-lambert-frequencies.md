# HANDOFF 2026-11-04: every word frequency of a perfect-power Lambert constant exists (DONE)

Branch `wip/power-lambert-frequencies`, worktree `~/src/nn-freq`.  Kickoff:
`KICKOFF-2026-11-04-power-lambert-frequencies.md`.

## Operator note (lap 1, kept for the record)

Lap 1 was OOM-killed while running three `lake build`s in parallel.  Build discipline on this box:
ONE `lake build <Module>` at a time, foreground; check single files with `lake env lean <file>`;
commit each green file at once (pathspec only).  Lap 2 followed this and harvested lap 1's
untracked drafts (`PowerLambertRuns`, `PowerLambertWindow` built as-is; `PowerLambertNearZero`
needed five `omega` repairs: a `change` so the reflected window sum is the `set` variable `g`,
and `generalize` of the nonlinear products `(b-1)*(L-1)` and of `2^r` before `omega`).

## Result

Both frozen statements of `src/NormalNumbers/PowerLambertFrequenciesExist.lean` are proved,
byte-identical to kickoff commit `9a8624e4` (only the two `sorry`s and two imports changed):

    #print axioms powerLambert_nearZero_density
      [propext, Classical.choice, Quot.sound]
    #print axioms powerLambertFrequenciesExist
      [propext, Classical.choice, Quot.sound]

So for `b, r ≥ 2` every base-`b` word has a limiting frequency in `Σ_{n≥1} 1/(b^{n^r} − 1)`;
with `not_isNormal_powerLambert` the law is non-uniform.  The gate file is now imported from the
root `src/NormalNumbers.lean` (with `PowerLambertRuns/Window/NearZero/PeriodicApprox/Frequencies`).

## Files and route

* `PowerLambertRuns.lean`: carry chains `carry_le_of_dvd_succ` (all digits `b−1`) and
  `carry_le_of_dvd` (all digits `0`, chain started within `P` positions); `powerHead`,
  `powerWindow`, `powerTail`, `powerLambert_mul_pow` (`S b^N = H_N + T_N`); run events as
  divisibilities `dvd_powerWindow_of_orbit_lt`, `dvd_powerWindow_succ_of_le_orbit`.
* `PowerLambertWindow.lean`: divisor-sum swap `sum_card_powerDivisors_filter_le`, mean
  `sum_powerDivisorCount_le` (`≤ 2X`), averaged tail `sum_range_tail_le`, small-root rigidity
  `sum_window_le` (`L + (11/12)L + K + big roots`), big-root average
  `sum_range_bigRoot_window_le`.
* `PowerLambertNearZero.lean`: `two_mul_le_of_run` (a run forces `2L ≤ window sum + ⌊T⌋ + 2^r
  + 2`; base 2 via `c = 1 + c'` and `P = 2^r`), Markov, `powerLambert_nearZero_density_aux`.
* `PowerLambertPeriodicApprox.lean` (parts B–D, simpler than the kickoff's sandwich):
  - `abs_card_filter_div_sub_le`: periodic averages, error `≤ Q/N`.
  - `mem_Ico_iff_of_fract_add`: with `0 ≤ R < η ≤ 1`, `{v+R}` and `v` agree on `[α,β)` unless
    `{v+R}` lies in `[α,α+η)`, `[β,β+η)` or `[0,η)`.
  - `orbit_shift_lt_of_mem_Ico`: each of those three windows (all of form `[k/b^ℓ, k/b^ℓ + η)`,
    `η = 1/b^(L+ℓ)`) forces `orbit (n+ℓ) < 1/b^L`: only the one-sided near-zero event is needed.
  - `sum_range_aperiodicTail_le`: `Σ_{n<N} R_Q(n) ≤ (2/(D+1))(N+2)`.
  - `exists_eventually_abs_wordFreq_sub_le`: `|freq_N(w) − G_Q| ≤ ε` eventually, `G_Q` the
    frequency in the `Q = (D!)^r`-periodic model; `powerLambertFrequenciesExist_aux` (Cauchy).

## Sanity table (stretch, numerics only, not in Lean)

Digit frequencies of `Σ 1/(10^{n^2} − 1)` over the first 200000 digits (exact carry
propagation of `Σ c(m) 10^{-m}`, `c(m) = #{d : d^2 ∣ m}`):

| digit | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|---|
| freq | .00055 | .60621 | .27759 | .04702 | .04917 | .00253 | .01166 | .00016 | .00454 | .00059 |

## Not done (stretch, optional)

Identify the limit as `lim_D G_D(w)` in Lean (it is implicit in
`exists_eventually_abs_wordFreq_sub_le`: the limit is within `ε` of `G_{Q(ε)}`).
