# HANDOFF 2026-09-14 — G4 disjunctivity, lap 7 (`bigAvg` discharged to closed form)

Branch `wip/g4-disjunctivity`.  Prior HEAD `ef58e7c` (this lap's first commit); this file is in
the second.  Not pushed.  Build line: `lake build NormalNumbers.G4MediumPrimes` — green; the
pre-commit `lake build` (8888 jobs) is green.  Every headline prints
`[propext, Classical.choice, Quot.sound]`.

## Proved this lap (`src/NormalNumbers/G4MediumPrimes.lean`)

Tripwire `CHECK-g4-route-deviations.md §4` honoured: `bigAvg` is split at `Y`, the medium
range is L² with the signed cancellation, only `p > Y` is pointwise.

* `dvd_add_iff_modEq`, `filter_dvd_add_eq`, `filter_dvd_add_and_eq` — `p ∣ n+ρ` is one residue
  class; two coprime such conditions are one class mod `pp'` (`Nat.chineseRemainder`).
* `sum_sq_block_eq` — second moment = `∑_{p,p'}∑_{i,i'} c_i c_{i'} · pairCount`.
* `pairCount_diag_le`, `pairCount_diag_eq_zero`, `abs_pairCount_sub_le` — the three counts.
* **`sum_sq_block_le`** — the abstract signed L² bound (statement in `PENDING_WORK.md`).
* `sampleAvg_abs_le_sqrt` — Cauchy–Schwarz on the sample.
* `medPrimes`, `omegaVL`, **`omegaBig_split`** — `ω_{>R} = ω_{R<p≤Y} + ω_{>Y}`.
* `rowCoeff`, `blockSum_omegaOn_eq`, `sum_rowCoeff_eq_zero`, `sum_sq_rowCoeff_le`
  (`≤ 8^{−K}/15`), `sum_abs_rowCoeff_le` (`≤ 2^{−K}/3`).
* `sep_of_goodPrime`, `apSample_equidistributed` — the grid satisfies the abstract hypotheses.
* **`sum_sq_blockSum_med_le`**, **`sampleAvg_abs_blockSum_med_le`** (`≤ √medBudget`).
* `card_filter_gt_mul_log_le`, `omegaVL_le`, **`abs_blockSum_omegaVL_le`**.
* **`bigAvg_le`** — `bigAvg ≤ √medBudget + (log Mx/log Y)·2^{−K}/3`.
* `dyadicPrimes`, `card_dyadicPrimes_mul_le` (`k·#(2^k,2^{k+1}] ≤ 2^{k+2}`),
  `sum_inv_dyadicPrimes_le` (`≤ 4/k`), `sum_Icc_inv_le`, **`sum_inv_primes_Ioc_le`**,
  `sum_inv_medPrimes_le`.
* **`bigAvg_le'`** — closed form with `∑_{med}1/p ≤ 4(1+log⌊log₂Y⌋−log⌊log₂R⌋)` and `|med| ≤ Y`.

## Dependency map

`PropA` ✅ · `PropC` ✅ · `PropD` = `gridFrame_propD` from `bigAvg_le'` (✅ closed form, needs
only the §5 sizes) + `farAvg` (open) · `PropB` open (all inputs proved, assembly is labour)
· `PropJackson` open · §5 schedule open.  Nothing refuted.
`isDisjunctive_four_of_frames` remains CONDITIONAL on `SeparatingFrameExists`.

## Resume here

1. **`farAvg`** (`G4Remainder.farAvg`): `|farPart n a| ≤ 2^K · ∑_{j>J} ω(n+ρ_{α,j})/4^j`;
   bound `E_n ω(n+ρ)` on the AP by `log(E d)/log 2` via `2^ω ≤ d` and Jensen-by-hand, and
   `∑_{m<N} d(m) ≤ N(log N+1)` (`∑_k ⌊N/k⌋`).  Mind that `ρ_{α,j}` grows with `j`: bound
   `E ω(n+ρ_{α,j}) ≤ O(log(X + ρ_{α,j}))/log 2` and sum `4^{−j} log(jd_α + X)` — converges to
   `O(4^{−J}(J + log X + log d))`; that `log X = e^L` factor is fine only because `4^{−J}` with
   `J = ⌈3 log₂ L⌉` … CHECK: `4^{−J} log X = L^{−6} e^{L}` is NOT small.  The brief's far tail
   uses "the progression mean of ω up to the remote cutoff and a pointwise logarithmic bound
   beyond it" — the remote cutoff must be `j ≈ log X`-ish, and for `J < j ≤ j_remote` the
   AP-mean `O(L)` gives `2^K 4^{−J} L = o(η)`; beyond `j_remote`, `ω(m) ≤ log m/log 2` with
   `m ≤ X + j d`, giving `∑_{j>j_rem} 4^{−j} log(jd+X)` tiny.  So the split is `J < j ≤ j_rem`
   (AP mean) and `j > j_rem` (pointwise log).  Define `j_rem` in the module, not in §5.
2. `PropJackson`, B assembly, §5 schedule.
