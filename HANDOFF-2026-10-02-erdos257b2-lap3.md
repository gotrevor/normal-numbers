# HANDOFF — Erdős #257 base 2 (prime subsets), lap 3 (2026-10-02)

Branch `proof/erdos257-base2`, HEAD after this file's commit. Tree clean, build green.
Scope: `sorry-free:src/NormalNumbers/Erdos257Base2.lean`, conditional on `CastingOut.TTEquidistributedDyadic`.

## Done this lap
- Headline `isDisjunctive_subsetLambert_two` + both corollaries PROVED from two lemmas:
  `veryLargeCovSupply_of_TT` (PROVED from leaves) and `exists_scheduleWitnessSC_two_of_supply` (N7, sorry).
- `G4SubsetWitnessCov`: `ScheduleWitnessSC` + `isDisjunctive_subsetLambert_of_witnessC` (proved).
- Finding: supply must CHOOSE X = 2^x, x ∈ [100,101]·2^{mE} (TT bad scales may hit the top block).
- N6 chain proved: `veryLargeCov_of_bins`, `abs_avg_le_blocks`, `exists_good_x`, `good_block_bound`,
  `binPair_cov` (TT per bin pair at X_T = Y^101, L = log X_T / C₅).

## Open leaves (all on path; see PENDING_WORK.md)
1. N5 `binInd_ap_mean` (G4Base2TTHyp.lean): inclusion–exclusion + rough-number count ≪ N/log X.
2. G4Base2Supply.lean: `exists_bins` (greedy), `abs_one_sub_binDelta_le`, `sum_inv_vlPrimes_le`
   (Mertens upper on (Y, Y^102]), `avg_binErr_le` (semiprime count + CRT).
3. N7 schedule at b=2 (Erdos257Base2.lean): port `SchedB.scheduleWitnessSE` with X=2^x variable,
   V=20000, κ ≤ 2^{-K/2}/(256K²); b≥3-only spots: gridB_bound, hN (clog), hfar, freqSeed.

## Check
Run `#print axioms Erdos257.isDisjunctive_subsetLambert_two` once leaves close; the build log shows
unrelated designated-open sorries (SwingC1, SwingC3Rotation, PrimeLambertOscillation) — confirm the
headline does not depend on them.
