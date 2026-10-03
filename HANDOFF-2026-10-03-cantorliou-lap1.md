# HANDOFF 2026-10-03 — Cantor–Liouville (Bugeaud 10.37) lap 1

Branch `proof/cantorliou`, HEAD `87bbe2c5`.  Tree clean (only untracked `scratch/`, git-excluded).

## Done (all in `src/NormalNumbers/CantorLiouville.lean`)
* **Headline `exists_liouville_mem_cantorSet_isNormal_two` PROVED**, `#print axioms` = propext,
  Classical.choice, Quot.sound.  Unconditional.
* `secondMoment_le` proved by **Cassels' three-point route** (not the digit-change route):
  `three_point` (Σ_{t<3}|cos(x+2πt/3)| ≤ 2), `residue_sum_le` (induction over units mod 3^k),
  `block_sum` (orbit c·2^b bijects onto units, via `orderOf_two_zmod_three_pow`), `sum_Hf_le`,
  `good_shift`, `bad_count`, `pair_sum_le`, `secondMoment_expand`.  Constant inside the proof:
  C = 1 + 3(3^{e+1}+2), e = v₃|h|, c = log(3/2)/2 (uniform in h).
* Also proved: `charFun_norm_le` (via `charFun_real`, `pt_consB`, `coinMeasure_eq`),
  `ae_isNormal_two_of_secondMoment` (`tendsto_of_tendsto_sched`), `sched_ratio`, `le_freeCount`,
  `summable_sched_bound`, `ae_frequently_free`, `liouville_cantorLiouvilleReal`,
  `abs_cos_le_of_tdig_ne`, `sum_pow_changes` (hsep unused).

## Open: only `exists_computable_liouville_mem_cantorSet_isNormal_two`
Engine in progress, new modules (not yet imported by CantorLiouville):
* `VisitDeviationW.lean`: `visit_deviation_w` (visit deviation from ∫‖S_N(h)‖² ≤ (w h)² N²). DONE.
* `SchedDerandomize.lean`: B-style tests with N parameter, base 2 (`Vc`, `Tc`, `fails`, `failsTop`,
  `levelBad n N p`), counting lemmas, `block_prob_w`, `tail_prob_w`, `level_bound_w`
  (≤ 74016 n³ √(κ Wv) Zc, needs 8 ≤ n ≤ N, depth ≥ N+2n, second moment at N and N+n). DONE.

## Next steps
1. Schedule (primrec): s = Nat.sqrt j, `Ns j = 2^s * (2s+2+(j-s²))` (strict mono, ratio→1),
   resolution `nr j = Nat.sqrt (Nat.sqrt j) + 8`.  Prove `nr j ≤ Ns j`, ratio, → ∞.
2. Primrec of tests (copy `primrec_*_b` from ComputableNormalB with N param).
3. Assembly `exists_computable_normal_sched`: test j = (levelBad (nr j') (Ns j') > 0) ∨ bad' j'
   (j' = j + j₁), depth max(Ns+2nr, d' j'); hyps: hsm ∀h≠0 ∀N≥1 ∫ ≤ κ|h|N²W N, W antitone,
   ∃ j₀ ∀ j≥j₀ nr j^6 · W(Ns j) ≤ 1/(j+1)^4, bad' primrec with mass ≤ 1/(j+1)²; conclude
   computable e, IsNormal 2 (G e), ∃ j₁ ∀ j ≥ j₁ bad' j (pre e (d' j)) = false.  Use
   `Derandomize.exists_primrec_avoid`, `ComputableNormal.tsum_tail_le`, interpolation via
   `tendsto_div_of_monotone_of_exists_subseq_tendsto_div` + `equidistributed_of_badic`.
4. CL application: explicit secondMoment (κ=16 since 3^{e+1} ≤ 3|h|), W N = exp(-cF)+N^{-1/2};
   A p = Σ_{i<|p|} ptDigit/3^{i+1} (Ψ primrec in ℕ arithmetic), error ≤ 3^{-D} ≤ 2^{-D};
   bad' j = all coins false on [P_j, P_j+j+2), P_j = (j+2)·runStart j (free gap), d' j = P_j+j+2.
