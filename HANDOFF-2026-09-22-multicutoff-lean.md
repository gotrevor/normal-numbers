# HANDOFF 2026-09-22 — Pair A multicutoff formalisation (laps 0–2 done)

Branch `wip/g5-prime-subset`.  Running `KICKOFF-2026-09-22-multicutoff-lean.md` under the
2026-09-22 17:12 EDT attended override.  New modules only; no existing statement touched;
`PrimeModelBrunLower.lean` untouched.

## Landed (all sorry-free, `lake build` green, headlines `#print axioms` clean)

### Lap 0 — `src/NormalNumbers/PrimeModelSqrtFresh.lean`
- `SqrtFreshMassZero P` (Astra 11.1).
- `recipSumIoc_mono_left`, `recipSumIoc_split_le`, `recipSumIoc_of_le` (elementary).
- `recipSumIoc_le_rootChain_pow` : `M ≤ y^(2^K) → S_P(y,M) ≤ ρK` (integer induction).
- `recipSumIoc_le_rootChain` : **Astra 11.3**, `S_P(y,M) ≤ ρ ⌈log(log M/log y)/log 2⌉`.
- `sqrtFreshMassZero_of_freshMassZero`, `sqrtFreshMassZero_of_relDensityZero`.

Deviations from the paper (both simplifications, no loss):
- `recipSumIoc_split_le` is subadditive across **any** intermediate point, so the chain
  induction needs no ordering hypotheses and Astra's remark "the final overshoot below `y`
  is harmless" is automatic.
- For §11.4's relative-density leg the Mertens ratio is bounded unconditionally:
  `N ≤ (Nat.sqrt N)^3` for all `N ≥ 4` (from `N < (s+1)^2` and `s+2 ≤ s^2`), so
  `log N / log ⌊√N⌋ ≤ 3` and the constant is `δ(9 + 12 log 3)`, no eventual-`N` fudging.

### Lap 1 — `src/NormalNumbers/PrimeModelBlockSieve.lean` (pure combinatorics)
- `bonfPartial`, `bonfIndic`; `bonfPartial_succ` = the Bonferroni pair identity
  `∑_{i≤r}(−1)^i C(b+1,i) = (−1)^r C(b,r)`.
- `bonfIndic_le_bonfPartial` (`U ≥ I ≥ 0`), `bonfPartial_sub_le` (`U − D ≤ I`), even `r`.
- `prod_sub_prod_le`, `prod_le_prod_of_defect` : the telescoping minorant, over an arbitrary
  strict ordered commutative ring (needed so the ℤ-valued pointwise form reuses them).
- `sum_powersetCard_prod` : for a 0/1 weight, degree-`i` esym sum `= C(b,i)`.
- `bonfPoly_eq`, `defectPoly_eq`, `blockMinorant_le` = **Lemma B property 2, pointwise**.
- `sum_powerset_union_disjoint`, `prod_sum_powerset_disjoint` = **the coefficient rule**.

Deviation: the paper proves `λ(E) ∈ {−1,0,1}` by a three-case analysis on the block profile
plus a disjoint-supports argument.  `prod_sum_powerset_disjoint` shows
`λ(E) = ∏_i c_i(E ∩ B_i)` **by construction**, so `|λ| ≤ 1` and the support/level conditions
are inherited factor-by-factor.  The case analysis is never needed.

### Lap 2 — `src/NormalNumbers/PrimeModelBlockSieveModel.lean`
- `model_defect` : `E[L] ≥ (∏V)(1 − (∑D̄)e^{∑D̄})` from `V_i ≤ E[U_i] ≤ V_i(1+D̄_i)`.
  No division anywhere (`Finset.mul_prod_erase` instead of `∏_{j≠i}V_j = ∏V/V_i`).
- `exp_neg_two_mul_le_one_sub` : `e^{−2t} ≤ 1−t` on `[0,1/2]`, via `1/(1−t) ≤ 1+2t ≤ e^{2t}`.
- `esymmOn`, `esymmOn_insert` (Pascal recursion), `add_pow_ge_two_terms`,
  `factorial_mul_esymmOn_le` : **`k! e_k(g) ≤ (∑g)^k`**.  Not in mathlib (only the algebraic
  `MvPolynomial.esymm` theory exists).  Proved by induction on the block with `∀ k` in the
  motive, which avoids the usual double-counting `(k+1)e_{k+1} = ∑_p g_p e_k(B∖p)`.
- `pow_self_le_factorial_mul_exp` : `n^n ≤ n! e^n`.  `exp_one_div_eight_le` : `e/8 ≤ e^{−1}`.
- `block_defect_le` : **`e_{r+1}(g) ≤ e^{−u−l−2} ∏(1−g)`** for `r = 64d+2u+2l+4`,
  `g ≤ 1/2`, block mass `≤ 8d`.
- `geom_sum_le_inv_one_sub`, `sum_block_defect_le` (`∑_j∑_l e^{−u_j−l−2} ≤ 0.215 ∑_j e^{−u_j}`),
  `eta_bound` (`S e^S ≤ 0.3T`), `model_defect_eta` = **Lemma B property 3**, packaged:
  `E[L] ≥ (1 − 0.3T) ∏V` with `T = ∑_j e^{−u_j} ≤ 1`.

Deviations in the defect chain (both simplifications):
- Feeding `λ ≤ n/8` (equivalent to `λ ≤ 8d` given `n ≥ 64d`) into the factorial bound removes
  `d` from the exponent algebra entirely: `λ^n/n! ≤ (n/8)^n e^n/n^n = (e/8)^n`.
- `e/8 ≤ e^{−1}` replaces the paper's `e < 4` **and** `log 2 ≥ 1/2` pair; the remaining numeric
  step is the integer inequality `64d+2u+2l+5 ≥ 16d+u+l+2`.

## Nothing refuted

Every paper step checked so far went through as stated or better.  No inequality failed.

## Next (kickoff laps 3–7)

3. Support level `log R = ∑_j (128 d_j + 4u_j + 14) log y_j`; the geometric identity
   `∑_{l≥0}(64d+2u+2l+4)2^{−l} = 128d+4u+12` plus the defect block's one extra prime.
   With `prod_sum_powerset_disjoint` this is a bound on `∏_{p∈E} p` for each admissible
   profile, i.e. `∑_i (r_i + 1) log(top of block i)`.
4. Per-prime class counts (`SieveCond`/`SiftedCond`, `radical_sieve_count`, remainder `≤ R²`).
5. Per-shift box (`retainedBox`, `radical_box_tail_exp20`).
6. **Theorem A** (graded `windowMeanLe`).
7. **Theorem C′** = the headline
   `isNormal_subsetLambert_of_sqrtFreshMassZero`, through
   `isNormal_subsetLambert_of_KMT_along` (`G4WiringSparse`), mirroring
   `PrimeModelFamilyConsumer.lean`.  Schedule: Astra §8/§11 (`y_j = ⌊N^{u_N^{-2} 2^{-j}}⌋`,
   `Z_N = ⌈exp √log N⌉`, `ρ_N = sup_{q≥Z_N} r_P(q)`, `u_N = ⌊min(√w, ρ_N^{−1/2})⌋`).

The abstract (non-arithmetic) half of Lemma B is now complete: laps 4–6 are the arithmetic
instantiation, where `g_p = d_p/p`, blocks are `U^{(j)} ∩ (y_j^{2^{-l-1}}, y_j^{2^{-l}}]`, and
`block_le_eight` (`PrimeModelPrimeDimension`) supplies the `λ ≤ 8d` hypothesis of
`block_defect_le`.
