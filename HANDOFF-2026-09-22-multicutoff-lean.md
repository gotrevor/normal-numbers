# HANDOFF 2026-09-22 — Pair A multicutoff formalisation (laps 0–5 done)

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


### Lap 3 — `src/NormalNumbers/PrimeModelBlockLevel.lean`
- `prod_le_of_block_bounds` : `|E ∩ B_i| ≤ m_i`, `B_i` topped by `w_i ≥ 1` ⟹
  `∏_{p∈E} p ≤ ∏_i w_i^{m_i}`.
- `sum_half_pow`, `sum_mul_half_pow` : exact finite identities
  `∑_{l<L}2^{−l} = 2 − 2·2^{−L}`, `∑_{l<L} l 2^{−l} = 2 − (2L+2)2^{−L}`.
- `level_sum_le` : `∑_{l<L}(64d+2u+2l+5)2^{−l} ≤ 128 d + 4u + 14`.

Deviation: Fable derives `128d+4u+12` and then adds a separate `log y₁` for the defect block's
extra prime.  Giving **every** block its uniform trace bound `r_i+1` (which is what the
coefficient rule hands you anyway) gives `128d+4u+14` in one geometric sum, no special case.

### Lap 4 — the graded arithmetic sieve
`src/NormalNumbers/PrimeModelRadicalCRTGraded.lean`
- `SieveCondD` (shift `< d p` at each sieve prime, plain `j p < p` at assigned primes),
  `card_sieve_graded`, `radical_sieve_admissible_card_graded` (exactly `∏_{p∈E} d p` classes),
  `radical_sieve_count_graded` (`|count − X ∏d/(Q D e)| ≤ ∏ d`).
  The CRT infrastructure of `PrimeModelRadicalCRT` is uniform in the local counts and is reused
  verbatim; only the local condition and the product of local counts change.

`src/NormalNumbers/PrimeModelBrunCountGraded.lean`
- `SiftedCondD`, `hitUD`, `weighted_counts_le_sifted_graded`,
  `brun_remainder_le_square_graded` (`∑_E |λ E| ∏_{p∈E} d p ≤ R²`, using `d p ≤ p`),
  `main_term_factor_graded`, and
- **`graded_sifted_count_lower`** :
  `#{n<X : SiftedCondD} ≥ X/(Q ∏_A p) · ∑_{E⊆U} λ(E) ∏_{p∈E}(d p/p) − R²`.

  The weights are **abstract** here: the arithmetic needs only (i) minorisation, (ii) `|λ|≤1`,
  (iii) support level `R`.  That is the interface the combinatorial half supplies.

`src/NormalNumbers/PrimeModelBlockWeights.lean` — the explicit weights
- `coefU`, `coefD`, `lamMain`, `lamDef`, **`blockLam`**;
  `sum_powerset_coefU/coefD` (powerset form of `bonfPoly`/`defectPoly`).
- `blockLam_expand` : `∑_{E⊆U} λ(E)∏_{p∈E}x_p = ∏_i U_i − ∑_i D_i ∏_{j≠i} U_j`.
- `blockLam_abs_le_one` (i), `blockLam_support` (iii), `blockLam_minorant` (ii).

  So **Lemma B is proved end to end for one concrete `λ`**.  `blockLam_abs_le_one` goes by the
  trichotomy on the excess set `T = {i : |E∩B_i| > r_i}` (`|T|=0` main term only, `|T|=1` that
  block's defect only, `|T|≥2` everything zero) — this is where Fable's asserted "supports are
  disjoint" is actually discharged.

`src/NormalNumbers/PrimeModelBlockSieveModel.lean` (lap 4d)
- `esymmAlt`, `esymmAlt_empty`, `esymmAlt_insert`
  (`P_{r+1}(insert a B) = P_{r+1}(B) − g_a P_r(B)`), and
- `esymmAlt_bonferroni` : even truncations `≥ ∏(1−g)`, odd truncations `≤`.  Induction on `B`
  with all `r` in the motive and **both parities together** — forced, since the step at one
  parity consumes the IH at the other.  This supplies `model_defect_eta`'s hypotheses
  `V ≤ E[U]` and `E[U] ≤ V(1+D̄)` for the real weights, with **no probability theory**: Fable's
  "product measure, blocks independent" is discharged as algebra on symmetric functions.

## Where the pieces meet

    laps 1,3,4c  →  (minorise, |λ|≤1, level R)  →  graded_sifted_count_lower   [arithmetic]
    laps 2,4d    →  (V ≤ E[U] ≤ V(1+D̄), D̄ ≤ e^{−u−l−2}, ∑D̄ ≤ 0.215T)
                 →  model_defect_eta : ∑_E λ ∏g ≥ (1 − 0.3T) ∏(1−g)          [model]

The only missing link between them is the **ring-generic form of `blockLam_expand`**: it is
currently stated for `x : α → ℤ`, and the model side needs `x = g : α → ℝ`.  `coefU`/`coefD` are
ℤ-valued and `prod_sum_powerset_disjoint` is already stated over an arbitrary commutative ring,
so this is a re-statement with `(blockLam … : ℝ)` casts, not new mathematics.

## Next, in order

1. `blockLam_expand` over `ℝ` (as above); then
   `∑_{E⊆U} λ(E)∏_{p∈E} g_p ≥ (1 − 0.3T) ∏_{p∈U}(1 − g_p)` by `model_defect_eta` +
   `esymmAlt_bonferroni` + `block_defect_le`.  Combined with `graded_sifted_count_lower` this is
   **Lemma B as the paper states it**, in arithmetic form.
2. Instantiate the block family: `B_{j,l} = U^{(j)} ∩ (y_j^{2^{−l−1}}, y_j^{2^{−l}}]`,
   `g_p = d_p/p`; `block_le_eight` (`PrimeModelPrimeDimension`) gives the `λ ≤ 8d` hypothesis of
   `block_defect_le`, and `2 d_p ≤ p` gives `g ≤ 1/2`.
3. Kickoff lap 5 (per-shift box, `retainedBox`, `radical_box_tail_exp20`).
4. Kickoff lap 6 — **Theorem A**, the graded `windowMeanLe`.
5. Kickoff lap 7 — **Theorem C′**, the headline
   `isNormal_subsetLambert_of_sqrtFreshMassZero`, through
   `isNormal_subsetLambert_of_KMT_along` (`G4WiringSparse`), mirroring
   `PrimeModelFamilyConsumer.lean`.  Schedule: Astra §8/§11.

## State

Branch `wip/g5-prime-subset`.  Working tree clean; every listed module is sorry-free and the
full `lake build` is green (9140 jobs).  No existing statement was edited;
`PrimeModelBrunLower.lean` untouched.  Nothing in the paper has been refuted — every step
checked so far went through as stated or better, and all five recorded deviations are
simplifications.

## Nothing refuted

Every paper step checked so far went through as stated or better.  No inequality failed.

The abstract (non-arithmetic) half of Lemma B is now complete: laps 4–6 are the arithmetic
instantiation, where `g_p = d_p/p`, blocks are `U^{(j)} ∩ (y_j^{2^{-l-1}}, y_j^{2^{-l}}]`, and
`block_le_eight` (`PrimeModelPrimeDimension`) supplies the `λ ≤ 8d` hypothesis of
`block_defect_le`.

---

## Laps 4e–4i — Lemma B closed end to end, and lap 5

### Lap 4e — `src/NormalNumbers/PrimeModelBlockWeightsReal.lean`
- `sum_powerset_coefU_real`, `sum_powerset_coefD_real`: the real powerset forms of the block
  Bonferroni polynomial and its defect, identified with `esymmAlt` / `esymmOn`.
- `blockLam_expand_real`: the expansion of `blockLam` against a **real** weight.
- `blockLam_model_lower`: `∑_{E⊆U} λ(E) ∏_E g ≥ (1 − 0.3T) ∏_U (1 − g)` from
  `model_defect_eta` + `esymmAlt_bonferroni`, with `Db i = e_{r_i+1}/V_i`.  No probability.
- `gradedDeg d u (j,l) = 64 d_j + 2 u_j + 2l + 4` (even), and `blockLam_model_lower_graded`:
  the same bound on the graded schedule, with the `0.215 T` hypothesis discharged by
  `block_defect_le` + `sum_block_defect_le`.  Only inputs: per-block mass `≤ 8 d_j`, `g ≤ 1/2`.

### Lap 4g–4h — `src/NormalNumbers/PrimeModelBlockFamily.lean`
- `cut y j l = y_j^{2^{-l}}`, `cut_sq`, `cut_antitone`, `one_le_cut`, `cut_eq_exp`.
- `gradedBlock U y (j,l) = U^{(j)} ∩ (cut y j (l+1), cut y j l]`; `gradedBlock_disjoint`
  (levels by the cutoff chain, shifts by hypothesis), `gradedBlock_mass_le`
  (`PrimeDensity.block_le_eight` gives `∑ 1/p ≤ 8`, so `∑ g ≤ 8 d_j`).
- `gradedBlock_model_lower`: Lemma B's model bound with **no abstract block hypotheses**.
- `gradedBlock_level_le`: **the support level**.  `blockLam_support` caps each trace at
  `r+1`, `prod_le_of_block_bounds` turns that into `∏_{p∈E} p ≤ ∏_{j,l} ⌊cut⌋^{r+1}`, and the
  geometric `level_sum_le` collapses it to `∏_j y_j^{128 d_j + 4 u_j + 14}`.

### Lap 4i — `src/NormalNumbers/PrimeModelGradedLemmaB.lean`
- `gradedLevel t d u y = ∏_j y_j^{128 d_j + 4 u_j + 14}`, `one_le_gradedLevel`.
- **`graded_brun_lower`** — *Lemma B as the paper states it*:

      #{n < X : SiftedCondD A W d_p j_p Q r}
        ≥ X/(Q ∏_A p) · (1 − 0.3 T) ∏_{p ∈ W} (1 − d_p/p) − R²

  for `W = ⋃_{j∈t, l<L} gradedBlock U y (j,l)`, `T = ∑_j e^{−u_j} ≤ 1`, `R = gradedLevel`.
  Hypotheses are elementary: `y_j ≥ 1`, disjoint prime sets `U^{(j)}`, `2 d_p ≤ p`,
  `d_p ≤ d_j` on `U^{(j)}`, cutoffs `≥ 2`, plus the usual `A`/`Q`/coprimality data.
  This joins `BrunGraded.graded_sifted_count_lower` to the combinatorial/model half.

### Lap 5 — `src/NormalNumbers/PrimeModelRadicalStateGraded.lean`
- `retainedBoxG k p T` with a **per-shift** threshold `T : Fin k → ℝ`;
  `retainedBoxG_card_le : #box ≤ ∏_j ⌊T_j⌋₊` (still independent of `#ι`).
- `sum_compl_retainedBoxG_le`, `radical_box_tailG` (per-shift Markov exponent `α_j` and
  budget `A_j`), and `radical_box_tailG_exp20`: tail `≤ ∑_j e^{20} / T_j^{1/(2 log y_j)}`
  with the arithmetic budget discharged by `radical_moment_budget`.

All sorry-free; `lake build` green; every headline `[propext, Classical.choice, Quot.sound]`.

## Next, in order

1. Kickoff lap 6 — **Theorem A**, the graded `windowMeanLe`: per-site E1 from
   `sum_omegaGt_shift_le`, graded model expectation with `A_{d_p}`, `A_j = 0` for `j < j₀`,
   `E5 = e^k exp(−S_P(2k, y_{j₀}))`, `Q = primorial (2k)`.  Inputs now available:
   `graded_brun_lower` (main term) and `radical_box_tailG_exp20` (tail).
2. Kickoff lap 7 — **Theorem C′**, the headline
   `isNormal_subsetLambert_of_sqrtFreshMassZero`, via `isNormal_subsetLambert_of_KMT_along`
   (`G4WiringSparse`), mirroring `PrimeModelFamilyConsumer.lean`.  Schedule: Astra §8/§11.

Nothing refuted: every paper step checked so far went through as stated or better.
