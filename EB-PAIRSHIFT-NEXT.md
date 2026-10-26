# EB c < 1 from the pair model only: plan (personal-c5, 2026-10-26)

**Target:** `src/NormalNumbers/CoefmassErdosBorweinPairShift.lean` sorry-free.  The headline is
`ebRandom_ae_normal_subpower_of_pairShift (hP : PairShiftKubiliusTV)`, the same conclusion as the
proved `ebRandom_ae_normal_subpower_of_multiShift`, without `MultiShiftKubiliusTV`.

## Frozen
- Never change `primePatternIoc`, `pairShiftMass`, `PairShiftKubiliusTV` or the headline statement
  (verbatim from the KB packet).  `PairShiftKubiliusTV` is a named hypothesis: never prove, weaken or
  axiomatize it.  **Do not use `MultiShiftKubiliusTV` anywhere in this proof.**
- Do not edit `CoefmassErdosBorweinMultiShift*.lean` or other existing files.  New lemmas go in
  `CoefmassErdosBorweinPairShiftAux.lean` (new).  You may *reuse* any proved lemma from them.
- The root `src/NormalNumbers.lean` runs a barrier audit that rejects untagged open sorries, so the
  PairShift file stays OUT of the root import list until it is sorry-free.  Add
  `import NormalNumbers.CoefmassErdosBorweinPairShift` to the root only once it is, then run the full
  `lake build`.
- No `native_decide`, no new `axiom`.  Commit locally; NEVER git push.

## Route (paper: draft section "Normal for c < 1 from a pair model only")
Copy the multishift headline's skeleton: `ebRandom_ae_normal_of_shiftedVariance_diverges` with the
same `multiShiftScheduleJ`, cutoffs, thresholds and `exists_multiShiftModerateParameters`.  The
deterministic part is unchanged: `low_shiftedVarianceMass_pattern_noHeavy` (low shifted variance ⇒
no heavy shift).  Replace the product-decay / single-TV step by Chebyshev:
1. `Z(n) = #{j ∈ active columns : H_j(n)}`, with `H_j` the heavy event of shift `j` (a function of
   `primePatternIoc P₀ y₀ (n + j + 1)` only; relate it to `multiShiftPattern` columns).
2. Chebyshev on `[1, N]`: `#{Z = 0}/N ≤ (E Z² − (E Z)²)/(E Z)²`.  It is a finite counting identity,
   with `E` = average over `n ∈ Icc 1 N`.
3. `E Z = Σ_j P_N(H_j)` and `E Z² = Σ_{i,j} P_N(H_i ∧ H_j)`.  Apply `PairShiftKubiliusTV` with
   `a = i+1`, `b = j+1` (`b − a ≤ J ≤ P₀`, `b ≤ N`), and with the single-shift marginal (a pair with
   `A = S ×ˢ univ`).  Each term is within `err(N) = C(e^{−u/C} + (log N)²/√N)` of the pair model.
4. Pair model: couple to two independent Bernoulli coordinates, TV `≤ Σ_{p > P₀} 1/p² ≤ 2/P₀`
   (reuse `sum_primeIndex_inv_sq_le`).  The single-coordinate law is the column law already used, so
   `q_j ≥ multiShiftScheduledColumnMass`-type lower bounds hold, and `Σ_j q_j → ∞`
   (`tendsto_multiShiftActiveExpColumnSum` / mixed variants).
5. Conclude `Var/E² ≤ 1/E Z + (J²·(2/P₀ + 2·err) + J·err)/(E Z)² → 0`.  `J²/P₀ → 0` is already
   proved (`tendsto_multiShiftCollisionError`), and `J²·err → 0` follows from
   `tendsto_multiShiftSieveExpError` / `...PowerError` with `J ↦ 2`.
Record a dated lap checkpoint at the bottom of this file each lap.
