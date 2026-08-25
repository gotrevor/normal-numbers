# HANDOFF — 2026-08-25 · image-Khinchin: variance bricks 1–3 DONE, MCT + Chebyshev remain

Branch `master`, HEAD `db0f421`, build 🟢 8760, working tree clean.

## State (real `#print axioms`, review lap #3 + grind #3b/c)
- **B5′ (10 headlines)**, **B6 single-map** `exists_cfNormal_and_affine_cfNormal`, **B6 Tier-2
  full affine family** `exists_cfNormal_and_affine_family_cfNormal'` (any real `r`, `q>0`) — ALL
  trust-triple `[propext, Classical.choice, Quot.sound]`. DONE + axiom-clean. Unchanged this lap.
- **The ONE open obligation in the repo**: `ae_tail_average_tendsto K` (`CFAeKhinchin.lean:756`,
  the sole live `sorry`), feeding `ae_khinchinTypical` (currently `+sorryAx`) ⇒ the **image-Khinchin
  headline**. This is the crux: a strong law (a.e. Birkhoff convergence) for the UNBOUNDED
  log-digit function under the Gauss measure. Route = L²→a.e. variance argument (Approach B, finite
  truncation), mirroring the PROVEN `ae_orbit_freq`. See DIRECTION.md CURRENT DIRECTIVE (review lap #3).
- The other two `src/` sorries (`CFScheduleA.lean:4400`, `:5774`) are DEAD/REFUTED schedule code —
  directive-FORBIDDEN, leave untouched.

## LANDED this lap (all in `CFAeKhinchin.lean`, all axiom-clean, green)
Bricks 1–3 of the variance route:
1. `integral_blockCount_cross` (+ `blockIndic_iterate_mul₂`, `integrable_blockIndic_iterate_mul₂`):
   cross 2nd-moment identity `∫ blockCount A n·blockCount B n = Σ_{i,j<n} γ.real(T⁻ⁱA∩T⁻ʲB)`.
2. `abs_cov_two_cyl_pair_le`: general-`(i,j)` two-cylinder covariance bound
   `|γ.real(T⁻ⁱ[a]∩T⁻ʲ[b]) − γ[a]γ[b]| ≤ 4(9/10)^{dist∸1}(|[b]|γ[a]+|[a]|γ[b])`.
3. Truncation defs `logBirkhoffTrunc`, `logTruncMean`; `integrable_blockCount_mul`;
   `integral_logBirkhoffTrunc_sq` (a), `sq_logTruncMean_eq` (b); constants `logTailC1/2/3` +
   `summable_logTailC1/2/3` + `_nonneg`; `logVarConst K = C₃+C₁²+176C₁C₂`;
   `sum_logMul_gaussMeasure_inter` (disjointness collapse); `inner_pair_bound` (the covariance
   fold to O(n)); and **`variance_truncated_le K M n`** :
   `|∫(logBirkhoffTrunc K M n)² − (n·logTruncMean K M)²| ≤ n·logVarConst K`, UNIFORM in M.

## NEXT STEPS (hardest-first) — bricks 4, 5, graft
4. **`variance_logBirkhoffSum_le K n`** : `|∫(logBirkhoffSum K n)² − (n·μ)²| ≤ n·logVarConst K`,
   `μ = ∫ logTailFn K = logTailC1 K`. MCT limit M→∞ on `variance_truncated_le`:
   - `logBirkhoffTrunc K M n ↑ logBirkhoffSum K n` a.e. as M→∞. Cleanest route: note
     `logBirkhoffTrunc K M n x = Σ_{a<M} log(K+1+a)·blockCount[K+1+a] n x = Σ_{i<n} f_M(gaussMapⁱ x)`
     where `f_M = Σ_{a<M} logTailTerm K a` (a Finset sum of `logTailTerm`), and
     `logBirkhoffSum K n x = Σ_{i<n} logTailFn K(gaussMapⁱ x)`. Since `logTailTerm K a ≥ 0` and
     `Σ'_a logTailTerm K a = logTailFn K` a.e. (`logTailTerm_tsum_ae_eq`, in `CFLogTail`), the partial
     sums `f_M ↑ logTailFn K` a.e. (monotone in M), so `f_M∘Tⁱ ↑ logTailFn K∘Tⁱ` (γ-preserving ⇒ the
     a.e. set pulls back), and the finite sum over `i<n` preserves ↑. [The identity
     `logBirkhoffTrunc = Σ_i f_M∘Tⁱ` needs: `blockCount[c] n x = Σ_{i<n} 1_{[c]}(Tⁱx)` = `Σ_{i<n} logTailTerm`
     coeff extraction — swap the finite `Σ_{a<M}` and `Σ_{i<n}`.]
   - `∫(logBirkhoffTrunc K M n)² ↑ ∫(logBirkhoffSum K n)²` by MCT (both nonneg squares, monotone;
     limit integrable via the uniform bound `∫(S_n^M)² ≤ (n·logTruncMean)² + n·logVarConst ≤ (n·μ)²+n·logVarConst`).
     Use `MeasureTheory.integral_tendsto_of_tendsto_of_monotone` OR go through `lintegral_iSup`.
   - `logTruncMean K M → μ`: partial sums of `logTailG(·+K)` → `∫ logTailFn K` via
     `integral_logTailFn_eq_of_hasSum`; note `logTruncMean K M ↑ logTailC1 K = μ` (monotone bounded).
   - Pass the (M-independent) RHS bound to the limit.
5. **`chebyshev_logBirkhoffSum` + `ae_tail_average_tendsto`**: TRANSCRIBE `chebyshev_blockCount`
   (`CFBlockFreq.lean`, Markov on `(S−nμ)²`) and `ae_orbit_freq` (`CFAeNormal.lean:81`, the FULL
   L²→a.e. skeleton: bad sets `E m k` on `p=(k+1)²`, per-`m` summability via Chebyshev, Borel–Cantelli
   `ae_eventually_notMem`, subsequence limit, monotone gap-squeeze). Substitutions:
   `blockCount A p` ↦ `logBirkhoffSum K p`, `γv` ↦ `μ`, variance const `(8|v|+80)γv` ↦ `logVarConst K`.
   Monotone gap-squeeze is available: `logBirkhoffSum K n` is ↑ in n (`logTailFn K ≥ 0`) and
   `logBirkhoffSum_nonneg` (both in `CFLogTail`).
6. **Graft**: `ae_khinchinTypical` becomes axiom-clean automatically; then intersect its co-null set
   into `exists_cfNormal_and_affine_family_cfNormal'` (one more null set in the `BadAll` union) ⇒
   image-Khinchin headline: witness CF-normal + all affine images CF-normal + Khinchin-typical.
   Re-`#print axioms` clean.

## Pointers
DIRECTION.md CURRENT DIRECTIVE (review lap #3) is the binding plan; PENDING_WORK.md top has the
detailed brick list + watch-outs; STATUS.md ledger refreshed this lap. Template lemmas to copy:
`ae_orbit_freq`/`chebyshev_blockCount`/`variance_blockCount_le` (`CFAeNormal.lean`/`CFBlockFreq.lean`).
