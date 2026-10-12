# HANDOFF: prove `finiteCRT_moment_bound` (CoefmassRandomLambertMoment.lean)

**Branch `research/lambert-moment` is LOCAL ONLY.  Never `git push`.**  The repo is public, and this
is private research.

## Objective

Make `src/NormalNumbers/CoefmassRandomLambertMoment.lean` sorry-free, then check that
`#print axioms NormalNumbers.RandomLambertMoment.finiteCRT_moment_bound` shows only `propext`,
`Classical.choice` and `Quot.sound`.

- **Do not edit** the statement of `finiteCRT_moment_bound` or of the five copied definitions
  (`Prime`, `BernoulliLaw`, `randomLambert`, `weylMean`, `primeVariance`).  They are a frozen copy
  of a reviewed research statement.
- **Helper lemma statements** (steps 1-8) may be strengthened or split when a proof needs it.
- **If a helper is FALSE as stated**, stop.  Record the counterexample in this file, under
  "Findings", and leave the target alone.  The controls in
  `experiments/random_lambert_moment_controls.py` passed on every statement, so a false helper
  would be news.
- **No `axiom`.**  No new hypothesis on the target.

## Order of attack (cheapest first)

1. `bernMod_sq` and `bernMod_le_one`: complex-norm algebra.
2. `momentGamma_pos`: `cos(π/b) < 1` for `b ≥ 2`, then `exp(-c₀) < 1`.
3. `bernMod_tuplePhase_mod`.  `b^p - 1` divides `b^n - b^(n % p)`, so each coordinate's phase
   shifts by an integer times `h·sign`.  `ePh` is 1-periodic, and `bernMod` depends on `θ` only
   through `ePh θ`.
4. `crt_tuple_prod_mean`.  Use `ZMod.prodEquivPi` (Mathlib, `Data/ZMod/QuotientRing.lean`) or an
   induction on `F` using `Nat.Coprime.prod_right` and CRT for two coprime moduli.  Sums over
   `Fin d → Fin Q` reindex to `Fin d → ZMod Q`.
5. `prefix_tuple_mean_le`.  Hybrid argument: replace one coordinate at a time.  For one coordinate,
   `|avg_{n<N} g(n % Q) - avg_{r<Q} g(r)| ≤ Q/N` for `g` with values in `[0,1]` (write
   `N = aQ + r`).
6. `residueTuple_mean_sq`.  Expand `bernMod² = 1 - 2v + 2v·Re e(θ)` with `bernMod_sq`.  The average
   of `e(h Σ ε_i α(r_i))` over independent uniform `r_i` factorizes as `f^k · conj(f)^k = ‖f‖^(2k)`.
   Use `Fintype.sum_pow`/`Finset.prod_univ_sum`, together with
   `b^r/(b^p-1) = residuePhase b p r`.
7. `localMean_normSq_le`, the spectral gap: the main real-analysis lemma.  Paper argument:
   - Use `1 - ‖f‖² = p⁻² Σ_{r,t} (1 - cos 2πh(α_r - α_t))`.  Keep only the `2(p-K)` ordered pairs
     `{p-a₀, t}` with `t ≤ p-K-1`, where `a₀ = 1 + v_b(h)`, `K ≥ a₀` and `b^K ≥ 16|h|`.
   - `h α(p-a₀) = (h/b^{a₀})·(1 + 1/(b^p-1))`, and `h/b^{a₀} = h'/b` with `b ∤ h'`, so it is at
     least `1/b` from `ℤ`.
   - `|h α(t)| ≤ |h| b^{-K-1}·(1+…) ≤ 1/(16b)·(1+…)`.  So the distance to `ℤ` is at least
     `1/(2b)`, giving `1 - cos ≥ 1 - cos(π/b) = c₀`.
   - With `P₀ = 2K` and `p > P₀`: `2(p-K)c₀/p² ≥ c₀/p`.
8. `residueTuple_mean_le`.
   - Cauchy-Schwarz: avg `G` ≤ `√(avg G²)`.
   - `√(1-2x) ≤ e^{-x}` for `0 ≤ x ≤ 1/2`, with `x = v(1-‖f‖^{2k})` and `v ≤ 1/4`.
   - `‖f‖^{2k} ≤ (1-c₀/p)^k ≤ e^{-c₀k/p}`.
   - Chord/concavity: `1-e^{-c₀ s} ≥ (1-e^{-c₀})·s` on `[0,1]`, and `≥ 1-e^{-c₀}` for `s ≥ 1`.
   - `P₀` is the one from step 7.
9. `moment_le_tupleAvg`.  `‖A‖^{2k} = A^k·conj(A)^k`; expand over `Fin (2k) → Fin N`.
   - The integral of the finite sum is the sum of integrals.  Then use the triangle inequality,
     `‖∫‖ ≤ ∫‖‖`, and `bernMod` symmetry under `s = ±1`, since `|1-δ+δe(-θ)| = |1-δ+δe(θ)|`.
   - Per tuple, `e(Σ_i ε_i h b^{n_i}(c + sY))` is a unit phase from `c`, times
     `e(s Σ_p X_p θ_p(n))`.
   - Split the primes into `F` and the rest.  The rest is independent of the `F` coordinates, via
     `ProbabilityTheory.indep_iSup_of_disjoint` or `iIndepFun.indepFun_finset` plus truncation and
     dominated convergence.  Its expectation has modulus at most 1.
   - On `F`, `iIndepFun.integral_fun_prod_eq_prod_integral` (Probability/Independence/Integration)
     gives `∏ E e(X_p sθ_p) = ∏ ((1-δ)+δ e(sθ_p))`, whose modulus is `∏ bernMod`.
   - `randomLambert` is a `tsum`; `Summable` comes from geometric domination (`b ≥ 2`).
10. **Assemble the target.**
    - Take `P₀` from step 8 and `γ = momentGamma b`.
    - Step 9, then step 2: each prime factor is `p`-periodic.
    - Step 5 with `Q = ∏ p` and `d = 2k`; the product of `bernMod` lies in `[0,1]`.
    - Step 4 with `q = Subtype.val`.  Distinct primes are coprime: `Nat.coprime_primes`.
    - Step 8 at each prime, then `∏ exp = exp Σ`, using `primeVariance` and `p.val > P₀`.
    - Casts: `(2k : ℕ)` versus `2 * (k : ℝ)`, and `∏ (p.val : ℝ)` versus `((∏ p.val : ℕ) : ℝ)`.

## Gates

- Compile: `lake env lean src/NormalNumbers/CoefmassRandomLambertMoment.lean`.  Commits run the
  pre-commit `lake build`.
- One coherent green checkpoint per lap.  Update this file's "Status", commit, and NEVER push.

## Status

- Skeleton: 11 sorries, 0 errors.  Exact statement controls are green
  (`experiments/random_lambert_moment_controls.py`).

## Findings

(none yet)
