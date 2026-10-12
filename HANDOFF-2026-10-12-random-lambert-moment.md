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

- Lap 6 checkpoint (`research/lambert-moment`): proved `residueTuple_mean_le`, closing the entire
  finite local analytic layer.  Two reusable real inequalities now absorb the Cauchy--Schwarz
  square root into `exp (-x)` and lower-bound `1 - exp (-c t)` by its chord on `[0,1]` and its
  monotone continuation afterward.  The main proof combines the exact residue second moment with
  `localMean_normSq_le`, proves `‖localMean‖^(2k) ≤ exp(-c₀ k/p)`, and carries the sharp Bernoulli
  variance factor `δ(1-δ)` through to `momentGamma b * min(k/p,1)`.  Two declarations remain open;
  no frozen statement or definition changed.
- Exact verification run:
  - `lake env lean src/NormalNumbers/CoefmassRandomLambertMoment.lean` (green; only the two
    remaining disclosed `sorry` warnings).
  - `lake build NormalNumbers.CoefmassRandomLambertMoment` (green, 8716 jobs).
  - `lake env lean AuditRandomLambertMomentLap6.lean` with `#print axioms` for
    `sqrt_one_sub_two_mul_le_exp_neg`, `momentGamma_mul_min_le_one_sub_exp`, and
    `residueTuple_mean_le` (temporary audit file; each exactly `[propext, Classical.choice,
    Quot.sound]`).
  - `~/personal/bin/lean-green ~/src/nn-lambert-moment --target NormalNumbers.CoefmassRandomLambertMoment`
    (`✅ FORMALIZE-TIER GREEN`, 8716 jobs).
  - `python3 experiments/random_lambert_moment_controls.py` (all positive controls within
    tolerance; both deliberately false red controls fail as expected).
  - Commit pre-hook `lake build` (green, 10847 jobs).
- Current blocker: `moment_le_tupleAvg` is now the route-decisive obligation.  The remaining work is
  the probability-theoretic expansion of the `2k`-th moment and factorization of the finitely many
  Bernoulli coordinates in `F`, while controlling the complementary infinite Lambert sum by a
  unit-modulus factor.  Once it is proved, only final CRT/prefix assembly remains.
- Next highest-value attack: prove summability and measurability of `randomLambert`, truncate its
  prime `tsum` to finite sets, establish the finite independent-characteristic-function bound via
  `iIndepFun.integral_fun_prod_eq_prod_integral`, and pass to the limit by dominated convergence.
  This avoids requiring a direct independence theorem between a finite coordinate block and an
  infinite complementary `tsum`.

- Lap 5 checkpoint (`research/lambert-moment`): proved the route-decisive spectral gap
  `localMean_normSq_le`, leaving three declarations open.  The proof factors
  `|h| = b^e m` with `b ∤ m`, takes the explicit cutoff `K = e + 1 + 16|h|`, and proves that
  the anchor phase at `p-(e+1)` minus every tail phase below `p-K` lies within `1/(4b)` of
  `m/b`.  A modular-rational enclosure then puts each such phase in the central part of a
  period, giving the exact loss `spectralConst b`.  A reusable double-sum lemma retains both
  ordered anchor/tail arms, hence `2(p-K)` deficits; `p > 2K` converts their normalized loss
  into `spectralConst b / p`.  Negative `h` is handled by cosine evenness.  No frozen statement
  or definition changed.
- Exact verification run:
  - `lake env lean src/NormalNumbers/CoefmassRandomLambertMoment.lean` (green; only the three
    remaining disclosed `sorry` warnings).
  - `lake build NormalNumbers.CoefmassRandomLambertMoment` (green, 8716 jobs).
  - `~/personal/bin/lean-green ~/src/nn-lambert-moment --target NormalNumbers.CoefmassRandomLambertMoment`
    (`✅ FORMALIZE-TIER GREEN`, 8716 jobs).
  - Commit pre-hook `lake build` (green, 10847 jobs).
  - `python3 experiments/random_lambert_moment_controls.py` (all positive controls within
    tolerance; both deliberately false red controls fail as expected).
  - `lake env lean AuditRandomLambertMomentLap5.lean` with `#print axioms` for
    `rational_phase_central`, `cos_two_pi_le_of_near_rational`, `anchor_tail_phase_error`,
    `double_sum_le_of_anchor`, and `localMean_normSq_le` (temporary audit file; each exactly
    `[propext, Classical.choice, Quot.sound]`).
- Current blocker: `residueTuple_mean_le` is now the next obligation.  Its exact squared mean and
  the required spectral gap are both proved; what remains is a self-contained real-inequality
  chain implementing Cauchy--Schwarz, `sqrt(1-2x) ≤ exp(-x)`, the power/exponential comparison,
  and the chord bound defining `momentGamma b`.
- Next highest-value attack: prove the analytic helper inequalities used in step 8, then combine
  `residueTuple_mean_sq` with `localMean_normSq_le` to close `residueTuple_mean_le`.  After that,
  only the probability-theoretic expansion `moment_le_tupleAvg` and final CRT assembly remain.

- Lap 4 checkpoint (`research/lambert-moment`): factored the spectral-gap obligation into three
  proved, axiom-clean interfaces.  `localMean_norm_sq_eq` is the exact normalized double-cosine
  identity for the local mean, so the remaining work is now a real finite-sum deficit estimate.
  `cos_two_pi_le_cos_pi_div` turns membership in the central fractional interval
  `[1/(2b), 1-1/(2b)]` into precisely the required loss `spectralConst b`.  Finally,
  `anchor_phase_formula` computes the handoff's anchor residue `p-(e+1)` exactly when
  `|h| = b^e m`, isolating the nonintegral main term `m/b` from its finite-period correction.
  The four original declarations remain open; no frozen statement or definition changed.
- Exact verification run:
  - `lake env lean src/NormalNumbers/CoefmassRandomLambertMoment.lean` (green; only the four
    remaining disclosed `sorry` warnings).
  - `lake build NormalNumbers.CoefmassRandomLambertMoment` (green, 8716 jobs).
  - `~/personal/bin/lean-green ~/src/nn-lambert-moment --target NormalNumbers.CoefmassRandomLambertMoment`
    (`✅ FORMALIZE-TIER GREEN`, 8716 jobs).
  - Commit pre-hook `lake build` (green, 10847 jobs).
  - `lake env lean AuditRandomLambertMoment.lean` with `#print axioms` for
    `cos_two_pi_le_cos_pi_div`, `anchor_phase_formula`, and `localMean_norm_sq_eq` (temporary audit
    file; each exactly `[propext, Classical.choice, Quot.sound]`).
- Current blocker: finish the phase-enclosure half of `localMean_normSq_le`.  Choose
  `e,m` from `Nat.exists_eq_pow_mul_and_not_dvd` for `h.natAbs = b^e m`; after reducing the signed
  `m/b` main term modulo an integer, `¬ b ∣ m` gives distance at least `1/b` from the endpoints.
  It remains to bound the anchor correction and every tail phase `t < p-K` by a combined
  `≤ 1/(2b)`, then feed the resulting central-interval membership to the new cosine lemma.
- Next highest-value attack: prove a single signed phase-enclosure helper using
  `Nat.exists_eq_pow_mul_and_not_dvd`, with `K ≥ e+1` and `b^K ≥ 16|h|`; then use
  `localMean_norm_sq_eq` to retain the `2(p-K)` ordered anchor/tail pairs while bounding all other
  cosine terms by one.  The arithmetic `2(p-K)/p² ≥ 1/p` follows from `p > 2K` and closes
  `localMean_normSq_le`.

- Lap 3 review checkpoint (`research/lambert-moment`): proved both remaining finite averaging
  layers, `prefix_tuple_mean_le` and `residueTuple_mean_sq`.  The prefix proof first establishes
  the sharp one-coordinate block/remainder estimate (complete `Q`-blocks plus a tail bounded by
  `Q/N`), then applies it through a `Fin.consEquiv` head-tail induction; each coordinate costs one
  `Q/N`.  The residue proof expands the tuple phase into a product of `ePh` factors, applies
  `Fintype.prod_sum`, splits the first/last `k` signs into a power and its conjugate, identifies the
  normalized sum with `‖localMean‖^(2k)`, takes real parts, and finishes with `bernMod_sq`.  Four
  declarations remain open.
- Adversarial review result: the route still reaches the frozen headline with no statement drift.
  A zero-context diff scan against skeleton commit `54019320` found no change to `Prime`,
  `BernoulliLaw`, `randomLambert`, `weylMean`, `primeVariance`, or `finiteCRT_moment_bound`; the
  Python positive and red controls still pass.  No direction correction is warranted.
- Exact verification run:
  - `lake env lean src/NormalNumbers/CoefmassRandomLambertMoment.lean` (green; only the four
    remaining disclosed `sorry` warnings).
  - `lake build NormalNumbers.CoefmassRandomLambertMoment` (green, 8716 jobs).
  - `~/personal/bin/lean-green ~/src/nn-lambert-moment --target NormalNumbers.CoefmassRandomLambertMoment`
    (`✅ FORMALIZE-TIER GREEN`, 8716 jobs).
  - `python3 experiments/random_lambert_moment_controls.py` (all positive controls within
    tolerance; both deliberately false red controls fail as expected).
  - `lake env lean AuditRandomLambertMoment.lean` with `#print axioms` for
    `prefix_tuple_mean_le` and `residueTuple_mean_sq` (temporary audit file; each exactly
    `[propext, Classical.choice, Quot.sound]`).
- Current blocker: `localMean_normSq_le` is now the active route-decisive spectral-gap obligation.
  The finite identities on both sides of it are closed; downstream remain
  `residueTuple_mean_le`, `moment_le_tupleAvg`, and final assembly.
- Next highest-value attack: set `a₀ = padicValNat b h.natAbs + 1` and prove the anchor/small-tail
  phase-separation lemma for `r = p - a₀` and `t < p - K`, choosing `K ≥ a₀` with
  `b^K ≥ 16|h|`, then sum the resulting `2(p-K)` cosine deficits.  The fresh source check found
  that generic (not necessarily prime-base) `padicValNat` in `Mathlib/Data/Nat/MaxPowDiv.lean`
  supplies `pow_padicValNat_dvd` and `pow_dvd_iff_le_padicValNat`, so it matches the composite-base
  statement and avoids building a custom valuation.

- Lap 2 checkpoint (`research/lambert-moment`): proved `crt_tuple_prod_mean`.  The proof passes
  from the finset `F` to its subtype, installs positivity-derived `NeZero` instances for every
  modulus, constructs `ZMod.prodEquivPi`, and transports it through `ZMod.finEquiv` to an explicit
  equivalence
  `Fin (∏ i∈F, q i) ≃ (∀ i : F, Fin (q i))`.  A projection lemma proves that each coordinate is
  exactly reduction modulo `q i`; lifting the equivalence pointwise to `d`-tuples and using
  `Fintype.prod_sum` then gives the normalized product factorization.  Six declarations remain
  open.
- Exact verification run:
  - `lake env lean src/NormalNumbers/CoefmassRandomLambertMoment.lean` (green; only the six
    remaining disclosed `sorry` warnings).
  - `~/personal/bin/lean-green ~/src/nn-lambert-moment --target NormalNumbers.CoefmassRandomLambertMoment`
    (`✅ FORMALIZE-TIER GREEN`, 8716 jobs).
  - `lake env lean AuditRandomLambertMoment.lean` with
    `#print axioms NormalNumbers.RandomLambertMoment.crt_tuple_prod_mean` (temporary audit file;
    exactly `[propext, Classical.choice, Quot.sound]`).
- Current blocker: `prefix_tuple_mean_le` is now the active finite-averaging obligation.  It needs
  a coordinate-by-coordinate hybrid between `Fin N` and `Fin Q`; the clean route is induction on
  `d` using `Fin.consEquiv`, backed by the one-dimensional periodic prefix estimate obtained from
  `N = (N / Q) Q + N % Q`.  The analytic spectral-gap lemma remains the later route-decisive crux.
- Next highest-value attack: first prove the one-dimensional `[0,1]` periodic prefix estimate,
  then induct on tuple dimension via `Fin.consEquiv` to close `prefix_tuple_mean_le`; reuse the
  resulting tuple-sum reindexing in `residueTuple_mean_sq`.

- Lap 1 checkpoint (`research/lambert-moment`): proved `bernMod_sq`, `bernMod_le_one`,
  `bernMod_tuplePhase_mod`, and `momentGamma_pos`.  The periodicity proof is now grounded in the
  public integer-divisibility helpers `pow_sub_pow_mod_dvd` and `residuePhase_add_int`; it proves
  that every coordinate shift changes the tuple phase by an integer and then applies the proved
  one-periodicity of `ePh`.  Seven declarations remain open.
- Exact verification run:
  - `lake env lean src/NormalNumbers/CoefmassRandomLambertMoment.lean` (green; only the seven
    remaining disclosed `sorry` warnings).
  - `~/personal/bin/lean-green ~/src/nn-lambert-moment --target NormalNumbers.CoefmassRandomLambertMoment`
    (`✅ FORMALIZE-TIER GREEN`, 8716 jobs).
  - `python3 experiments/random_lambert_moment_controls.py` (all positive controls within tolerance;
    both deliberately false red controls fail as expected).
- Current blocker: the finite averaging layer is next; specifically, `crt_tuple_prod_mean` needs a
  clean reindexing between functions into `Fin (∏ i ∈ F, q i)` and the product of the residue
  function spaces.  The analytic spectral-gap lemma remains the later route-decisive crux.
- Next highest-value attack: prove `crt_tuple_prod_mean`, preferably via `ZMod.prodEquivPi`, then
  use its chosen reindexing machinery for `prefix_tuple_mean_le` before expanding the exact second
  moment.

## Findings

(none yet)
