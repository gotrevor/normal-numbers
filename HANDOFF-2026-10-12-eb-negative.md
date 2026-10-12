# HANDOFF: prove the EB negative side (CoefmassErdosBorweinNegative.lean)

**Branch `research/eb-random` is LOCAL ONLY.  Never `git push`.**  The repo is public, and this is
private research.

## Objective

Make `src/NormalNumbers/CoefmassErdosBorweinNegative.lean` sorry-free.  `#print axioms` for each
theorem must show only `propext`, `Classical.choice` and `Quot.sound`.

- **Do not edit** the statements of the four theorems or of the definitions `BernoulliLawNat`,
  `ebLambert` and `largeDivisorMass`.  They are verbatim copies of a reviewed research statement.
- Helper lemmas are free.  If a statement is FALSE, record a counterexample under "Findings" and
  stop.  No `axiom`.

## Paper proof (marginal-only; reviewed by codex2 at 95%)

Notation: `μ_M(n) = largeDivisorMass a M n = Σ_{d ∣ n, d > M} (log d)^{-a}`.

1. **`largeDivisorMass_moment_small`.**
   - Choose `0 < s ≤ 1` with `q = 2^s - 1 < a·s` (possible since `a > ln 2`: `(2^s-1)/s → ln 2`),
     and set `κ = a s - q > 0`.
   - For `y ≥ 2`, write `n_y` for the `y`-smooth part of `n`.  Then `τ(n_y)^s = Σ_{d ∣ n} g_y(d)`,
     where `g_y ≥ 0` is multiplicative, with `g_y(p^r) = (r+1)^s - r^s` for `p ≤ y` and `0` for
     `p > y`.  For EVERY `T ≥ 1`:
     `(1/T) Σ_{n≤T} τ(n_y)^s ≤ Σ_d g_y(d)/d = ∏_{p≤y}(1 + Σ_r g_y(p^r)/p^r)`
     `≤ ∏_{p≤y}(1 + q/p + 1/(p(p-1))) ≤ A_s (log y)^q`.
     The last step needs only an UPPER Mertens-type bound, `Σ_{p≤y} 1/p ≤ log log y + O(1)`.  Check
     Mathlib/repo for one; otherwise prove a crude version.  Any bound `≤ B·log log y + C` with
     `B·q < κ` would also do, so slack is available: pick `s` with margin.
   - Use dyadic blocks `2^ℓ < log d ≤ 2^{ℓ+1}`.  Their mass is at most
     `2^{-aℓ}·τ(n_{exp(2^{ℓ+1})})`, because every divisor `d ≤ y` divides `n_y`.
   - Subadditivity of `t ↦ t^s` (`0 < s ≤ 1`) gives `(1/T) Σ μ_M^s ≤ A_s 2^q Σ_{ℓ ≥ L} 2^{-κℓ}`.  This
     tends to 0 as `M = ⌈exp(2^L)⌉` grows.
2. **`typicalDivisorMass_small`.**  Markov on step 1.
3. **`ebRandom_ae_not_normal_of_marginal_bound`.**
   - Remove the head `m ≤ M`: the difference is a finite sum of rationals, and
     `NormalNumbers.WallRational.isNormal_rat_mul_add` (WallRational.lean ~l.1461) preserves
     normality.
   - Exact residual: `R_M(n) = Σ_{j≥1} b^{-j} D_M(n+j)`, where `D_M(t) = #{m > M selected : m ∣ t}`.
     `b^n Y_M - R_M(n) ∈ ℤ`, and `frac(b^n Y_M) ≤ R_M(n)`.  For each `m`, summing over `j` with
     `m ∣ n+j` gives `b^{n mod m}/(b^m-1)`.
   - Subadditivity and then Jensen (`E D^s ≤ (E D)^s`, with `E D_M(t) ≤ C μ_M(t)` from the
     marginals): `E frac^s ≤ C^s Σ_j b^{-js} μ_M(n+j)^s`.
   - Average over `n ≤ N`.  The shift by `j` costs at most a factor `1+j`, and `Σ (1+j) b^{-js} < ∞`.
   - **Normal-event lower bound (simplification: avoid integrals).**  Use
     `t^s ≥ 2^{-s}·1[t ≥ 1/2]`, and on the normality event the visit frequency of `[1/2, 1)` tends
     to `1/2`.  Use `NormalNumbers.isNormal_iff_equidistributed_orbit` (Wall.lean ~l.100) and the
     `visitCount` definition (RealDefs).  So `liminf (1/N) Σ frac^s ≥ 2^{-s-1}` there.
   - Fatou gives `P(normal_b)·2^{-s-1} ≤ C^s K_L Σ(1+j)b^{-js}`.  Let `L → ∞`.  Then
     `P(normal_b) = 0`, and a countable intersection over `b` finishes.
4. **`ebRandom_ae_not_normal`.**  `BernoulliLawNat` marginals satisfy the marginal bound: from
   `hdelta`, and `C ≥ 0` follows by taking `m = 2`.  Apply step 3.

## Gates

- Compile: `lake env lean src/NormalNumbers/CoefmassErdosBorweinNegative.lean`.  Commits run the
  pre-commit `lake build`.
- One green checkpoint per lap.  Update "Status", commit, NEVER push.

## Status

- **Lap 6 checkpoint (2026-10-12): marginal selected-divisor fractional moment proved; 1 sorry remains.**
  - PROVED summability of the Lambert denominators and every selected subseries
    (`summable_ebLambert_denom`, `summable_ebLambert_terms`), plus measurability of the full random
    Lambert sum (`measurable_ebLambert`).  These are the analytic prerequisites for the tail-orbit
    random variables.
  - DEFINED the real-valued finite divisor count `selectedDivisorCount X M n w`, and PROVED its
    nonnegativity, uniform finite bound, measurability, integrability, and exact expectation from
    the one-coordinate marginals (`integral_selectedDivisorCount`).
  - PROVED the load-bearing independence-free Jensen estimate
    `integral_selectedDivisorCount_rpow_le`:
    `E[D_M(n)^s] <= C^s * largeDivisorMass(a,M,n)^s` for `0 < s <= 1`.  This is the precise
    probabilistic bridge from the frozen marginal hypothesis to Lap 5's arithmetic moment bound;
    no joint law or independence is used.
  - A byte-level extraction/diff against introduction commit `3e4cac49` reconfirmed that all four
    frozen theorem statements and all three protected definition signatures are unchanged.  The
    sole remaining sorry is still `ebRandom_ae_not_normal_of_marginal_bound`.
  - Exact verification:
    - `lake env lean src/NormalNumbers/CoefmassErdosBorweinNegative.lean` — succeeds, exactly one
      expected sorry warning (`ebRandom_ae_not_normal_of_marginal_bound`).
    - `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinNegative --import
      NormalNumbers.CoefmassErdosBorweinNegative --axioms
      NormalNumbers.ErdosBorweinRandom.integral_selectedDivisorCount_rpow_le` — FORMALIZE-TIER
      GREEN; axioms exactly `propext`, `Classical.choice`, `Quot.sound`.
    - `~/personal/bin/lean-green .` — FORMALIZE-TIER GREEN, 10847 jobs.

- **Lap 5 checkpoint (2026-10-12): uniform large-divisor fractional moment proved; 1 sorry remains.**
  - PROVED `largeDivisorMass_moment_small`, the arithmetic/analytic half of the negative theorem.
    The proof partitions `largeDivisorMass` by an exact finite cutoff recursion
    (`largeDivisorMass_cutoff_step`, `largeDivisorMass_cutoff_iterate`,
    `largeDivisorMass_eq_block_sum`), avoiding a brittle explicit logarithmic block index.
  - PROVED finite fractional-power subadditivity in `rpow_finset_sum_le_sum_rpow` and the exact
    algebraic reduction `divisorBlockMomentBound_eq_geometric`: the one-block estimate is a fixed
    positive constant times `r^ℓ`, where `r = 2^{-(a*s-(2^s-1))} < 1`.  Summing the finite
    geometric tail uniformly in `N` closes the frozen theorem.
  - The four frozen theorem statements and the protected definitions are unchanged.  The only
    remaining sorry is `ebRandom_ae_not_normal_of_marginal_bound`; its corollaries
    `typicalDivisorMass_small` and `ebRandom_ae_not_normal` remain proved.
  - Exact verification:
    - `lake env lean src/NormalNumbers/CoefmassErdosBorweinNegative.lean` — succeeds, exactly one
      expected sorry warning (`ebRandom_ae_not_normal_of_marginal_bound`).
    - `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinNegative --import
      NormalNumbers.CoefmassErdosBorweinNegative --axioms
      NormalNumbers.ErdosBorweinRandom.largeDivisorMass_moment_small` — FORMALIZE-TIER GREEN;
      axioms exactly `propext`, `Classical.choice`, `Quot.sound`.
    - `~/personal/bin/lean-green .` — FORMALIZE-TIER GREEN, 10847 jobs.

- **Lap 4 checkpoint (2026-10-12): divisor-support bridge and block moment bound proved; 2 sorries remain.**
  - DEFINED the exact `y`-smooth part `smoothPart y n` and PROVED its factorization and prime-factor
    identities (`smoothPart_factorization`, `smoothPart_primeFactors`).  Consequently
    `smoothPart_card_divisors` identifies its number of divisors with `smoothDivisorCount y n`.
  - PROVED the requested cardinal bridge `card_divisors_filter_le_smoothDivisorCount`:
    every divisor `d | n` with `d ≤ y` divides `smoothPart y n`, so
    `#(n.divisors.filter (fun d => d ≤ y)) ≤ smoothDivisorCount y n`.
  - Introduced the fully discrete cutoffs `dyadicExpCutoff ℓ = 2^(2^ℓ)`, avoiding all
    `Nat.ceil (exp ·)` bookkeeping while preserving the exponent gap.  PROVED the one-block
    pointwise bound `divisorBlockMass_le` and the uniform averaged fractional-moment estimate
    `divisorBlockMass_rpow_sum_le`, which composes directly with Lap 3's smooth-divisor theorem.
  - Exact verification:
    - `lake env lean src/NormalNumbers/CoefmassErdosBorweinNegative.lean` — succeeds, exactly the
      two expected sorry warnings (`largeDivisorMass_moment_small` and
      `ebRandom_ae_not_normal_of_marginal_bound`).
    - `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinNegative --import
      NormalNumbers.CoefmassErdosBorweinNegative --axioms
      NormalNumbers.ErdosBorweinRandom.divisorBlockMass_rpow_sum_le` — FORMALIZE-TIER GREEN;
      axioms exactly `propext`, `Classical.choice`, `Quot.sound`.
    - `~/personal/bin/lean-green .` — FORMALIZE-TIER GREEN, 10847 jobs.

- **Lap 3 checkpoint (2026-10-12): exact uniform smooth-divisor averaging proved; 2 sorries remain.**
  - PROVED the formerly open combinatorial bridge `factorizationMajorant_sum_le`:
    `Σ_{n≤N} ∏_{p∈P,p∣n}(1+q v_p(n)) ≤ N * ∏_{p∈P}(1+q/(p-1))` for `q ≥ 0`
    and finite prime sets `P`.  The proof realizes the majorant as the divisor sum of a
    multiplicative arithmetic function, counts multiples exactly by `⌊N/d⌋`, and evaluates the
    resulting summable weight with mathlib's finite-prime Euler-product theorem.  This avoids the
    more brittle direct expansion into subsets and prime powers while retaining the exact `q`.
  - PROVED `smoothDivisorCount_rpow_sum_le_eulerProduct`, specializing the bridge to
    `P = y.primesLE` and `q = 2^s-1`, uniformly for every averaging cutoff `N`.
  - PROVED `smoothDivisorCount_rpow_sum_le_log_rpow`, composing the new bridge with Lap 2's sharp
    Mertens bound:
    `Σ_{n≤N} smoothDivisorCount(y,n)^s ≤ N * exp(q*mertensBound+1) * (log y)^q`.
    Thus the complete uniform smooth-divisor moment estimate is now discharged.
  - Fresh adversarial review rechecked the dependency route and the frozen interface against the
    introduction commit: all four theorem statements and the three protected definitions remain
    unchanged; no counterexample or hidden strengthening was found.
  - Exact verification:
    - `lake env lean src/NormalNumbers/CoefmassErdosBorweinNegative.lean` — succeeds, exactly the
      two expected sorry warnings (`largeDivisorMass_moment_small` and
      `ebRandom_ae_not_normal_of_marginal_bound`).
    - `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinNegative --import
      NormalNumbers.CoefmassErdosBorweinNegative --axioms
      NormalNumbers.ErdosBorweinRandom.smoothDivisorCount_rpow_sum_le_log_rpow` — FORMALIZE-TIER
      GREEN; axioms exactly `propext`, `Classical.choice`, `Quot.sound`.
    - `~/personal/bin/lean-green .` — FORMALIZE-TIER GREEN, 10847 jobs.

- **Lap 2 checkpoint (2026-10-12): sharp smooth-divisor Euler majorant proved; 2 sorries remain.**
  - PROVED the sharp local concavity bound `rpow_nat_succ_le_secant`:
    `(r+1)^s ≤ 1 + (2^s-1)r` for `0 < s ≤ 1`.  This avoids formalizing the exact increment
    function `g_y` while preserving the indispensable coefficient `q = 2^s-1`.
  - DEFINED `smoothDivisorCount y n` from the exponents of primes `p ≤ y` in `n`, and PROVED
    `smoothDivisorCount_rpow_le_factorizationMajorant`, bounding its fractional moment by
    `∏_{p≤y,p∣n}(1+q v_p(n))`.
  - PROVED the complete analytic Euler-product bound:
    `momentPrimeFactor_le`, `momentEulerProduct_le_exp`,
    `reciprocalPrimePowerError_sum_Icc`, `reciprocalPrimePowerError_sum_le_one`,
    `momentEulerProduct_le_mertens`, and finally `momentEulerProduct_le_log_rpow`:
    `∏_{p≤X}(1+q/(p-1)) ≤ exp(q*mertensBound+1) * (log X)^q`.
    Thus the exact exponent-`q` Mertens side of the uniform smooth-divisor estimate is discharged.
  - Exact verification:
    - `lake env lean src/NormalNumbers/CoefmassErdosBorweinNegative.lean` — succeeds, exactly the
      two expected sorry warnings (`largeDivisorMass_moment_small` and
      `ebRandom_ae_not_normal_of_marginal_bound`).
    - `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinNegative --import
      NormalNumbers.CoefmassErdosBorweinNegative --axioms
      NormalNumbers.ErdosBorweinRandom.momentEulerProduct_le_log_rpow` — FORMALIZE-TIER GREEN;
      axioms exactly `propext`, `Classical.choice`, `Quot.sound`.
    - `~/personal/bin/lean-green .` — FORMALIZE-TIER GREEN, 10847 jobs.

- **Lap 1 checkpoint (2026-10-12): 2 sorries remain; full repository green.**
  - PROVED `exists_erdosBorwein_moment_exponent`: for `a > log 2`, there is `0 < s ≤ 1` with
    `2^s - 1 < a*s`, via the right-hand secant limit at zero.  The proof is wired into
    `largeDivisorMass_moment_small`, so its remaining hole starts after the exponent choice.
  - PROVED `primeReciprocalMass_le_log_log_add`, reusing the axiom-clean bounded-error Mertens
    theorem `Erdos67.PrimeEstimates.abs_primeReciprocals_sub_log_log_le` (separately checked:
    `propext`, `Classical.choice`, `Quot.sound` only).
  - PROVED `typicalDivisorMass_small` from `largeDivisorMass_moment_small` by the finite Markov
    inequality at threshold `ε^s`.  Its statement is unchanged and was moved below its dependency.
  - PROVED `ebRandom_ae_not_normal` from the marginal-only theorem: `C ≥ 0` follows from the
    `m = 2` bound and positivity of `(log 2)^{-a}`, and the Bernoulli law supplies the marginals.
    Its statement is unchanged and was moved below its dependency.
  - Exact verification:
    - `lake env lean src/NormalNumbers/CoefmassErdosBorweinNegative.lean` — succeeds, exactly the
      two expected sorry warnings (`largeDivisorMass_moment_small` and
      `ebRandom_ae_not_normal_of_marginal_bound`).
    - `~/personal/bin/lean-green . --target ErdosProblems.Erdos67.PrimeEstimates --import
      ErdosProblems.Erdos67.PrimeEstimates --axioms
      Erdos67.PrimeEstimates.abs_primeReciprocals_sub_log_log_le` — FORMALIZE-TIER GREEN.
    - `~/personal/bin/lean-green .` — FORMALIZE-TIER GREEN, 10847 jobs.

### Current blocker / next attack

The sole open theorem is `ebRandom_ae_not_normal_of_marginal_bound`.  Both its arithmetic input and
the marginal-to-divisor-moment Jensen bridge are now complete.  Next define the Lambert tail above
`M` and the shift residual
`R_M(n,w) = sum_{j>=1} b^(-j) * selectedDivisorCount X M (n+j) w`.  Prove its
summability/measurability, the exact residual identity modulo an integer, infinite fractional-power
subadditivity, and the integrated Cesàro estimate using `integral_selectedDivisorCount_rpow_le` and
`largeDivisorMass_moment_small`.  The short, already kernel-checked quotient identity
`residuePhase_add_int` in `CoefmassRandomLambertMoment.lean` (~lines 145--166) is a useful template:
`b^n/(b^m-1) = b^(n % m)/(b^m-1) + z` for an integer `z`.  For residual summability, the crude bound
`selectedDivisorCount X M (n+j) w <= (n+j).divisors.card <= n+j` is enough against the geometric
weight.

For the probability/orbit close, avoid first proving that the `IsNormal` event is measurable (no
such repository lemma was found).  Instead, for each base majorize the normal set by a measurable
level set of the `liminf` of the tail-orbit Cesàro averages.  Normality supplies the positive lower
bound through `isNormal_iff_equidistributed_orbit` and visits to `[1/2,1)`; Fatou bounds that level
set by the integrated moment estimate.  Let the arithmetic cutoff tend to infinity, use Wall's
`isNormal_rat_mul_add` to restore the finite rational head, then take the countable intersection in
`b`.  The route-decisive first checkpoint is the exact residual plus integrated moment estimate;
the final checkpoint is the measurable-liminf/Fatou and normal-orbit contradiction.

## Findings

- The arithmetic-function route gives the exact desired Euler factor `1 + q/(p-1)` directly;
  no coefficient slack or extra prime-power error is introduced by the averaging step.
