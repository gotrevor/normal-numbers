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

- Skeleton: 4 sorries, compiles.

## Findings

(none yet)
