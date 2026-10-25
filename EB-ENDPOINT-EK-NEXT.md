# EB endpoint, Step 2 + assembly (FDEK-conditional) — COMPLETE 🎯

**Objective:** make `src/NormalNumbers/CoefmassErdosBorweinEndpointEK.lean` sorry-free.  The headline
`ebPowerCandidateNormal_of_EK` must be axiom-clean: `[propext, Classical.choice, Quot.sound]`.

**Do not change** any statement in that file.  They are verbatim from the KB packet.  `ErdosKacFiniteDim` is
a named HYPOTHESIS; never prove or weaken it, and never add an axiom.  Helpers go above the
theorems or in a new `CoefmassErdosBorweinEndpointEKAux.lean`.  No `native_decide`.
**NEVER git push:** `research/eb-endpoint` is local only.

## Current checkpoint (2026-10-25)

Lap 7 completed the scoped objective.  `CoefmassErdosBorweinEndpointEK.lean` is sorry-free; the
frozen theorem statements remain unchanged; `ErdosKacFiniteDim` remains exactly the planted named
hypothesis; and the Step-2 theorem plus both downstream headlines audit to the standard trust
triple only.  The final proof uses elementary Gaussian Chebyshev tails, the power grid
`R = q^8`, `delta = q^-2`, three closed FDEK events, and the previously proved deterministic walk
cap.  Full verification and proof architecture are in `HANDOFF-2026-10-25-eb-endpoint-ek.md`.

The assembly is closed.  `ebRandom_ae_normal_le_ln2_of_EK` now applies the Step-1 growing-moment
criterion to `divisorVariance_diverges_at_ln2`, and `ebPowerCandidateNormal_of_EK` follows from the
proved uniform variance lower bound `exists_powerDelta_variance_lower`.  Both frozen statements are
unchanged.

The deterministic chain is also closed in Lean.  `divisorVarianceMass_ge_primeChain_endpoint`
constructs exactly `2^(t-1)` distinct squarefree divisors ending at a prime `p`, proves that each
divides `n` and is at most `p^t`, and obtains

```text
2^(t-1) * c * (t * log p)^(-log 2) ≤ divisorVarianceMass v P n,
    t = omegaUpTo p n.
```

The pointwise walk cap is now closed too.  `walk_cap_analytic` takes logarithms in this inequality;
`omegaUpTo_sub_log_log_le_of_divisorVarianceMass_le` specializes it at a prime jump; and
`omegaUpTo_sub_log_log_le_of_divisorVarianceMass_le_of_le` proves the uniform form

```text
omegaUpTo p n - log (log p)
  ≤ 1 + log (2*L) + log (T/c) / log 2
```

whenever `W ≤ T` and `omegaUpTo p n ≤ 2*L`.

The finite-cutoff bridge is also closed.  `omegaUpTo_primeJump_or_eq_early` selects the largest
prime factor in `(P,y]`: either the count at `y` is attained at that prime jump, or it equals the
count at any earlier cutoff `x` with `P ≤ x ≤ y`.  Consequently
`omegaUpTo_cutoff_eq_early_or_sub_log_log_le` transfers the uniform walk cap to an arbitrary grid
cutoff, with the no-jump case returned as an exact equality to the early-grid count.

The lap-5 review closed the missing collision-cutoff comparison and corrected the probability
route.  `eventually_collisionCutoff_le_exp_log_rpow_add` puts `collisionCutoff N` below every fixed
positive shifted FDEK cutoff.  A fixed terminal threshold of one was insufficient (its Brownian
complement has nonzero limiting mass), so
`omegaUpTo_le_two_mul_of_normalized_terminal_le` now accepts a free threshold `A`, with
`eventually_const_le_sqrt` supplying `A ≤ √L`.

The concrete FDEK grid is now the equal grid `equalTimeGrid R`.  Its monotonicity, endpoint, and
variance-`1/R` increments are proved, and `brownianFDD_upperRectangle_equalTimeGrid` identifies a
constant Brownian upper rectangle exactly with the iid Gaussian partial-sum event
`gaussianPartialSumUpperSet`.  The soft Gaussian ballot proof has now been ported locally into
`CoefmassErdosBorweinEndpointEKAux.lean`, including fixed-variance rescaling and prefix-sum
identification.  `brownianFDD_upperRectangle_equalTimeGrid_le` gives the required fourth-root
equal-grid rectangle bound directly.

No `sorry` remains in the scoped file.  Detailed completion record:
`HANDOFF-2026-10-25-eb-endpoint-ek.md`.

Paper: `~/personal/claude/knowledge/drafts/collatz-nn-mechanisms/nn-erdos-borwein-random-2026-10-12.md`,
section "Step 2".  Proved input: `ebRandom_ae_normal_of_divisorVariance_diverges` (Step 1, the
growing-moment criterion), in `CoefmassErdosBorweinEndpoint.lean`.

## Completed plan for `divisorVariance_diverges_at_ln2`

Write `L = log log N` and `y_t = exp((log N)^t)`.

1. **Shift.**  FDEK is stated for `n`; the target uses `n + a₀`.  The filtered sets differ by at most
   `a₀` elements of `[1, N]`, so the densities differ by `≤ a₀/N`.
2. **Chain bound** (deterministic).  If `p ∣ n+a₀` is prime with `P₀ < p`, and `t = ω(n+a₀; ≤ p)`
   counts the primes `≤ p` dividing `n+a₀`, then the `2^{t−1}` squarefree divisors `p·d′` are
   distinct, `> P₀`, and `≤ p^t`.  So `W ≥ c·2^{t−1}·(t·log p)^{−ln 2}`.  Use only the lower bound
   on `v`, not monotonicity.
3. **Walk cap.**  On `W ≤ T`: at every prime `p ∣ n+a₀` with `P₀ < p`,
   `ω(n+a₀; ≤ p) − log log p ≤ C_T + log₂-ish(t)`.  Between primes the walk only decreases.  So at a
   grid time `t_j` with some prime of `n+a₀` in `(P₀, y_{t_j}]`,
   `ω(n+a₀; ≤ y_{t_j}) − t_j·L ≤ C_T + O(log L)`.
4. **No Turán–Kubilius needed.**  Use the equal grid `t_j = j/R` and control the first and terminal
   coordinates by FDEK itself.
   - `P₀ = exp(L²) ≤ y_{1/R}` eventually by
     `eventually_collisionCutoff_le_exp_log_rpow_add`.
   - Take the first-coordinate threshold `δ = R^{-1/4}`.  In the no-prime branch,
     `normalized_omegaUpTo_cutoff_le` propagates this bound from time `1/R` to every later grid
     time; in the jump branch the chain cap is eventually at most `δ√L`.
   - Take a separate free terminal threshold `A`.  Off `{B₁ ≥ A}`, the generalized terminal helper
     supplies `ω ≤ 2L`; unlike the old fixed threshold one, `A` can be sent to infinity.
   - Thus `{W ≤ T}` is contained in the constant `δ` upper rectangle, union the first-coordinate
     failure and terminal-coordinate failure.
5. **Portmanteau** is already the form of `ErdosKacFiniteDim`: `limsup density ≤ brownianFDD(F_ε) + ε′`.
6. **Gaussian lemma** (finite product only).  Port the sibling soft ballot estimate through
   `gaussianWalk_survival_probability_le_fourthRoot` and rescale it to increment variance `1/R`.
   `brownianFDD_upperRectangle_equalTimeGrid` is already the exact adapter.  At
   `δ = R^{-1/4}`, the rectangle bound is `O(R^{-1/8})`; Chebyshev gives first-coordinate failure
   at most `1/(Rδ²) = R^{-1/2}` and terminal failure at most `A^{-2}`.  Choose `A`, then `R`, then
   the portmanteau error.
7. Conclude `density{W ≤ T} → 0`.

## Assembly
- `ebRandom_ae_normal_le_ln2_of_EK`: Step 1's criterion with `hdiv` from `divisorVariance_diverges_at_ln2`,
  applied to `v = δ(1−δ)` (nonnegative because `δ ∈ [0,1]` under `BernoulliLawNat`; check the def).
- `ebPowerCandidateNormal_of_EK`: for `0 < a ≤ ln 2` and `m ≥ 3`, `powerDelta a m ≤ 1/2` gives
  `δ(1−δ) ≥ δ/2 ≥ (log m)^{−ln 2}/2`, using `log m ≥ 1`.  `m = 2` is absorbed by the constant `c = 1/8`.

**Verify:** `lake build NormalNumbers.CoefmassErdosBorweinEndpointEK`, then `#print axioms` on the three
theorems.
