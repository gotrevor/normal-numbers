# EB endpoint, Step 2 + assembly (FDEK-conditional) 🎯

**Objective:** make `src/NormalNumbers/CoefmassErdosBorweinEndpointEK.lean` sorry-free.  The headline
`ebPowerCandidateNormal_of_EK` must be axiom-clean: `[propext, Classical.choice, Quot.sound]`.

**Do not change** any statement in that file.  They are verbatim from the KB packet.  `ErdosKacFiniteDim` is
a named HYPOTHESIS; never prove or weaken it, and never add an axiom.  Helpers go above the
theorems or in a new `CoefmassErdosBorweinEndpointEKAux.lean`.  No `native_decide`.
**NEVER git push:** `research/eb-endpoint` is local only.

## Current checkpoint (2026-10-25)

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

Exactly one `sorry` remains, on `divisorVariance_diverges_at_ln2`.  The next load-bearing layer is
the deterministic implication from the new cutoff alternative and the two FDEK control coordinates
into a coordinatewise upper rectangle, followed by the FDEK closed-set estimate and the elementary
Gaussian grid bound.  Detailed baton: `HANDOFF-2026-10-25-eb-endpoint-ek.md`.

Paper: `~/personal/claude/knowledge/drafts/collatz-nn-mechanisms/nn-erdos-borwein-random-2026-10-12.md`,
section "Step 2".  Proved input: `ebRandom_ae_normal_of_divisorVariance_diverges` (Step 1, the
growing-moment criterion), in `CoefmassErdosBorweinEndpoint.lean`.

## Plan for `divisorVariance_diverges_at_ln2`

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
4. **No Turán–Kubilius needed.**  Control `ω(n+a₀) ≤ 2L` and the small primes by FDEK itself.
   - Add an extra grid point `s₀ < t₁` (and `t = 1`) to the FDEK grid.
   - Since `P₀ = exp(L²) ≤ y_{s₀}` eventually, `ω(≤ P₀) ≤ ω(≤ y_{s₀})`.
   - When no prime lies in `(P₀, y_{t_j}]`, `ω(≤ y_{t_j}) − t_j L ≤ (ω(≤ y_{s₀}) − s₀ L) − (t_j − s₀) L`,
     which is `< 0` off an FDEK-small set.
   - So on `{W ≤ T}`, minus FDEK-small sets, the normalized vector lies in the closed set
     `F_ε = {x : x_j ≤ ε for all grid j}`.
5. **Portmanteau** is already the form of `ErdosKacFiniteDim`: `limsup density ≤ brownianFDD(F_ε) + ε′`.
6. **Gaussian lemma** (elementary, no Brownian paths).  Take geometric times `t_j = r^{R−j}·τ`.
   - With `X_j = B_{t_j}/√t_j`: `X_j = √r·X_{j−1} + √(1−r)·Z_j`, with `Z_j` iid `N(0,1)`
     (from `brownianFDD`'s independent increments).
   - On `|X_{j−1}| ≤ M`, the event `X_j ≤ δ` needs `Z_j ≤ (δ + √r·M)/√(1−r)`, probability `≤ q < 1`.
   - So `P(all X_j ≤ δ) ≤ q^R + R·2e^{−M²/2}`.  Choose `M`, then `R`.  Note `ε/√t_j ≤ δ` for `ε` small.
   - This gives `brownianFDD(F_ε) → 0` along refining grids and `ε → 0`.
7. Conclude `density{W ≤ T} → 0`.

## Assembly
- `ebRandom_ae_normal_le_ln2_of_EK`: Step 1's criterion with `hdiv` from `divisorVariance_diverges_at_ln2`,
  applied to `v = δ(1−δ)` (nonnegative because `δ ∈ [0,1]` under `BernoulliLawNat`; check the def).
- `ebPowerCandidateNormal_of_EK`: for `0 < a ≤ ln 2` and `m ≥ 3`, `powerDelta a m ≤ 1/2` gives
  `δ(1−δ) ≥ δ/2 ≥ (log m)^{−ln 2}/2`, using `log m ≥ 1`.  `m = 2` is absorbed by the constant `c = 1/8`.

**Verify:** `lake build NormalNumbers.CoefmassErdosBorweinEndpointEK`, then `#print axioms` on the three
theorems.
