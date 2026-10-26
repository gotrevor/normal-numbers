# Normal above the sub-power weight for every `c < 1`, given the `J`-shift Kubilius model 🎯

**Objective:** make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free.  The headline
`ebRandom_ae_normal_subpower_of_multiShift` must be axiom-clean.

**Do not change** `subpowerWeight`, `primesIoc`, `multiShiftPattern`, `multiShiftMass`,
`MultiShiftKubiliusTV` or the headline: they are verbatim from the KB packet.  `MultiShiftKubiliusTV`
is a named HYPOTHESIS: never prove, weaken or axiomatize it.  Helpers go above the headline or in a
new `CoefmassErdosBorweinMultiShiftAux.lean`.  You may delete `private` on helpers in existing files,
and nothing else.  No `native_decide`, no new `axiom`.  **NEVER git push:** `research/eb-endpoint` is
local only.  If the hypothesis turns out to be FALSE as stated (a counterexample), record it
precisely and `box stuck`; do not route around it.

## Reuse (all PROVED in this repo)
- **Step 1′:** `NormalNumbers.ErdosBorweinShift.ebRandom_ae_normal_of_shiftedVariance_diverges`
  (CoefmassErdosBorweinShift.lean).  The headline is Step 1′ applied with `J N := ⌈√(log log N)⌉`
  (check `hJ`); all the work is its hypothesis `hdiv`.
- **Chain bound:** `divisorVarianceMass_ge_primeChain` and `card_primeChainDivisors`
  (CoefmassErdosBorweinEndpointEK.lean).
- **Kubilius-model technique:** `kubiliusMass_eq_bernoulliSubsetMass` and the block-sum lemmas in
  CoefmassErdosBorweinEndpointKub.lean, as patterns for turning a finite model mass into a product
  probability.
- **Mertens:** the repo's Mertens / `primeReciprocal` lemmas (grep `mertens`).

## Proof of `hdiv` (paper: draft section "Normal for c < 1 given the J-shift Kubilius model")
Fix `b ≥ 2`, `j₀`, `T`.  Let `L = log log N`, `J = J N`, `u = J·(log L)³`, `y₀ = ⌊N^{1/u}⌋`,
`P₀ = collisionCutoff N`, `L₀ = log log y₀`, and `ψ(x) = √(c x log x)` (for `c ≤ 0`, `ψ = 0`).
1. **Deterministic heavy ⇒ large mass.**  Let `X_j(n) = #{p ∈ (P₀, y₀] : p ∣ n+j}` and
   `μ₀ = Σ_{P₀<p≤y₀} 1/p`.  If `X_j(n) ≥ μ₀ + ψ(L₀) + 2j log₂ b + B log L` and `ω(n+j) ≤ 4L`, then
   `b^{−2j}·divisorVarianceMass … (n+j) > T`.  Use the chain bound at the largest prime of `n+j` in
   `(P₀, y₀]`, `hdelta`, monotonicity of `subpowerWeight` (eventually), and Mertens for `μ₀` vs
   `L₀ − log log P₀`.  Choose `B` large.
2. **Exceptional set.**  The density of `{n ≤ N : ∃ j ≤ J, ω(n+j) > 4L}` is
   `≤ J·(log 2N + 1)·2^{−4L} → 0` (Markov on `2^ω`, with `Σ_{m≤x} 2^{ω(m)} ≤ Σ τ ≤ x(log x + 1)`).
3. **Transfer.**  `{n : ∀ j ∈ [j₀, J), X_j(n) < threshold_j}` is a `multiShiftPattern P₀ y₀ J` event.
   Apply `hM` once (check `J ≤ P₀`, `2 ≤ y₀ ≤ N`, `C·J·log(J+2) ≤ log N/log y₀`).  The error is
   `C(e^{−(log L)³/C'} + (log N)^J/√N) → 0`.
4. **Model.**
   - Compare `multiShiftMass` directly with the fully independent product (each shift has its own
     Bernoulli(`1/p`)).  It is **not** literally the independent product conditioned on "at most
     one shift per prime": conditioning changes the singleton weights.  At one prime the exact TV
     is the independent law's total singleton deficit
     `J/p · (1 - (1 - 1/p)^(J-1)) ≤ J(J-1)/p²`; tensorize to get `≤ J²/P₀`.
   - Then `P(no heavy) = Π_{j}(1 − p_j) ≤ exp(−Σ_j p_j)`.
5. **Moderate-deviation LOWER bound** (pure probability; the main analytic risk).  For independent
   `B_p ~ Bernoulli(1/p)`, `S = Σ B_p`, mean `μ`, and `x = o(μ^{2/3})`:
   `P(S ≥ μ + x) ≥ exp(−(1+ε)x²/(2μ))` for large `μ`.  Proof by exponential tilting `θ = x/μ`, then
   Chebyshev under the tilted law on the window `[μ + x, μ + x + 2σ_θ]`.
6. **Sum.**  `p_j ≥ exp(−(1+ε)(ψ + 2j log₂ b + B log L)²/(2μ₀))`.  Summing over `j₀ ≤ j < J` gives
   `≳ L^{−c(1+ε)/2}·min(J, L/ψ) → ∞` because `c < 1`.  Choose `ε` with `c(1+ε) < 1`.

Order of attack: 5 (standalone probability lemma) → 4 → 1 → 2 → 3 → assemble via Step 1′.  Commit each
green lemma.

## Lap checkpoint (2026-10-26, lap 5)

Step 4's cleared-independent bridge is now exact in
`CoefmassErdosBorweinMultiShiftAux.lean`.  `singletonClearing` keeps a singleton shift subset and
maps every other subset to `none`; `independentShiftSubsetWeight_singletonClearing_fiber` proves
that its one-prime pushforward is exactly `clearedIndependentShiftWeight`.  The generic theorem
`finiteProductMass_pushforward` lifts a coordinatewise pushforward through arbitrary finite product
event masses, and `clearedProductMass_eq_independentClearedMass` specializes it to the multishift
model.

The collision cost is also proved locally.  `independentShiftCollisionMass_eq` computes

```text
P(card S ≥ 2) = 1 - (1-q)^J - Jq(1-q)^(J-1),
```

and `independentShiftCollisionMass_le` bounds it by `J(J-1)q²`.  Together with lap 4's
`categorical_cleared_product_comparison`, all one-prime and abstract product comparison inputs are
now in place and axiom-clean.

The next Step 4 attack is global: prove the finite-product union bound for the event that some prime
coordinate collides, transpose the independent prime-by-shift array, and apply the existing
Bernoulli cylinder factorization to obtain `P(no shift is heavy) = ∏_j (1-p_j)`.  Then identify
`multiShiftMass` with the categorical `finiteProductMass` after enumerating `primesIoc`, specialize
`q_i = 1/p_i`, and absorb both comparison errors by the reciprocal-square tail.  Detailed baton:
`HANDOFF-2026-10-26-eb-multishift-lap5.md`.

## Lap checkpoint (2026-10-26, lap 6)

The global part of Step 4 is now proved in `CoefmassErdosBorweinMultiShiftAux.lean`.
`independentShiftProductCollisionMass_le` is the finite-product collision union bound;
`singletonClearing_column_eq` proves that clearing preserves every column away from collisions.
`shiftArrayEquiv` transposes prime rows into a Bernoulli subset of `Fin n × Fin J`, and
`independentShiftProduct_card_lt_eq_prod_one_sub` proves the exact formula
`P(no shift is heavy) = ∏_j (1-p_j)`. Finally,
`categoricalShiftProduct_noHeavy_le_independent` combines both comparison losses and bounds the
categorical no-heavy mass by the independent one plus `2 ∑_i J(J-1)q_i²`. All are axiom-clean.

The next Step 4 attack is now the concrete specialization: enumerate `primesIoc P y`, identify
packet-verbatim `multiShiftMass` with the categorical `finiteProductMass` at `q_i=1/p_i`, translate
column counts to the resulting prime finsets, and bound the summed reciprocal squares by
`O(J²/P)`. Then Step 4 is ready to consume the already-proved moderate-deviation lower bound.
Detailed baton: `HANDOFF-2026-10-26-eb-multishift-lap6.md`.

## Lap checkpoint (2026-10-26, lap 7)

Step 4 is now complete in its concrete packet-verbatim form. `primeIndexEquiv` enumerates
`primesIoc`; `multiShiftMass_eq_finiteProductMass` proves exact equality with the categorical
finite product; `card_indexedMultiShiftPattern` transports column counts; and
`multiShiftMass_noHeavy_le_prod_one_sub` combines the abstract coupling, the exact independent
column factorization, and Mathlib's reciprocal-square tail to give

```text
multiShiftMass(no heavy)
  ≤ ∏_j (1 - independent heavy-column mass_j) + 2 J (J-1) / P.
```

The theorem is axiom-clean. No packet-verbatim statement changed, and no `native_decide`, axiom,
or new `sorry` was introduced. The next attack is Step 1: formalize deterministic
heavy-prime-count ⇒ large `divisorVarianceMass`, reusing `divisorVarianceMass_ge_primeChain`,
`card_primeChainDivisors`, `hdelta`, and the repo's Mertens estimates. Detailed baton:
`HANDOFF-2026-10-26-eb-multishift-lap7.md`.

## Lap checkpoint (2026-10-26, reflection lap 8)

Step 1's deterministic bridge is now proved, with a route simplification. Every divisor in the
selected prime chain divides `n+j`, so it is at most the global cutoff `M` (eventually `2N`). The
proved eventual antitonicity of `subpowerWeight` therefore gives the common lower bound at `M`
without any hypothesis on `omega(n+j)`. `divisorVarianceMass_ge_primeDivisorSet` supplies at least
`2^(r-1)` chain divisors from any `r` selected primes, and
`shiftedVarianceMass_gt_of_heavyColumn` turns the resulting explicit scalar inequality into the
required `shiftedVarianceMass > T` conclusion. All are axiom-clean.

This deletes the planned large-omega exceptional-set step entirely; the `B log L` threshold still
absorbs `log u + log log P` and the negligible difference between the square-root penalties at
`y0` and `2N`. The next attack is the scalar/schedule adapter: Mertens for `primesIoc`, eventual
cutoff facts, and an integer heavy threshold implying the new explicit chain inequality. In the
later probability step, split `c > 0` (moderate deviations) from `c <= 0` (a fixed-probability
central-tail lower bound), because the existing moderate theorem's large-deviation premise does
not apply directly when the square-root displacement vanishes. Detailed baton:
`HANDOFF-2026-10-26-eb-multishift-lap8.md`.
