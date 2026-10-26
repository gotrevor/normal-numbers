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

## Lap checkpoint (2026-10-26, lap 4)

Step 4's finite tensorization layer is now proved in
`CoefmassErdosBorweinMultiShiftAux.lean`.  `finiteProductWeight_l1_le` proves the product-law
`L¹` inequality, `abs_finiteProductMass_sub_le_half_l1` converts it to the sharp event/TV bound,
and `categorical_cleared_l1_eq` computes the exact one-prime defect.  Consequently
`categorical_cleared_product_comparison` gives, for arbitrary events,

```text
|P_categorical(A) - P_cleared-independent(A)|
  ≤ Σ_i J(J-1)q_i².
```

Here the cleared law retains independent singleton outcomes and merges every nonsingleton outcome
into `none`.  The next attack is the remaining half of Step 4: identify this law as the pushforward
of the fully independent `Finset (Fin J)` coordinates, bound the probability that clearing changes
any coordinate, and expose factorization of the per-shift heavy events.  Detailed baton:
`HANDOFF-2026-10-26-eb-multishift-lap4.md`.
