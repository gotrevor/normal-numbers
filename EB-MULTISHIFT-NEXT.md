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

## Lap checkpoint (2026-10-26, lap 9)

The positive-`c` model adapter is now concrete. `mertens_primesIoc_bound` specializes the repo's
proved Mertens theorem to the packet-verbatim block `primesIoc P y`, with mean
`log log y - log log P + O(1)`. Enumeration and column-sum lemmas identify that mean exactly in
every shift column, while `sum_shiftArrayColumn_inv_sq_le` gives square-mass at most `1/P`.

`multiShiftColumnMass_ge_moderate` now applies the lap-3 finite moderate-deviation theorem directly
to one shift column and uses the Bernoulli cylinder identity to return the probability in exactly
the full prime-by-shift universe occurring in `multiShiftMass_noHeavy_le_prod_one_sub`. Thus Steps
4 and 5 are connected without any remaining finite-model bookkeeping; a threshold
`ceil(mean + x_j)` is converted to its real inequality by `Nat.ceil_le`. All new theorems are
axiom-clean. No packet-verbatim statement changed, and no `native_decide`, axiom, or new `sorry`
was introduced.

The next attack is the asymptotic schedule itself: define `J(N)`, `u(N)`, and `y0(N)`; choose the
integer thresholds `ceil(mean + x_j)`; and prove eventually both the explicit chain scalar premise
of `shiftedVarianceMass_gt_of_heavyColumn` and the hypotheses of
`multiShiftColumnMass_ge_moderate`. Then sum the column lower bounds, send the product and collision
error to zero, and apply `hM`. The `c <= 0` branch still needs the fixed-probability central-tail
variant rather than the moderate-deviation theorem. Detailed baton:
`HANDOFF-2026-10-26-eb-multishift-lap9.md`.

## Lap checkpoint (2026-10-26, lap 10)

Step 3's finite transfer layer is now proved. `low_shiftedVarianceMass_pattern_noHeavy` shows that
every low shifted-mass sample lies in the no-heavy pattern event: active columns use lap 8's
prime-chain scalar bridge, while inactive columns receive the impossible threshold
`card (primesIoc P y) + 1`. `low_shiftedVarianceMass_density_le_model` then turns any one-use
total-variation estimate into the required density upper bound. The square-root schedule
`multiShiftScheduleJ` is defined, tends to infinity, and eventually satisfies Step 1's condition
`J(N) <= log log N`.

The planned separate `c <= 0` central-tail theorem is unnecessary. The proved wrapper
`multiShiftColumnMass_ge_moderate_of_baseline` shows that a fixed sufficiently large
`A * sqrt(mean)` buffer discharges the existing moderate-deviation theorem's large-deviation and
absorption hypotheses. Use this buffer in every threshold. For `c <= 0` it gives a fixed positive
column probability across order `sqrt L` active shifts; for `0 < c < 1` it is lower order than
`sqrt(c L log L)` and does not change the exponent.

The next attack is the remaining scalar schedule: define the variable cutoff `y(N)`, prove its
Mertens mean is `L - O(log L)`, and bundle the eventual deterministic, sieve, collision, and
moderate-deviation inequalities for thresholds containing the new square-root baseline. Detailed
baton: `HANDOFF-2026-10-26-eb-multishift-lap10.md`.

## Lap checkpoint (2026-10-26, lap 11)

The variable cutoff and its first full asymptotic bundle are now proved. The new definitions are
`multiShiftScheduleU N = J(N) * (log log log N)^3` and
`multiShiftCutoffY N = floor (exp (log N / u(N)))`. The reusable variable-exponent floor lemma
`natFloor_exp_log_bounds` controls both logarithms after taking the natural floor.

`eventually_multiShiftCutoffY_bounds` proves `collisionCutoff N <= y(N) <= N` and the sharp bounds
`x/2 <= log y <= x`, `log x - log 2 <= log log y <= log x`, where `x = log N/u`.
`eventually_multiShiftLogBlock_bounds` then proves the prime block has logarithmic length between
`L - 6 log L - log 2` and `L + log 2`, and `eventually_multiShiftPrimeMean_bounds` inserts Mertens
to obtain `L/2 <= mu <= 2L`. Finally `eventually_multiShiftSieveGeometry` packages
`1 <= J <= collisionCutoff N`, `2 <= y <= N`, and `u <= log N/log y <= 2u`. All new declarations
are axiom-clean, and only the packet headline's original `sorry` remains.

The next attack is the constant-dependent analytic schedule: prove the remaining sieve depth
inequality, the two TV errors and `J^2/P` tend to zero, and define the active-column thresholds.
Then bundle the deterministic scalar inequality and the moderate-deviation hypotheses, keeping the
sharp `L - O(log L)` information from `eventually_multiShiftLogBlock_bounds` for the final exponent.
Detailed baton: `HANDOFF-2026-10-26-eb-multishift-lap11.md`.

## Lap checkpoint (2026-10-26, lap 12)

The constant-dependent sieve schedule and all transfer losses are now closed. The theorem
`eventually_multiShiftSieveDepth` proves the final depth hypothesis

```text
C J log(J+2) <= log N / log y(N),
```

using `J <= L` and `u = J (log L)^3`. The three limits
`tendsto_multiShiftSieveExpError`, `tendsto_multiShiftSievePowerError`, and
`tendsto_multiShiftCollisionError` prove respectively that the Rankin tail, the sieve remainder
`(log N)^J/sqrt N`, and the concrete coupling cost `2J(J-1)/P` vanish.
`tendsto_multiShiftTransferError` packages the exact combined loss used after applying `hM`.
All are axiom-clean.

The next attack is the active-column threshold. Fix moderate-deviation constants and define the
threshold as the ceiling of the prime mean plus the subpower square-root penalty, a fixed
`A sqrt(mean)` baseline, the `2j log_2 b` shift cost, and a `B log L` buffer. Prove uniformly on a
long initial interval of shifts both the explicit scalar premise of
`shiftedVarianceMass_gt_of_heavyColumn` and the hypotheses of
`multiShiftColumnMass_ge_moderate_of_baseline`. Then use the sharp
`eventually_multiShiftLogBlock_bounds` estimate—not merely `mean >= L/2`—to make the sum of column
lower bounds diverge. Detailed baton: `HANDOFF-2026-10-26-eb-multishift-lap12.md`.

## Lap checkpoint (2026-10-26, review lap 13)

The active threshold and its deterministic scalar calculation are now proved.
`multiShiftPrimeMean`, `multiShiftSubpowerPenalty`, and `multiShiftThreshold` define respectively
the scheduled reciprocal-prime mean, the exact square-root penalty from
`subpowerWeight c (2*N)`, and the ceiling threshold with an `A*sqrt(mean)` baseline, exact shift
cost, and `8*log L` buffer. `eventually_multiShiftPrimeMean_lower` retains the sharp
`L - 6 log L - O(1)` Mertens lower bound, while `tendsto_multiShiftBufferedMean` proves that after
subtracting the exact `log log (2N)` weight loss the buffer tends to infinity.

The uniform theorem `eventually_multiShiftThreshold_scalar` now proves, for every fixed
`b >= 2`, `T`, `c0 > 0`, `A >= 0`, and every shift index `j`,

```text
T*b^(2*(j+1))
  < 2^(multiShiftThreshold c A b N j - 1) * c0 * subpowerWeight c (2*N)
```

eventually in `N`. Thus the scalar premise of the deterministic prime-chain bridge is closed
without approximating the packet weight. The review also rechecked the `j : Fin J` indexing
against Step 1': column `j` is exactly the shift `j+1`, and all packet-verbatim statements still
match the planting commit.

The next attack is the probability schedule for this exact threshold. Choose `eps, eta, A`, prove
the moderate-deviation side conditions uniformly on an initial interval of length
`K(N) ~ sqrt(L/log L)`, and show the sum of the resulting column lower bounds diverges. Split the
penalty estimate at `c <= 0` versus `0 < c < 1`, but keep the same threshold and baseline theorem;
then apply `multiShiftMass_noHeavy_le_prod_one_sub` and the already-proved transfer-error limit.
Detailed baton: `HANDOFF-2026-10-26-eb-multishift-lap13.md`.

## Lap checkpoint (2026-10-26, lap 14)

The exact threshold is now connected all the way to the independent one-column probability bound.
`multiShiftDeviation` is the threshold displacement with a final `+1` absorbing `Nat.ceil`.
`eventually_multiShiftDeviation_smallTilt` proves uniformly for **every** scheduled column
`j : Fin (multiShiftScheduleJ N)` that

```text
(1 + 4*eta) * deviation_j / mean <= eta.
```

Thus the shorter active prefix proposed in lap 13 is unnecessary: the full `J ~ sqrt L` shift
schedule satisfies the moderate-deviation tilt condition.  The proof keeps the exact `2N`
subpower penalty and bounds its radicand using `c < 1`, the sharp mean is not weakened, and the
shift cost is controlled directly from `J = ceil(sqrt L)`.

`eventually_multiShiftModerateSideConditions` packages mean/displacement positivity,
reciprocal-square control, small tilt, and domination by the fixed `A*sqrt(mean)` baseline.
Finally `eventually_multiShiftColumnMass_ge_deviation` applies the existing finite
moderate-deviation theorem and transports its real-cardinality event through the ceiling to the
exact natural threshold event used by `multiShiftMass_noHeavy_le_prod_one_sub`.  All three results
are axiom-clean.

The next attack is the exponent and sum estimate.  Choose fixed `eps, eta, A` with
`c*(1+eps) < 1`; prove a uniform upper bound

```text
(1+eps) * deviation_j^2 / (2*mean)
  <= alpha * log L + o(log L),   alpha < 1/2,
```

or an equivalent explicit bound, then show the sum of the full `J` column lower bounds tends to
infinity.  This sends the product of lower-tail complements to zero.  Combine it with the already
proved collision/TV limit and the deterministic transfer, then apply Step 1'.  Detailed baton:
`HANDOFF-2026-10-26-eb-multishift-lap14.md`.
