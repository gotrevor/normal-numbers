# HANDOFF twopoint lap 15 — the ℓ² route, set up and priced

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointGramL2.lean`, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`.

## Advance on the crux

Lap 14 identified the leaf as a dilation-average (MRT-shaped) problem.  The only standard handle
is Cauchy–Schwarz in the pair index; this lap builds it and prices it, before any investment in
the fourth-moment machinery.

* `kataiPairGramSq` — the `ℓ²` mass `Σ_{p≠q≤w} ‖G_{pq}‖²` of the off-diagonal Gram matrix.
* **`kataiPairGram_sq_le`** — `(Σ_{p≠q}‖G_{pq}‖)² ≤ π(w)²·Σ_{p≠q}‖G_{pq}‖²` (mathlib's
  `sq_sum_le_card_mul_sum_sq` on the product index set; the diagonal contributes `0`).
* **`kataiPairGram_le_of_l2`** — hence the leaf's `ℓ¹` target follows from
  `Σ_{p≠q}‖G_{pq}‖² ≤ ε²·N²·L(w)⁴/π(w)²`.
* **`tendsto_l2_budget_ratio`** — the price: `L(w)⁴/π(w)² → 0` (from the kernel fact
  `tendsto_card_div_kataiPrimeRecip_sq`).

## Reading

The `ℓ²` demand is `Σ_{p≠q}‖G_{pq}‖² = o(N²)` by an unbounded factor `π(w)²/L(w)⁴`.  The trivial
`ℓ²` bound is `N²·Σ_{p≠q} 1/max(p,q)²`, and unlike `M(w) = Σ 1/max(p,q)` (lap 13, divergent),
`Σ_{p≠q} 1/max(p,q)² ≤ 2 Σ_p π(p)/p²` is a **convergent**-looking sum.  So the `ℓ²` route does
not die of the same disease as the `ℓ¹` one: there the trivial mass beat the budget by an
unbounded factor with no room; here the gap is between a bounded constant and `L(w)⁴/π(w)²`,
which is a power-saving demand of a familiar kind.

Under the square-root-cancellation heuristic `‖G_{pq}‖ ≈ √(N/max(p,q))` the `ℓ²` mass is
`≈ N·M(w)`, which is `≫ N²L⁴/π²` exactly when `M(w)·π(w)² ≫ N L⁴` — and since `N ≥ w²` while
`M(w)π(w)² ≈ w³/log⁴w`, the comparison is `w³ vs w²·polylog`, so the heuristic says the route
FAILS by a factor `≈ w`.  That is the decisive computation for lap 16 to make rigorous or refute.

## Next attack (lap 16)

1. Prove `Σ_{p≠q≤w} 1/max(p,q)² ≤ 2 Σ_{p≤w} π(p)/p²` and bound that by an absolute constant
   (Chebyshev-free: `π(p) ≤ p`, giving `Σ 1/p` — divergent; so a real prime bound is needed.  If
   mathlib's `Nat.primeCounting` bounds are unavailable, state the trivial-`ℓ²` bound as
   `N²·Σ_{p≠q}1/max²` without evaluating it and compare directly.)
2. Then decide the comparison `trivial ℓ² mass` vs `ε²N²L⁴/π(w)²` in kernel.  If the trivial mass
   exceeds the demand by an unbounded factor even at `N = w²`, the `ℓ²` route is refuted for the
   same structural reason as the `ℓ¹` one and the honest verdict is that no Cauchy–Schwarz-based
   route reaches this leaf — a strong, publishable negative result about the C1 route.

## Confidence
- `twoPointWeightedAvg_all` TRUE: 88%.
- `twoPointGramSum` leaf TRUE: 80%; provable with known techniques: 8%.
- The `ℓ²` (Cauchy–Schwarz-in-pair-index) route reaches the leaf: 20% — the heuristic above says
  it loses by `≈ w`, but the computation is not yet in kernel.
