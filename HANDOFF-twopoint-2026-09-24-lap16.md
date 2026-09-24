# HANDOFF twopoint lap 16 — the fourth-moment identity

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointGramFrobenius.lean`, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`.

## Advance on the crux

The `ℓ²` route (lap 15) needs the Gram matrix's Frobenius mass in a form an analytic input can
attack.  That conversion is now in kernel:

* `sum4_comm` — the four-fold interchange.
* **`gram_frobenius`** —
  `Σ_{p,q ∈ A} ‖Σ_m C_p(m) conj C_q(m)‖² = Σ_{m,m'} ‖Σ_{p ∈ A} C_p(m) conj C_p(m')‖²`.
  Reading the same matrix by rows (pairs of *multipliers*) and by columns (pairs of *points*).
* `dilationPairSum` — the superposition `Σ_{p ≤ w} a(pm) conj a(pm')`, the object on the right.
* **`kataiPairGramSq_eq`** — `kataiPairGramSq = (fourth moment) − Σ_p ‖csGram p p‖²`, i.e. the
  off-diagonal `ℓ²` mass is the fourth moment minus its explicit diagonal
  `Σ_p (Σ_m ‖C_p(m)‖²)² = Σ_{p≤w} ⌊N/p⌋²`.

## Why this is the right object

It converts the leaf's remaining content into a statement about **dilation orbits of point
pairs**: for how many `(m,m')` does `Σ_{p ≤ w} a(pm) conj a(pm')` fail to exhibit cancellation?
That is precisely the shape an MRT/entropy-decrement or large-sieve-in-the-multiplier argument
produces (MRT bound shifts; here the family is dilations, and the identity above is what lets a
dilation-family bound be fed back into the pair sum).

It also exposes the route's real difficulty numerically: the diagonal `Σ_{p≤w} ⌊N/p⌋² ≈ N²Σ1/p²`
is of order `N²`, while the `ℓ²` demand of lap 15 is `ε²N²L(w)⁴/π(w)²`, i.e. `o(N²)` by an
unbounded factor.  So the fourth moment must be computed to *better than* its own diagonal —
the diagonal has to cancel exactly against `Σ_p ⌊N/p⌋²`, which `kataiPairGramSq_eq` now does
exactly rather than by estimate.  Any future bound must therefore control
`Σ_{m ≠ m'} ‖Σ_p a(pm) conj a(pm')‖²` plus the `m = m'` terms' deviation from `Σ_p ⌊N/p⌋²`.

## Next attack (lap 17)

Split the fourth moment at `m = m'`:
`Σ_{m,m'} = Σ_m ‖Σ_p ‖C_p(m)‖²‖² + Σ_{m≠m'} ‖·‖²`, and prove
`Σ_m (Σ_p ‖C_p(m)‖²)² = Σ_m k(m)²` with `k(m) = #{p ≤ w : pm ≤ N}` (for unimodular `a`).
Then `kataiPairGramSq = Σ_m k(m)² − Σ_p ⌊N/p⌋² + Σ_{m≠m'} ‖·‖²`, and since
`Σ_m k(m)² ≈ N·(counting)` while `Σ_p ⌊N/p⌋² ≈ N²Σ1/p²`, the first difference is **negative and
of order `−N²`** — which forces `Σ_{m≠m'} ‖·‖²` to be of order `N²` too, with the demand being
that the two nearly cancel.  Making that precise in kernel would either refute the `ℓ²` route
outright (if the cancellation is provably insufficient) or isolate exactly the off-diagonal
fourth moment that must be bounded.  This is the decisive computation and is now purely
combinatorial — no analytic number theory needed to state it.

## Confidence
- `twoPointWeightedAvg_all` TRUE: 88%.
- `twoPointGramSum` leaf TRUE: 80%; provable with known techniques: 8%.
- The `ℓ²` route reaches the leaf: 15% (down from 20: the demand is now known to sit below the
  fourth moment's own diagonal, which is a delicate-cancellation regime).
