# HANDOFF twopoint lap 17 — the ℓ² route priced exactly, and effectively refuted

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointGramDiag.lean`, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`.

## Advance on the crux

The fourth moment of lap 16 is now split exactly, for unimodular `a`:

* `kataiCount w N m = #{p ≤ w : 1 ≤ m ≤ ⌊N/p⌋}`; `dilationPairSum_diag` — the `m = m'` term of
  the fourth moment is `k(m)`.
* **`sum_kataiCount_sq`** — `Σ_{m ≤ N} k(m)² = Σ_{p,q ≤ w} min(⌊N/p⌋, ⌊N/q⌋)`.
* `norm_csGram_self_trunc`, `card_filter_Ioc` — `‖csGram p p‖ = ⌊N/p⌋`.
* **`kataiPairGramSq_split`** —

      kataiPairGramSq a w N
        = ( Σ_{p,q≤w} min(⌊N/p⌋,⌊N/q⌋) − Σ_{p≤w} ⌊N/p⌋² )
          + Σ_{m ≠ m' ≤ N} ‖Σ_{p≤w} a(pm) conj a(pm')‖² .

## Verdict on the `ℓ²` route

The bracket is **negative of order `−N²`**: the first term is `≍ N·Σ_{p,q}1/max(p,q)` (linear in
`N`), the second is `≍ N²·Σ_{p≤w}1/p²` (quadratic).  Since `kataiPairGramSq ≥ 0`, the off-diagonal
fourth moment `Σ_{m≠m'}‖Σ_p a(pm)conj a(pm')‖²` is itself of order `N²`, and the lap-15 demand
(`kataiPairGramSq ≤ ε²N²L(w)⁴/π(w)²`) asks it to cancel the bracket to **relative precision
`L(w)⁴/π(w)² → 0`**.

That is not a bound, it is an asymptotic evaluation of a fourth moment of dilates to a precision
that no known method supplies — MRT-type entropy decrement yields `o(1)` savings, not
`π(w)²/L(w)⁴`.  Combined with lap 13 (the `ℓ¹` route loses by an unbounded factor), **both
Cauchy–Schwarz-over-multipliers routes to the leaf are dead**.  The surviving possibility is a
method using the arithmetic of `ω(pm+1)` directly.

This is the run's main negative finding, and it is kernel-grounded rather than heuristic: every
identity above is exact, so the obstruction cannot be an artefact of lossy estimates.

## Next attack (lap 18)

The arithmetic route.  The one structural fact not yet exploited is that `a(n) = ζ^{ω_tail(b,n)}`
is a *multiplicative-in-`ω`* phase, so `a(pm)` and `a(m)` differ by `ζ^{ω(pm+1)−ω(m+1)}` — a
*bounded* digit-level quantity only when `p ∤ ·`.  The concrete next brick: formalise
`omegaTail (b, p*m)` in terms of `omegaNat (p*m+1)` and the one-digit peel already available
(`PairDecoupleOneDigit.lean`), and look for an exact algebraic relation between
`dilationPairSum` at `(m, m')` and at `(m', m)` or at scaled points — i.e. a symmetry of the
dilation family that forces cancellation.  If no such symmetry exists, the honest end state is:
leaf open, both standard routes refuted, recorded as such.

## Confidence
- `twoPointWeightedAvg_all` TRUE: 88%.
- `twoPointGramSum` leaf TRUE: 80%; provable with known techniques: **4%** (down from 8: both
  Cauchy–Schwarz routes are now refuted in kernel-grounded terms).
