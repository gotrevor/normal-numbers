# HANDOFF twopoint lap 21 — rotation pairing: the tool an arithmetic argument can actually feed

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointPairing.lean`, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`.

## Correction to lap 20's "next attack"

Lap 20 proposed finding two blocks `A, B` with `‖f(m) − f(m')‖ ≥ d` for **all** cross pairs.  That
is not deliverable by arithmetic: for unrelated `m, m'` the values `ω(pm+1)`, `ω(pm'+1)` are
unrelated, so no such uniform separation exists.  `norm_sum_le_of_separated` stays true and
useful, but it is the wrong interface.

## Advance on the crux

The right interface is a **pairing**, which is exactly what an arithmetic construction produces:

* **`norm_sum_le_of_rotation`** — if `σ` injects a set `A ⊆ S` into `S \ A` with
  `f(σ m) = z·f(m)` for a fixed `z`, then

      ‖Σ_{m∈S} f(m)‖  ≤  (|S| − 2|A|)  +  ‖1 + z‖·|A| ,

  a saving of `(2 − ‖1+z‖)·|A|`, positive for every unit `z ≠ 1`.
* `norm_sum_le_of_rotation'` — with `|A| ≥ α|S|`: `‖Σ_S f‖ ≤ (1 − (2−‖1+z‖)α)·|S|`.
* **`twoPointTruncSum_pairing`** — the same for the leaf's per-pair sum.

Chaining laps 11, 12, 19, 21, `ConjC1` follows from Delange plus:

> for each `ε > 0` there is `w(N) → ∞`, `w(N)² ≤ N`, such that for all primes `p ≠ q ≤ w(N)`
> the range `m ≤ min(⌊N/p⌋,⌊N/q⌋)` carries an injection `σ` on a subset of relative density `α`
> into its complement with
> `ζ^{ω(pσ(m)+1)} conj ζ^{ω(qσ(m)+1)} W_{p,q}(σ m) = z·ζ^{ω(pm+1)} conj ζ^{ω(qm+1)} W_{p,q}(m)`
> for a fixed `z ≠ 1`, and `(2 − ‖1+z‖)·α ≳ L(w)²/π(w)`.

## Why this is now a *constructive* target

`σ` only has to move `m` in a way that changes the `ζ`-exponent by a fixed amount.  The natural
construction: pick an auxiliary prime `r` and let `σ` map `m` to an `m'` in the same residue class
mod `q`-side data with `pm'+1 = r·(pm+1)`-type relations — i.e. multiplicative rather than
additive moves.  The exact relation to aim for is `ω(pσ(m)+1) = ω(pm+1) + 1` with the `q`-side and
the weight unchanged, giving `z = ζ`, `‖1+ζ‖ = 2|cos(πt/b)| < 2`.

## Next attack (lap 22)

Build the arithmetic of `σ`.  Concretely, formalise: for `r` a prime with `r ∤ p`, the map
`m ↦ (r·(pm+1) − 1)/p` is well defined on `m ≡ m₀ (mod r')`-type classes (it needs
`p ∣ r(pm+1) − 1`, i.e. `r ≡ 1 (mod p)` up to units), is injective, and satisfies
`ω(pσ(m)+1) = ω(pm+1) + 1` when `r ∤ (pm+1)`.  The `q`-side is then the obstruction: `qσ(m)+1`
is *not* controlled, so the honest next step is to check whether the construction can be done
with the `q`-side frozen — if not, that is a genuine structural obstruction to the pairing route
and should be recorded as such.

## Confidence
- `twoPointWeightedAvg_all` TRUE: 88%.
- `twoPointGramSum` leaf TRUE: 80%; provable with known techniques: 7%.
- The pairing route yields the per-pair saving: 25% — it is the first route whose hypothesis is a
  *construction* rather than an equidistribution statement, but the `q`-side freeze is unproven.
