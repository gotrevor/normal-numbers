# HANDOFF twopoint lap 20 — the deficit identity: separation ⇒ cancellation

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointDeficit.lean`, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`.

## Advance on the crux

Lap 19 reduced the leaf to a per-pair relative saving `L(w)²/(2π(w))`.  Any arithmetic argument
delivering such a saving must convert "the summand points in different directions on two sizeable
sets" into a number.  That conversion is now exact, in kernel:

* **`sum_unimodular_deficit`** — for `‖f‖ ≡ 1` on `S`,

      ‖Σ_{m∈S} f(m)‖² = |S|² − ½ Σ_{m,m'∈S} ‖f(m) − f(m')‖² .

  The triangle inequality is the all-values-equal case; every disagreeing pair of indices
  subtracts exactly `‖f(m) − f(m')‖²`.
* `norm_sum_le_of_separated` — disjoint `A, B ⊆ S` with `‖f(m) − f(m')‖ ≥ d` across them give
  `‖Σ_S f‖² ≤ |S|² − |A||B|d²`.
* **`twoPointTruncSum_saving`** — the lap-19 target in usable form: two blocks of relative size
  `α` inside `m ≤ min(⌊N/p⌋,⌊N/q⌋)`, with phase separation `d`, give

      ‖T_{p,q}(N)‖ ≤ (1 − α²d²/2) · min(⌊N/p⌋,⌊N/q⌋) .

## What the leaf now needs, end to end

Chaining laps 11, 12, 19, 20: `ConjC1` follows from Delange plus —

> for every `ε > 0` there is `w(N) → ∞` with `w(N)² ≤ N` such that for all primes `p ≠ q ≤ w(N)`
> the truncated range splits into two blocks of relative size `α` and phase separation `d` with
> `α²d²/2 ≥ 1 − ε·L(w)²/(2π(w))·max(p,q)/…`

— more usefully, since `α²d² ≍ L(w)²/π(w)` suffices, **both the block density and the separation
may degrade slowly as `w` grows**.  That is a far weaker demand than equidistribution of
`ω(pm+1) − ω(qm+1)`, and it is finite-dimensional per pair: exhibit two positive-density residue
or factorisation classes of `m` on which `ζ^{ω(pm+1)} conj ζ^{ω(qm+1)} W_{p,q}(m)` points in
separated directions.

## Next attack (lap 21)

Find such a split for a concrete pair.  The natural candidate: classes of `m` determined by the
factorisation of `pm+1` at one small auxiliary prime `r`.  On `m ≡ r̄(−1)·p⁻¹ (mod r)` the dilate
`pm+1` is divisible by `r`, adding `1` to `ω` (when `r² ∤ pm+1`) and rotating the summand by
exactly `ζ`.  If the corresponding class for `qm+1` can be kept disjoint (CRT on `r`, `r'`), the
two blocks have density `≍ 1/r` each and separation `d = ‖1 − ζ‖ > 0` — giving `α²d² ≍ 1/r²`,
which beats `L(w)²/π(w)` as soon as `r` is bounded and `w` is large.  The obstruction to watch:
the weight `W_{p,q}` also moves with `m`, so the separation must be shown for the *product*, not
just the `ζ^{ω}` factor.  Formalising the `r`-divisibility class and its effect on `ω` is the
next Lean brick (`omegaNat_succ_of_dvd`-style), and the repo's `PairDecoupleOneDigit` already has
the weight's definition to work against.

## Confidence
- `twoPointWeightedAvg_all` TRUE: 88%.
- `twoPointGramSum` leaf TRUE: 80%; provable with known techniques: 7% (up from 5: the deficit
  route turns the target into a positive-density-class question, which is at least attackable).
