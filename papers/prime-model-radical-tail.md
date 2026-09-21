# The retained-box tail and phase transfer (radical model)

Formalized in `src/NormalNumbers/PrimeModelRadicalTail.lean`, namespace
`NormalNumbers.PrimeModel.Radical`.  No `sorry`, no `axiom`; every headline result
is `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).

## Setting

The finite radical model (`PrimeModelRadical.lean`) puts the product law
`weight k (primeRecip p)` on `ι → Option (Fin k)`, `ι` a finite index of primes
`p i > k`, `k ≥ 1`.  The **radical size** at shift `j` is

  `radSize p j s = ∏_i (if s i = some j then (p i : ℝ) else 1)`,

i.e. `d_j(s)`, the product of the primes assigned to shift `j`.  The **retained
box** is `retainedBox k p T = {s : ∀ j, d_j(s) ≤ T}`.

## Results

1. `radSize_rpow` — the real-power-of-a-product identity
   `d_j(s)^α = ∏_i (if s i = some j then (p i)^α else 1)`.  *Proved*, not assumed;
   it is what turns the moment into the single-site multiplier shape.
2. `radical_radSize_moment_le_exp` — with `α ≥ 0` and the moment budget
   `∑_i ((p i)^α - 1)/(p i) ≤ A`, `E[d_j^α] ≤ exp A`.  (Uses
   `radical_site_moment_le_exp` at `t i = (p i)^α`.)
3. `radical_shift_markov` — Markov at a fixed shift: the mass of `{d_j > T}` is
   `≤ exp A / T^α`.
4. `sum_compl_retainedBox_le` — the reusable finite union bound over the `k`
   shifts for any nonnegative family.
5. **`radical_box_tail`** — for `T ≥ 1`, `α > 0` and the budget `A`,

       ∑_{s ∉ B(T)} weight k (primeRecip p) s ≤ k · exp A / T^α.

6. **`radical_box_phase_transfer`** — for any nonnegative normalized law `ν` on
   the same finite state space, any `f` with `‖f s‖ ≤ 1`, and retained `L¹`
   discrepancy `∑_{s ∈ B(T)} |ν s - weight s| ≤ δ`,

       ‖E_ν f - E_model f‖ ≤ 2·(k · exp A / T^α) + 2δ,

   obtained by composing (5) with `PrimeModel.probability_complement_phase`
   (that inequality is *reused*, not reproved).

## Numeric anchors (independent of the general theorems)

`k = 2`, two sites carrying the primes `3, 5`.  The nine states, expanded by hand
through `Fin.consEquiv`, have masses `1/5` (`(none,none)`, `(some j, none)`) and
`1/15` (the remaining six), and `d_j ∈ {1,3,5,15}`.  In-file `example`s check

| `T` | tail mass |
|---|---|
| 1 | `4/5` |
| 2 | `4/5` |
| 3 | `2/5` |
| 5 | `2/15` |
| 15 | `0` |

For `T = 5` only the two states assigning **both** primes to the **same** shift
have `d_j = 15 > 5`, each of mass `1/15`.

## Remaining obligations (explicitly NOT discharged here)

* **The arithmetic budget.**  `A` is a hypothesis.  The intended instance
  `A ≤ 20` (or `4√e`) needs `p^α - 1 ≤ √e · α log p` for `α log p ≤ 1/2`
  (`Real.add_one_le_exp` + convexity on `[0, 1/2]`) and Mertens
  `∑_{p ≤ y} log p / p ≤ 2 log y`, at `α = 1/(2 log y)`, `y ≥ e²`.  See
  `papers/prime-model-radical.md`.
* **The retained `L¹` discrepancy `δ`.**  A hypothesis of the transfer; supplying
  it for the actual arithmetic law is the sieve input (two-sided fundamental
  lemma), a separate campaign — see item 3 of `HANDOFF-radical.md`.
* Neither is hidden in an axiom.
