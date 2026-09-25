# HANDOFF c3-mrt 2026-09-25 — lap 36: the `K`-fold bridge expansion

**Branch** `wip/c3-mrt`.  Both green: `lake build` (9257 jobs) and
`lake build NormalNumbers.C3MrtMultiShift` (new chain tip: imports `C3MrtProductPhase` →
`C3MrtKPoint` → `C3MrtArchimedean`, so it covers the whole `C3Mrt*` chain).
Prior batons: `-lap35.md` (the Tao–Teräväinen discovery), `-lap34.md`, `-lap33.md`.

## Advance

The first genuinely `K`-dimensional step of the assembly is proved.  New module
`src/NormalNumbers/C3MrtMultiShift.lean`, all sorry-free, trust-triple:

| name | content |
|---|---|
| `sum_piFinset_snoc` | split a tuple sum over `Fin (K+1)` as `∑_{last} ∑_{rest}`, via `Fin.snoc` and `Finset.sum_nbij'` (mathlib has no succ-split for `Fintype.piFinset`) |
| `prod_pow_cardFactors` | `∏_i z_i^{Ω(m)} = (∏_i z_i)^{Ω(m)}` — the algebraic fact behind `ProductLogElliott`'s product hypothesis |
| **`sum_pow_omega_multi_eq`** | the `K`-fold bridge expansion |

    ∑_{n ∈ S} F(n) ∏_{i<K} z_i^{ω(n+i+1)}
      = ∑_{(d_i) ∈ (range (B+1))^K} (∏_i sqfW z_i (d_i))
          ∑_{n ∈ S, ∀i  d_i ∣ n+i+1}  F(n) ∏_i z_i^{Ω((n+i+1)/d_i)}

Proved by induction on `K`, peeling the **last** shift.  Two things made it go through:

1. `sum_pow_omega_offset_eq` was already stated for an *arbitrary* index set `S` and offset `c`
   (lap 2 wrote it that way on purpose), so the `i`-th peel runs inside the congruences the
   previous peels imposed.
2. **`F` must be quantified inside the induction**: each peel absorbs one `z_K^{Ω((n+K+1)/d_K)}`
   factor into the weight, so the induction hypothesis has to hold for every weight, not for the
   fixed `F` of the statement.  (The first attempt quantified `F` outside and failed exactly
   there — recorded so it is not retried.)

The inner sum is now a `K`-point correlation of the **completely multiplicative** `z_i^Ω` along
`K` linear forms in the progression variable: the shape `ProductLogElliott K` is stated for.

## Where this sits

Assembly chain for the depth-`K` rung, mirroring laps 23–33 at `K = 2`:

| step | `K = 2` | general `K` |
|---|---|---|
| bridge expansion | `sum_pow_omega_two_shift_eq_coprime` | **`sum_pow_omega_multi_eq` (lap 36)** |
| truncate moduli at `Y` | `two_shift_truncation_bound` | TODO |
| CRT to an initial segment | `inner_sum_linear_forms` + `filter_linear_lt_eq_range` | TODO |
| per-tuple rung bound | `progression_sum_bound` / `inner_pair_bound` | TODO |
| tuple mass is finite | `pair_mass_le` | TODO (`∏_i sqfWMass z_i`, by `Finset.sum_prod_piFinset`) |
| ε-chase | `rung_two_correlation` | TODO |

## NEXT

1. **`tuple_mass_le`**: `∑_{(d_i) ≤ Y} ∏_i ‖sqfW z_i (d_i)‖/d_i ≤ ∏_i sqfWMass z_i`.
   `Finset.sum_prod_piFinset` (mathlib, `Algebra/BigOperators/Ring/Finset.lean:161`) turns the
   tuple sum into a product of one-dimensional sums, then `sum_norm_sqfW_div_le_mass` per factor.
   This is the `K`-fold `pair_mass_le` and it is the step that makes the tuple sum absolutely
   convergent — no new mathematics, and it is what licenses truncating each `d_i` at `Y`.
2. `multi_truncation_bound`: iterate `offset_truncation_bound_of_mass` `K` times; the error
   telescopes to `≤ ∑_{i<K} (∏_{j<i} sqfWMass z_j) · (1 + log(N+K)) · bridgeTail z_i Y`.
3. Pairwise coprimality of `K` powerful moduli is NOT automatic for `K ≥ 3` (consecutive
   integers `n+1, n+2, n+3`: `d_0` and `d_2` can share the factor `2`).  **This is the one real
   new obstruction the `K ≥ 3` assembly faces** — at `K = 2` consecutive integers are coprime and
   `joint_progression_eq_empty_of_not_coprime` disposed of the rest.  Attack: the joint
   progression `∀i d_i ∣ n+i+1` is still a single class mod `lcm(d_i)` when it is nonempty, and
   CRT applies to the lcm; the `1/(d_0⋯d_{K-1})` gain degrades to `1/lcm`, which is exactly where
   the `∏ sqfWMass` bound has to be re-derived.  Decide this before doing steps 4–6.

## Still refuted — DO NOT RETRY

Unchanged, plus: quantifying `F` outside the `K`-induction of `sum_pow_omega_multi_eq`.

## Confidence

* `K`-fold expansion: **proved**.
* `K ≥ 3` assembly completable: ≈ 55% (down from 70% at lap 35 — the non-coprimality of the
  `K` moduli is a real new obstruction, not bookkeeping; it was invisible at `K = 2`).
* leaf TRUE ≈ 97%; leaf PROVABLE with known techniques ≈ 25% (unchanged).
