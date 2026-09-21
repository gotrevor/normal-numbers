# HANDOFF — the lower Brun sieve core is PROVED (all three target properties)

Branch `proof/prime-model-complement`.  `lake build` GREEN (9109 jobs).
`src/NormalNumbers/PrimeModelBrunLower.lean`: **no `sorry`, no `axiom`**;
`#print axioms` on every headline is `[propext, Classical.choice, Quot.sound]`.

`KICKOFF-brun-lower-core.md` asked for coefficient/support, pointwise minorant and
relative error **together**, with no hypothesis equivalent to the conclusion.  All
three are proved and packaged as `brun_lower_fundamental`.

## The construction

Over an arbitrary finite set `U` of distinct naturals (primality is never used), with
cutoffs `Y : ℕ → ℕ`.  Instead of decreasing prime *lists*, admissibility is stated via
the rank from the top, `ab E q = #{p ∈ E | q < p}`:

    Adm Y E  ↔  ∀ q ∈ E, Odd (ab E q) → q ≤ Y ((ab E q + 1) / 2)
    lam Y E  =  if Adm Y E then (-1)^#E else 0

`q` sits at an even position iff `ab E q` is odd, and the position is `(ab E q + 1)/2`.
This is local, decidable, and — the load-bearing property — depends only on the part of
`E` weakly **above** each element, which is what lets a first-failure prefix be cut off.

## Property (2): the pointwise minorant  (`sum_lam_le_indicator`)

`∀ B ⊆ U, ∑_{E ⊆ B} lam Y E ≤ (if B = ∅ then 1 else 0)`, with **no hypothesis on `Y`**.

Engine: `sum_not_adm_eq`, the **first-failure decomposition**, exact and weight-generic:

    ∑_{E ⊆ B, ¬Adm} (-1)^#E ∏_E f
      = ∑_{F ⊆ B, FirstFail F} (∏_F f) · ∏_{p ∈ B, p < min F} (1 - f p)

proved by `Finset.sum_fiberwise_of_maps_to` along `ff E` (the part of `E` above the
largest failing element), each fibre reindexed by `S ↦ F ∪ S` (`sum_nbij'`) onto the
powerset of the elements below `F`; the inner sum telescopes by `Finset.prod_sub`.
`FirstFail.even_card` supplies the `(-1)^#F = 1` that kills the prefix sign.
Specialising at `f = 1` gives (2); specialising at `f = g` gives `defect_eq`, the exact
nonnegative model defect, which is the entry point for (3).  One engine, both uses.

## Property (1): coefficients and support  (`brun_lower_one`)

`|lam| ≤ 1`, and `lam E ≠ 0 → ∏ E ≤ y^s`, for `1 ≤ k`, `s ≥ 80k`, elements `≤ y`.

* `ab E : E → range #E` is a bijection (strictly antitone), so a pointwise bound
  `q ≤ W (ab E q)` reindexes to `∏_{q∈E} q ≤ ∏_{i<#E} W i` (`prod_comp_ab`).
* `exists_ab_pred`: the element directly above `q` drops `ab` by exactly one.  With
  `(2j+1)/2 = (2j-1+1)/2 = j` this propagates each even-position cutoff to its odd
  neighbour, so EVERY element of rank ≥ 2 is at most the cutoff of its pair.
* Cutoffs `brunCut`: `Y j = y` for `j ≤ J = ⌊s/4⌋`, `Y j = ⌊y^(α^(j-J))⌋` after,
  `α = 1 - 1/(20k)`.  `sum_expoI_odd` pairs ranks `2j-1, 2j`; `sum_expo_le` charges
  `J` full cutoffs plus the geometric tail `α/(1-α) = 20k-1`; total exponent
  `1 + 2J + (40k - 2) = 2J + 40k - 1 ≤ s`.

## Property (3): the relative error  (`brun_lower_three`)

`(1 - 2 e^{-s/2}) · V ≤ ∑_{E ⊆ U} lam E ∏_E g`, from the elementary hypotheses plus

    Dimension U g y K k :  ∀ 1 ≤ t ≤ y, ∏_{p ∈ U, p > t} (1 - g p)⁻¹
                             ≤ K · (log y / log (max 2 t))^k

and `s ≥ 40 log K + 4`.  Chain:

* `firstFail_struct` — a first failed prefix has `#F = 2m` with `m > J`, and all of `F`
  lies above `t_ℓ = y^(α^ℓ)`, `ℓ = m - J ≥ 1`.  A prefix of length `≤ 2J` CANNOT fail:
  its cutoff is `y` and every element is `≤ y`.  (`q0 > ⌊t⌋` gives `q0 > t` exactly, so
  the floor in the cutoff costs nothing.)
* `esymm_le_exp_div` / `esymm_le_pow` — **the assessment's factorial/Stirling step is
  unnecessary**: for every `x > 0`,
  `xⁿ e_n(W) ≤ ∑_{E⊆W} x^{#E} ∏_E g = ∏_{p∈W}(1 + x g p) ≤ exp(x ∑_W g)`
  (`Finset.prod_add` and `1+u ≤ eᵘ`), and `x = n/T` gives `e_n(W) ≤ (e T/n)ⁿ`
  whenever `∑_W g ≤ T`.  No factorials appear anywhere in the file.
* `dim_prod_le` / `dim_sum_le` — `∏_{p>t_ℓ}(1-g)⁻¹ ≤ exp(A+Bℓ)` and `∑_{p>t_ℓ} g ≤ A+Bℓ`,
  `A = log K`, `B = -k log α`.  The `max 2 t` branch is exactly where a cutoff below 2 is
  absorbed: there `log 2 > log t_ℓ = α^ℓ log y`, so the ratio bound holds more easily.
* `Bconst_le` — `B ≤ k/(20k-1) ≤ 1/19` (from `log x ≤ x-1` at `x = α⁻¹`), and
  `A ≤ J/10` from `s ≥ 40A+4`; hence `T = A+Bℓ ≤ (J+ℓ)/10 = n/20`.
* `block_le` — per block `n = 2m`: `V · exp T · (e T/n)ⁿ ≤ V · 4^{-n}`, using
  `e^{21/20}/20 ≤ 1/4` (`exp_const_le`, proved from `1+u ≤ eᵘ` alone — no numeric
  bound on `e` is imported).
* `geom_tail_le` + `exp_two_le` (`e² ≤ 16`) — `∑_{n ≥ 2J+2} 4^{-n} ≤ 16^{-J}/12
  ≤ e^{2-s/2}/12 ≤ (4/3) e^{-s/2} ≤ 2 e^{-s/2}`.

## Anchors (kernel `decide`, no `native_decide`)

`U = {2,3,5,7}`, cutoffs `3, 2`: supported max `42` (`anchor_support`, sharp at
`{2,3,7}`), `V = 8/35`, model sum `23/105` — defect `1/105`, relative defect `1/24`.
GOTCHA recorded: `Rat` division does not reduce in the kernel, so the model-sum anchor
runs through an integer avatar `lamZ` plus the denominator-clearing `sum_inv_prod_eq`.

## What is NOT done

The sieve *core* is done; the assessment's remaining assembly is untouched and still
open: the radical-state predicate equivalence, retained-state cardinality, summing the
sieve remainders against `radical_sieve_count`, the interval→dimension estimate (i.e.
DISCHARGING `Dimension` for the intended `g`), phase decay, constant bookkeeping.
`Dimension` is a hypothesis here because the assessment lists it as a separate,
not-yet-formalised input — it is not a restatement of any of (1), (2), (3).
