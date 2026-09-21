# Handoff: quantitative lower arithmetic sieve count — both targets proved

**Date**: 2026-09-21 · **Branch**: `wip/g5-prime-subset` · Scope: `KICKOFF-brun-arithmetic-count.md`

## Result

`src/NormalNumbers/PrimeModelBrunCount.lean` (new, 0 `sorry`, imported from `src/NormalNumbers.lean`).
No existing module edited; no new analytic hypothesis.

### `brun_remainder_le_square`
For `U` a finite set of primes `p > h`, weights `lam` with `|lam E| ≤ 1` on `E ⊆ U` and
`lam E ≠ 0 → (∏_{p∈E} p : ℝ) ≤ R`, and `1 ≤ R`:

    ∑_{E ⊆ U} |lam E| · h^#E ≤ R^2.

Route as specified: `h^#E ≤ ∏_{p∈E} p` termwise (each `h < p`); `E ↦ ∏_{p∈E} p` injective on
`U.powerset` (`prod_injOn_powerset`, via `p ∣ ∏ E ↔ p ∈ E` for primes) into `Icc 1 ⌊R⌋₊`, so at
most `⌊R⌋₊ ≤ R` summands are nonzero, each `≤ R`.  Empty `E` included (product 1).

### `brun_sifted_count_lower`
Hypotheses exactly: `1 ≤ h`; `exp 2 ≤ (y:ℝ)`; `1920 * (h:ℝ) ≤ s`;
`40 * log (4^h * exp (16h)) + 4 ≤ s`; `A U : Finset ℕ`, `Q r X : ℕ`, `j : ℕ → Fin h`;
`∀ p ∈ A, p.Prime ∧ h < p`; `∀ p ∈ U, p.Prime ∧ h < p ∧ p ≤ y`; `Disjoint A U`; `0 < Q`;
`r < Q`; `∀ p ∈ A ∪ U, Nat.Coprime Q p`.  Conclusion:

    (1 - 2 exp (-s/2)) · X/(Q·∏_{p∈A} p) · ∏_{p∈U} (1 - h/p) - ((y:ℝ)^s)^2
      ≤ #{n < X : Radical.SiftedCond h A U Q r j n}.

`X = 0` allowed; no positivity of `1 - 2exp(-s/2)` used.  No `Dimension`, sieve-weight,
counting-error or root-cardinality hypothesis remains.

## Proof structure (for reuse)

* `hitU h U n` + `sieveCond_iff_sub` / `siftedCond_iff_hit_empty` — local re-proofs of the
  private `hitSet` lemmas of `PrimeModelRadicalCRT` (that module untouched).
* `weighted_counts_le_sifted` — the Brun minorant summed: interchange `∑_n ∑_{E⊆U}`, collapse
  `U.powerset.filter (· ⊆ hitU)` to `(hitU).powerset`, apply
  `∑_{E ⊆ B} lam E ≤ [B = ∅]`.  Base-condition failure kills every term.
* `main_term_factor` — `X·h^#E/(Q·D·∏E) = X/(Q·D) · ∏_{p∈E}(h/p)` (no nonvanishing needed).
* Assembly: per `E`, `radical_sieve_count` gives `|c_E - m_E| ≤ h^#E`, so
  `lam E · c_E ≥ lam E · m_E - |lam E| h^#E`; sum, use `prime_density_brun_lower` property (3)
  for the main term (scaled by the nonnegative `X/(Q D)`) and `brun_remainder_le_square` with
  `R = (y:ℝ)^s` (`1 ≤ R` from `y ≥ exp 2 ≥ 1`, `s ≥ 0`) for the error.

## Verification

`lake build` → `Build completed successfully (9115 jobs)`.  `#print axioms` on both targets →
`[propext, Classical.choice, Quot.sound]` (the `#print axioms` lines are in the file).

## Gotchas hit

* `Set.InjOn`/`Set.MapsTo` goals over `(S : Set (Finset ℕ))`: `simp [Finset.coe_filter]` fails
  ("no progress" / deprecated `Set.mem_setOf_eq`).  Use `have h' : E ∈ S := hE` then
  `rw [Finset.mem_filter]`.
* `▸` refuses an `hEF : (fun E => ∏ p ∈ E, p) E = ...`; restate it as a `have` at the
  beta-reduced type first.

## Next (out of scope here)

Encoding/cardinality of the selected primes, phase decay, and parameter assembly remain before
the final selected-prime theorem.  This result is the counting input only.
