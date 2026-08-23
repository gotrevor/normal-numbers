# HANDOFF — B5′ / W2 campaign: prove the 10 sorries in `src/NormalNumbers/CFDigitLaw.lean`

**Objective**: work package W2 of expedition B5′ — digit laws, the partition
calculus, the Gauss/Lebesgue comparison, and the Markov substitute for B–Y
Lemma 5.  All 10 `src/` sorries live in `CFDigitLaw.lean`; `src/` sorry-free
= done (the self-stop gate).  W1 (`CFCylinder.lean`) is complete and
axiom-clean — build on it freely.

**Read first**: `KHINCHIN.md` (the plan), the module docstrings of
`CFDefs.lean` / `CFCylinder.lean` / `CFDigitLaw.lean`, and
`papers/becher-yuhjtman-2019-abs-normal-cf-normal.md` §"Efficiency-free
substitute" (the mathematical route for the two `∃ C` statements).

**Statement discipline** 🎯: the 10 statement shapes and the `genWords` def
are FROZEN (guard-by-name; the 4 anchors are kernel-checked and must keep
passing).  Add as many private intermediate lemmas as you like — in
`CFDigitLaw.lean` or a new imported module — but do not weaken, reshape, or
re-hypothesize a frozen statement.  If one looks *wrong*, STOP on it, write
the evidence into this HANDOFF, and move to the others.  Oversight:
`JUDGE.md`.

**Suggested order** (algebra → measure → the two `∃ C` headliners):

1. `cfK_le_prod` — direct `cfK.induct`; warm-up (W1's technique note: revert
   hypotheses before the induction so the IHs carry them — not even needed
   here, no hypotheses).
2. `volume_digit_cylinder` — specialize `volume_cfCylinder` to `[k]`.
3. `cfCylinder_disjoint` — two same-length words that differ read
   incompatible digits at the first differing index; `List.ext_getD`-style
   argument.  No positivity needed.
4. `volume_append_mul_fib_le` — chain `volume_cylinder_append_le`,
   `volume_cfCylinder` (for `|I_u| ≤ 1/K(u)²`), `fib_le_cfK`.  ENNReal
   care: multiplicative form on purpose; avoid division.
5. `gaussMeasure_le_volume`, `volume_le_gaussMeasure` — `withDensity` +
   `setLIntegral` monotonicity against the density window
   `1/(2 log 2) ≤ 1/((1+x) log 2) ≤ 1/log 2` on `(0,1)`.
6. `gaussMeasure_univ` — `∫₀¹ dx/(1+x) = log 2`: mathlib's interval
   integral of `(1+x)⁻¹` (e.g. via `integral_inv` on `[1,2]` after a shift,
   or `intervalIntegral.integral_one_div`); then the `withDensity`/
   `lintegral` bookkeeping.
7. `volume_eq_tsum_extensions` — the meaty middle: extensions are subsets
   (prefix property), pairwise disjoint (3), and their union covers the
   irrationals of `cfCylinder w` (an irrational's Gauss orbit never hits 0,
   so every digit is genuine — W1's `irrational_gaussMap` + digit lemmas
   are `private` in `CFCylinder.lean`; re-prove locally or lift them into a
   shared module, both fine).  Rationals are countable → null.
   `measure_biUnion`/`tsum` over the countable type `↥(genWords n)`.
8. `tsum_mul_log_cfK_le` — the conditional expectation bound: `cfK_le_prod`
   turns `log K(u)` into `Σᵢ log(aᵢ+1)`; for each position `i`, the marginal
   mass of digit `k` is `≤ 2·|I_w|/(k(k+1))` (partition + distortion + digit
   law); `Σₖ log(k+1)/(k(k+1)) < ∞` (compare `log(k+1) ≤ √k`-style or
   `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` — any summable majorant).
   Take `C = 2·Σ + 1`.
9. `half_mass_long_extensions` — Markov on (8) with threshold `e^{Cn}`,
   `C = 2·C₈`: the bad extensions carry `≤ |I_w|/2`, so the good carry
   `≥ |I_w|/2`.  Handle `n = 0` separately (everything is good:
   `K([]) = 1 ≤ e⁰`).

**Warnings** ⚠️: digit-positivity (`∀ a ∈ w, 1 ≤ a`) stays load-bearing —
digit `0` is the junk marker (`CFDefs.lean` conventions).  Work up to
measure zero; don't chase set equalities the statements don't need.  `ℝ≥0∞`
gotchas: `ring` won't distribute `⁻¹` (use `div_mul_div_comm` /
`div_le_div_iff₀` at the ℝ layer and cross with `ENNReal.ofReal` lemmas);
this repo writes `(2 : ENNReal)`, no `open ENNReal` notation.

**Gates**: `lake build` green every commit; anchors keep passing; once all
10 are discharged, `#print axioms` each of the 10 = exactly
`propext`, `Classical.choice`, `Quot.sound`.
