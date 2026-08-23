# HANDOFF — W2 campaign COMPLETE; next: stage W3

**Date**: 2026-08-23 · **Branch**: `master` · W2 done in one session, 3 laps.

## State
- `src/` sorry-free.  All 10 W2 statements in `CFDigitLaw.lean` proved,
  axiom-clean (`propext`/`Classical.choice`/`Quot.sound`, observed via
  `#print axioms`), anchors passing, no frozen statement reshaped.
- W1 (`CFCylinder.lean`, 12/12) and Stoneham unchanged.  Two W1 lemmas
  lifted `private` → public: `one_le_cfK`, `irrational_gaussMap`.
- Commits: `0f512a4` (7 warm-ups) → `9933e57` (partition crux) →
  `fdc51a6` (log-continuant bound) → this one (Markov substitute, records).
  Not pushed (host pushes).

## Technique notes worth carrying forward
- **Measurability of cylinders is now proved outright**
  (`measurable_gaussMap`/`measurable_cfDigit`/`measurableSet_cfCylinder`,
  private in `CFDigitLaw.lean`) — W1's "never need measurability" stance is
  obsolete; `measure_biUnion` is available for W3.
- **`tsum_mul_log_cfK_le` went by first-digit peeling**, not positional
  marginals: `K(k::s) ≤ (k+1)K(s)` + partition identities + distortion +
  digit law, induction on `n` with the base word `w` generalized.
  `genConsEquiv : {k // 1 ≤ k} × genWords n ≃ genWords (n+1)` (via
  `Equiv.ofBijective`) and `ENNReal.tsum_prod` (needs the `f :=` binder
  types spelled out) do the reindexing.
- Summability of `Σ log(j+2)/((j+1)(j+2))`: `log x ≤ 2√x` (from
  `Real.log_le_sub_one_of_pos` at `√x`) against the `3/2`-p-series
  (`Real.summable_one_div_nat_rpow` + `summable_nat_add_iff`).
- ENNReal gotchas hit: `mul_le_mul_right'`/`mul_le_mul_left'` do NOT
  resolve in this pin — use `gcongr`; cancellation lemma is
  `ENNReal.mul_le_mul_iff_left/right` (Operations.lean);
  `ENNReal.add_le_add_iff_right` needs the finiteness argument
  (cylinder ⊆ `Ioo 0 1` gives it).
- `push_neg` deprecated in this pin (warns; prefer `push Not`).

## 🎬 Next actions (W3, per `KHINCHIN.md`)
1. Read `KHINCHIN.md` §W3 and freeze the mixing/Chebyshev statement
   shapes with kernel-checked anchors (planted-scaffold doctrine, as for
   W1/W2).  Inputs ready: distortion pair, partition calculus,
   `tailDensity_mem_Icc`, Gauss/Lebesgue comparison, `gaussMeasure_univ`,
   `half_mass_long_extensions`.
2. Then the W3 campaign itself.

---
**→ Next session: don't summarize this doc back or wait for instructions;
absorb it and start at Next actions #1.**
