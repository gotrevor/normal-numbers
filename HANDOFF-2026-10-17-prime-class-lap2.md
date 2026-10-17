# Prime class lap 2 (2026-10-17): cyclotomic relation bridge

## Concrete advance

- Added `StonehamPrimeClassCyclotomic.lean`, the first general-family layer required by kickoff
  step 1.  `relationPolynomial` packages `∑ qᵢ X^mᵢ`, and
  `cyclotomic_dvd_iff_aeval_eq_zero` proves that it vanishes at a primitive complex `d`-th root
  exactly when `cyclotomic d ℚ` divides it.
- `linearIndependent_powers_iff_cyclotomic` and
  `not_linearIndependent_powers_iff_exists_cyclotomic` translate arbitrary finite-family
  independence/dependence into the required polynomial divisibility statement.  The latter
  produces a concrete nonzero coefficient vector.
- `linearIndependent_powers_primitiveRoot_congr` proves that this independence criterion is
  independent of the chosen primitive complex root, closing the embedding-choice part of the
  kickoff description.
- Descended the bridge to cleared integer coefficients using Gauss's lemma:
  `cyclotomic_int_dvd_integerRelationPolynomial_iff`.  Finally,
  `cyclotomic_eval_dvd_integerRelation_eval` proves that the cyclotomic value at any finite
  integer representative divides the corresponding cleared relation evaluation.
- The scoped target imports this layer.  Its two analytic T-B′ halves remain the only direct
  sorries; no statement or waiver changed this lap.

## Verification

- `lake env lean src/NormalNumbers/StonehamPrimeClassCyclotomic.lean` — success.
- `lake build NormalNumbers.StonehamPrimeClassCyclotomic` — success, 8,775 jobs.
- `lake env lean src/NormalNumbers/StonehamPrimeClass.lean` — success; only the two ratified core
  declarations report sorry.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target
  NormalNumbers.StonehamPrimeClass` — 8,958 jobs, final verdict `FORMALIZE-TIER GREEN`.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target
  NormalNumbers.StonehamPrimeClassCyclotomic --axioms
  NormalNumbers.StonehamPrimeClass.cyclotomic_int_dvd_integerRelationPolynomial_iff` — 8,775
  jobs, `[Classical.choice, Quot.sound, propext]`, final verdict `FORMALIZE-TIER GREEN`.
- `~/personal/bin/lean-green ~/src/nn-prime-class` — 10,883 jobs; BarrierAudit reports 79
  waivers / 106 open sorries scanned, final verdict `FORMALIZE-TIER GREEN`.

## Current blocker

The remaining arithmetic half of kickoff step 1 is now sharply isolated: prove that for
`d = orderOf (b : ZMod p)` and the compatible representative `w_K = b^(p^K)`, the value
`cyclotomic d ℤ |>.eval w_K` carries the required growing `p`-power (with the separate extra-
precision dyadic statement).  The new evaluation-divisibility lemma then transfers that power
immediately to every cleared dependent relation.  The normal half additionally needs the
converse bounded-loss/nonvanishing statement for independent relation polynomials.

## Next highest-value attack

Stay in kickoff step 1.  Prove the odd-prime finite-root lemma by combining
`teichmullerRepresentative_pow_pred_modEq_one`, the exact order `d` modulo `p`, cyclotomic
factorization of `X^d - 1`, and unit-ness modulo `p` of all factors except `Φ_d`.  Then prove the
dyadic `d = 1` specialization directly from the existing extra-precision tower.  Feed the result
through `cyclotomic_eval_dvd_integerRelation_eval`; only after this finite-level bridge is complete
should the next lap enter the non-normal density argument.
