# HANDOFF: prove `rieszEnergyTail` (branch `wip/riesz-energy`)

**Objective.**  Make `src/NormalNumbers/CoefmassRieszEnergy.lean` sorry-free by proving
`theorem rieszEnergyTail : RieszEnergyTail`.

**Rules:**
- Do NOT change the statement of `RieszEnergyTail`, or the definitions `psiP`, `periodMean`,
  `muP`, `rieszCentered`.  They are under referee review in
  `docs/notes/coefmass-bv-ledger-2026-10-11.md`.  If the statement is false, stop and say so with a
  counterexample (`box stuck`); do not weaken it.
- Helper lemmas may go in the same file.
- No axioms, no `native_decide`.

**Proof plan.**  It is in the module docstring, steps 1–6.  The arithmetic core is step 1, the CRT
product average.  Everything else is finite algebra over `Finset.powerset`.

Suggested order:
1. Prove step 5 (the scalar inequality) first.  It is self-contained.
2. Then steps 2 and 1 (periodicity, CRT average).
3. Then steps 3, 4 and 6.

**Done means:**
1. `lake build NormalNumbers.CoefmassRieszEnergy` is green with no `sorry` warning.
2. `#print axioms NormalNumbers.PrimeModel.SiteFactor.rieszEnergyTail` shows only `propext`,
   `Classical.choice` and `Quot.sound`.
3. As the last step, add `import NormalNumbers.CoefmassRieszEnergy` to `src/NormalNumbers.lean`,
   and confirm the full `lake build` is green (~17 min).
4. Commit on `wip/riesz-energy`.

**Numerical control** (exact, out of tree): J=3, P={7,11,13,17}.  The energy equals the
orthogonal sum `Σ_T (1−w_T)² ∏|μ|² ∏V` to all printed digits:
- K = log 200, k = 1: 0.186636 ≤ 0.298677
- K = log 40, k = 5: 0.516344 ≤ 2.14494

## Status

### 2026-10-11 grind lap 1

Concrete advance in `CoefmassRieszEnergy.lean`:
- proved `one_sub_rieszWeight_sq_le`, completing proof-plan step 5 (the scalar cutoff loss);
- proved `psiP_mod`, completing step 2 (local periodicity);
- proved the local facts `norm_psiP` and `periodMean_psiP_sub_muP`, which supply the
  unimodularity and centered-mean-zero inputs needed by step 3.

Exact verification:
`~/personal/bin/lean-green ~/src/nn-coefmass-riesz-energy --target NormalNumbers.CoefmassRieszEnergy`
ended `FORMALIZE-TIER GREEN`; the only warning in the target file is the original
`rieszEnergyTail` sorry.

Current blocker: proof-plan step 1, a reusable finite CRT product-average identity.  This should
be stated for a finite set of pairwise coprime positive moduli and residue-dependent complex
functions; the prime hypothesis then supplies pairwise coprimality.  Once this is in place,
orthogonality and the diagonal second moment become finite-product calculations.

Next highest-value attack: prove the CRT identity via the equivalence
`ZMod (∏ p ∈ P, p) ≃+* ∀ p : ↑P, ZMod p`, transporting the `Fintype` sum (or, if the
available equivalence API is awkward, induct on `P` using the two-modulus Chinese remainder
bijection).  Then immediately derive the centered cross-term vanishing lemma for two distinct
subsets of `P`.

### 2026-10-11 grind lap 2

Concrete advance in `CoefmassRieszEnergy.lean`:
- proved `sum_range_eq_sum_zmod`, the exact bridge from the theorem's natural-number period sum
  to a `ZMod` sum;
- proved `sum_zmod_prod_eq_prod_sum`, the route-decisive finite CRT product-sum factorization via
  `ZMod.prodEquivPi` and `Fintype.prod_sum`.

Exact verification:
`~/personal/bin/lean-green ~/src/nn-coefmass-riesz-energy --target NormalNumbers.CoefmassRieszEnergy`
ended `FORMALIZE-TIER GREEN`; the target's sole remaining warning is the original
`rieszEnergyTail` sorry.

Current blocker: specialize the generic `ZMod` factorization to the subtype `p : ↑P`.  Supply
`NeZero p` and pairwise coprimality from primality/distinctness, and rewrite
`(ZMod.prodEquivPi ...) x p` as the residue `x.val % p` using `ZMod.prodEquivPi_apply`.

Next highest-value attack: package that specialization as the natural-number CRT average lemma,
then prove that a product with one centered local factor has zero period sum.  This immediately
gives cross-term orthogonality for distinct powerset terms.
