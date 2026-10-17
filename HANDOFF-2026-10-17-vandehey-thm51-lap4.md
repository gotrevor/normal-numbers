# Vandehey Theorem 5.1 lap 4: twisted subgroup sums proved

## Concrete advance

- Proved kickoff rung 2 in its actual cyclic-subgroup form:
  `NormalNumbers.VandeheyKorobov.norm_twisted_powers_sum_le_sqrt`.
  For `τ = orderOf (b : ZMod m)`, a unit frequency `a`, and any additive
  character `ψ : AddChar (ZMod τ) ℂ`, it proves
  `‖∑_j ψ(j) e_m(a b^j)‖ ≤ √m`.
- The proof uses the sparse Parseval interface from lap 3 correctly:
  - `j ↦ (b^j mod m)` is injective for `j : ZMod τ` by the defining
    minimality of `orderOf`;
  - `Function.extend` places `ψ` at those actual residue coordinates and zero
    elsewhere;
  - the extended vector has exact squared mass `τ`;
  - the frequencies `a b^h mod m` are distinct because `a` is a unit;
  - translation by `h` in `ZMod τ` reindexes the Fourier sum and multiplies it
    by the norm-one scalar `ψ(-h)`.
- Added the consumed specialization
  `norm_completed_power_sum_le_sqrt`, taking
  `ψ = ZMod.stdAddChar.mulShift h`.  This is exactly the completed sum needed
  for Vandehey Lemma 2.2.
- Added the public phase bridges `phase_eq_stdAddChar_zmod`, `phase_val_mul`, and
  `phase_eq_ePhase`, so the finite Fourier API can be connected to the frozen
  theorem's `ePhase` expression without redoing exponential algebra.

## Reflection audit

- The theorem is about arbitrary subgroup characters, not merely untwisted
  subgroup sums, and its support is the actual set of power residues.  Thus it
  matches kickoff rung 2 and avoids lap 3's rejected dense-coordinate shortcut.
- No frozen definition or corollary statement changed.  The only `sorry` in
  `src/NormalNumbers/VandeheyProof.lean` remains the headline
  `vandeheyThm51_holds`; no helper debt was introduced.
- The scoped target is not complete: kickoff rungs 3--6 remain.

## Verification actually run

- `taskset -c 0-3 lake env lean -j 1 src/NormalNumbers/VandeheyKorobov.lean`
  -- passed after integration.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green \
    /Users/gotrevor/src/nn-vandehey \
    --target NormalNumbers.VandeheyProof \
    --axioms NormalNumbers.VandeheyKorobov.norm_twisted_powers_sum_le_sqrt`
  -- `Build completed successfully (8924 jobs)`; the new rung-2 theorem's
  axiom list was exactly `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.

## Current blocker

Kickoff rung 3 now reduces to the finite completion identity plus the sharp
Dirichlet-kernel L1 estimate

`(1 / τ) * Σ_h |Σ_{1 ≤ n ≤ N} e(-hn/τ)| ≤ 1 + log τ`

for `1 ≤ N ≤ τ`.  The completed power-orbit factor is discharged by
`norm_completed_power_sum_le_sqrt`.

The constant matters: using only `harmonic_le_one_add_log` loses an extra `1`
and does not fit the frozen `k = 0` constants.  The sharp elementary bookkeeping
is still available.  Pair frequencies `h` and `τ-h`, use the geometric-sum
bound `≤ τ/(2 min(h,τ-h))`, and prove the centered harmonic estimates

- `H_n ≤ log(2n+1)` (odd `τ = 2n+1`),
- `H_{n-1} + 1/(2n) ≤ log(2n)` (even `τ = 2n`).

For the induction step, mathlib's `Real.sum_range_le_log_div` at one term gives
`2x ≤ log((1+x)/(1-x))`; take `x = 1/(2k)` to obtain the telescoping increment
`1/k ≤ log(2k+1)-log(2k-1)`.

## Next highest-value attack

1. Prove the centered harmonic inequalities above as reusable elementary
   lemmas (including `τ = 1,2` boundary cases).
2. Prove the geometric character-sum bound and pair the nonzero residues to
   obtain the exact Dirichlet-kernel L1 estimate.
3. Use finite character orthogonality to expand the interval indicator on
   `ZMod τ`, apply `norm_completed_power_sum_le_sqrt` termwise, and conclude
   the repaired `d = 1` form of Vandehey Lemma 2.2.
4. Proceed in kickoff order to Lemma 2.3; do not start the differencing rung
   before completion is kernel-checked.

Do not call `box done`: the host predicate
`sorry-free:src/NormalNumbers/VandeheyProof.lean` is not met.
