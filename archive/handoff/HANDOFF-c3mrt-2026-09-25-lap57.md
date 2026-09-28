# HANDOFF c3-mrt 2026-09-25 lap57 — obligation A, brick 2: truncation over an arbitrary index set

**New file** `src/NormalNumbers/C3MrtProgTrunc.lean` (chain tip:
`lake build NormalNumbers.C3MrtProgTrunc`, 8988 jobs).  Sorry-free, 2 declarations, trust triple.
`lake build` green (9257).

## Brick 2 turned out to be a specialisation, not a new estimate

`multi_truncation_telescope` (lap 43) was ALREADY stated for an arbitrary `S : Finset ℕ` with
`∀ n ∈ S, n < N` — the two-term block-mass invariant never looks at the shape of `S` — and
`joint_multi_harmonic_mass` (lap 42) likewise takes an arbitrary `S`.  The only thing tying
`multi_truncation_bound` to `range N` was its own statement.

* `multi_truncation_bound_set` — the same bound `K·truncA + (1+log N)·K^{K²}·truncB` for every
  `S ⊆ range N`.
* `multi_truncation_bound_prog` — the case `S = {n < N : n ≡ n₀ (mod Mo)}`, one line.

**Recorded because it was not obvious a priori**: the progression could have cost a new mass
estimate (the class mod `Mo` meets each `d`-class in a class mod `lcm(Mo, lcm d)`, so the
individual masses shrink), but the bound is *monotone in `S`*, so nothing is needed.  The
larger-modulus gain proved in lap 56 (`C3MrtProgForms`) is available but **unused** here — it will
be used in brick 3, where the inner sums are reindexed along the joint class.

## NEXT — obligation A, brick 3: the inner layer

`multi_full_sum_bound` (`C3MrtMultiTupleMass`), `inner_multi_bound` and `multi_bound_of_rung`
(`C3MrtMultiInner`).  These are the ones that reindex each `d`-class as `L·j + a` and feed the
result to the rung; that is where `C3MrtProgForms` enters:

* replace `inner_sum_multi_forms` by `inner_sum_prog_forms` (so `L ↦ progLcm Mo d`);
* replace `nondegenerateForms_of_tuple` by `nondegenerateForms_prog`;
* the inner harmonic bound `inner_harmonic_le_generic` / `progression_sum_bound_generic` are
  already *generic* in the modulus (lap 46 named them so deliberately), so they take `progLcm`
  with no change;
* `kfold_lcm_mass_le` bounds `∏_i (1/d_i)` against `K^{K²}/lcm d`; compose with
  `Nat.le_of_dvd` on `lcm d ∣ progLcm Mo d` to get `K^{K²}/progLcm`, i.e. the estimate only
  IMPROVES.

Then brick 4 = the ε-chase (`multi_correlation_of_uniform_rung` with `progLcm`) and
`rung_multi_uniform` over the progression, giving `ProgressionLogRung K` outright and discharging
obligation A.
