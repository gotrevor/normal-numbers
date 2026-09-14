# HANDOFF 2026-09-14 — G5 lap 1 (grind): the weight interface exists, transport exact, junk mean proved

Branch `wip/g4-disjunctivity`.  `lake build` 8938 jobs **green**; every new theorem prints
`[propext, Classical.choice, Quot.sound]`.  Two commits this lap (the second is the ℕ-valued
coefficient refactor + docs).

## Read first

`DIRECTION.md` CURRENT DIRECTIVE (campaign G5) outranks this file.  Its mandated "decisive
probe" (C2 with valuations) turned out to be **unnecessary** in the formulation chosen here —
see `PENDING_WORK.md` §"STRUCTURAL FINDING".  This is a route finding, not a directive edit:
the objective (interface + two instances, `ω` verbatim) is unchanged and the interface now exists.

## Mathematics proved (declaration names)

* `PrimeLambert.weightW c = ω + excess c`, `excess c m = ∑_{p∣m} c_p (v_p(m) − 1)`, `c : ℕ → ℕ`;
  `weightW_zero` (`= omegaR`), `weightW_one` (`= Ω`), `weightLambert_zero/one`, `weightW_eq_cast`.
* `excess_mul`, `weightW_mul`, `overlapW_congr` — the exact affine transport identity and its
  periodicity mod `rad d`; `valWeight_mul` (complete additivity).
* `excess_eq_frozen_add_junk`, `frozenExcess_congr` — the split on the progression modulus.
* `card_filter_pow_dvd_le` (one-congruence count), `sum_junk_le` (junk AP-mean),
  `sum_inv_pred_le_harmonic`, `sum_inv_mul_pred_le`, `two_pow_cardFactors_le`,
  `summable_weightW_div_pow`.

## Isolated (stated in prose, to be formalised)

* The class `weightW c` is exactly the additive weights with affine-in-valuation local parts
  and unit indicator coefficient — the largest class the present §4C reaches.
* Coefficients must be integers (orbit identity); bounded by `C` with `C ≤ K` in the schedule.
* The far-tail excess needs `∑_{j>J} b^{−j}(j+1)²`, a new closed form of the `farBound` kind.

## Resume at

`PENDING_WORK.md` §"Next actions", step 1: the weight-generic `Frame` in `G4Wiring.lean`
(`w`, `x` fields; `gridFrame` instantiates `omegaR`, `primeLambertAtBase`; all existing
theorems must stay verbatim).  Then transport (step 2) — `corrW = overlap − overlapW`.
