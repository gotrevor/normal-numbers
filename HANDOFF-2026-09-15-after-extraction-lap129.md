# Handoff: after-the-extraction lap 129 — L1 and L2 proved; F (design lap) is next

**Date**: 2026-09-15 · **Branch**: `wip/g4-entropy` · tree clean after this commit

## 🎯 Objective
`DIRECTION.md` ACTIVE override "AFTER THE EXTRACTION": L1, L2, then F (design lap first), W on
slack.  Spec: `BRIEF-after-extraction-2026-09-14.md`.

## ✅ This lap (all `lake build` green, all `#print axioms` = `[propext, Classical.choice, Quot.sound]`)
* **L1** `src/NormalNumbers/G4ResidualConfinement.lean` — physical index `physIdx d t n = (n−t)/d`
  (= `kIdx` on the schedule, `kIdx_eq_physIdx : rfl`); `recentring` + `recentring_anchor`
  (17 vs 15, no axioms); CRT pinning `modEq_prod_of_forall`; `physIdx_of_pinned`;
  `physIdx_modEq` (index confined mod `D/d_α`); `card_filter_le_of_confined`;
  `density_bound` (`≤ L·m(Σd_α)/(2D) + |ι|m`); `sum_div_prod_le`;
  schedule: `Sched.confinement_at_scale`, `Sched.density_coeff_le`.  Header records the numbers.
* **L1 prose**: `G4EntropyResidueProbe` module + theorem docstrings scoped; footnote in
  `HANDOFF-2026-09-14-entropy-session-wrap-A0-B-E0down.md`.  Theorem kept unchanged.
* **L2** `src/NormalNumbers/G4OffsetRigidity.lean` — `CoordCancel`, `const_of_update_invariant`
  (walk coordinate by coordinate), `offset_rigidity` (`∃ Δ, t' = t + Δ`), `physIdx_translate`,
  `grid_cancel` (the real grid satisfies `CoordCancel` via `proj_update_eq`).  Scope is in the
  module docstring: the coordinatewise mechanism only.

## 🎬 Next
1. **F design lap**: write `DESIGN-2026-09-15-deformation.md`.  Pick one deformation; discharge
   the brief's four preconditions on paper with numbers (orbit indices of unchanged `G₄` with all
   divisibility hypotheses; finite-prefix coverage AND weighting; replacement transport identity
   with its error term priced against the entropy/volume saving; proof plan or obstruction).
   Only then Lean: frozen `Prop` interfaces, transport identity + error term first.
2. **W** on slack: `docs/extracted-normal-number-2026-09-15.md`.

## ⚠️ Gotchas
* `Finset.pow_card_le_prod` needs `MulLeftMono`; prove it in `ℕ` and cast.
* `Nat.cast_div_le` gives `((m/n : ℕ) : ℝ) ≤ m / n`; combine with `Nat.cast_div` when `n ∣ D`.
* `Finset.prod_dvd_of_coprime` is the `IsCoprime` (ring) version; go through `ℤ` with
  `Nat.isCoprime_iff_coprime` and `Nat.modEq_iff_dvd`.
