# HANDOFF 2026-09-14 — G4 disjunctivity, lap 9 (Jackson + B discharged; only §5 remains)

Branch `wip/g4-disjunctivity`, HEAD `b7c12f4` (final state of lap 9; tree clean).  Not pushed.  Pre-commit
`lake build` (8888 jobs) green on every commit.  Every headline below prints
`[propext, Classical.choice, Quot.sound]`.

## Commits this lap

* `96155de` `G4Jackson.lean` — **`Frame.propJackson`**, unconditional for every frame:
  `PropJackson (1/(res·√(D+1))) ((2D+1)^r)`.  Product Fejér kernel; the pointwise split
  `‖t‖F_D ≤ aF_D + 1/(4(D+1)a)` gives the first moment `1/√(D+1)` with no interval integral.
* `d39c41d` `G4TubeVolume.lean` — **`Frame.volume_tube_le`** (abstract B assembly):
  `vol(tube) ≤ ∑_{G ∈ goodSets} (#Bs)^H η^{|G|} vol([A_G,I_G]·cube)` from a cylinder cover
  with half-width `≤ η`.  Markov in `dAv`, nearest image point by compactness, marginal
  projection measure preserving, torus projection, translation, `addHaar_smul`.
* `0211f8c` `G4GridTube.lean` — **`gridFrame_volume_pieceCube_le`**: on the grid each piece
  cube is `≤ exp(Lg/2)(√(2πe/|G|)√(H+|G|))^{|G|}` with `Lg ≥ log det(1 + T_s^{⊗K})`
  (via `Frame.volume_pieceCube_le_of_reindex`, `gridFrame_AR`).
* `7c157ce` — **`gridFrame_propB_of_bound`**: `PropB δ₁` from ONE real inequality
  (statement in `PENDING_WORK.md` lap 9), plus `exists_cylinder_subset`,
  `exists_cover_of_omit`, `card_goodSets_le`.

## Dependency map (the whole §4 is now discharged modulo §5 arithmetic)

`PropA` ✅ (`gridFrame_propA`) · `PropC` ✅ (`gridFrame_propC`) · `PropJackson` ✅
(`Frame.propJackson`, no side conditions) · `PropD` = two real inequalities
(`gridFrame_propD_of_bounds`) · `PropB` = one real inequality (`gridFrame_propB_of_bound`).
`isDisjunctive_four_of_frames` remains CONDITIONAL on `SeparatingFrameExists`.  Nothing refuted.

## Resume here — the §5 schedule module (`G4Schedule2.lean` or extend `G4Schedule.lean`)

Goal: `SeparatingFrameExists`.  For each omitted `[a,c)`: `exists_cylinder_subset` gives `ℓ, w`;
then for `X` large (one simultaneous limit in `L = log log X`, `K = ⌊log L/(100 log log L)⌋`,
`s = K²`, `η = 2^{−K/4}`, `ε = 1/K`, `M = ⌈K/(8ℓ)⌉`, `D` polynomial in `2^{K/4}`) build the
`GridParams` (needs `P₀, Q, D₀, U, B` per draft (3.2) — check `G4Progression`/`G4CRTInput` for
the existing constructors), the `gridFrame`, and verify:
1. B: `((4^ℓ−1)^M)^H η^g e^{Lg/2} (√(2πe/g)√(H+g))^g ≤ δ₁/2^r` for `(1−ε)r ≤ g ≤ r`, with
   `Lg = r(log 2 + 23√K)` (`log_det_one_add_tensorGram_le'`).  Paper: exponent
   `(K/4)(dH − g) + O(r√K) < 0` once `√K(1−d−ε−1/K) ≳ 70`, `d = log_4(4^ℓ−1)`.
2. D: the two inequalities of lap 7 (`bigAvg_le'`, `farAvg_le`) with `R = X^{1/(20M)}`, `Y = X^{1/100}`.
3. C: `δ₃` from `gridFrame_propC`, and `Λδ₃ = (2D+1)^r e^{−cL8^{−K}} → 0` by `schedule_budget` (C4).
4. Jackson: `2κ = 2/(εη√(D+1))` small ⇐ `D ≥ (8K 2^{K/4})²`.
Budget: `δ₁ + δ₂ + 2κ + Λδ₃ < 1`.  Trigger **G-T3** applies if the limit cannot close all four
simultaneously: then the honest endpoint is the conditional theorem plus the named gap.

## Addendum (lap 9b) — `ScheduleWitness` and the full paper check

`G4ScheduleWitness.lean` (`69e3ebf`): `separatingFrameExists_of_witness`,
`isDisjunctive_four_of_witness`.  The candidate proof is now exactly "produce a
`ScheduleWitness ℓ w` for every omitted cylinder".  Paper check of all five inequalities is in
`PENDING_WORK.md` (lap 9b).  **One constraint the brief does not state**: the far tail carries
`farC ≈ log P₀ ≈ K^{5K}N^K`, so the retained depth must be `N ≈ 10 K log K`, not merely
`1 + ⌈log₄(2^K D)⌉`.  With that choice everything closes on paper.  Resume at attack step (1):
an explicit `GridParams` constructor from `(K, N)` with a `log P₀` bound.
