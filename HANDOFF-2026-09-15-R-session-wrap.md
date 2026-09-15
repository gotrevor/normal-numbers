# Handoff: objective R — session wrap (laps 132–145)

**Date**: 2026-09-15 · **Branch**: `wip/g4-entropy` · **HEAD**: `c648de3` · `lake build` 🟢 9040 jobs
· working tree clean · every headline declaration `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).

## Verdict on R: delivered, and then some

DIRECTION's ACTIVE override asked for R-a..R-d on the row-balanced cancellation question and said
"stop when R has a kernel verdict".  R has one, and the laps after it closed nearly all of the
surrounding debt.

### R proper (laps 132–136) — `src/NormalNumbers/G4BalancedRigidity.lean`
* **R-a** the exact proposition + `K = 1`; **R-b** the probe (transfer-matrix DFS: no `K = 2`
  witness on grids to `6×6`, a `K = 3` witness found); **R-c** the verdict; **R-d** the pricing.
  All recorded in `DESIGN-2026-09-15-row-balanced.md`.
* **The threshold is exact**: row-balance forces "ignores a coordinate" at `K ≤ 2`
  (`ignores_coord_of_balanced_two`, via the grid lemma `two_dim_rigidity`) and fails at `K ≥ 3`
  (`ex_balanced`/`ex_not_ignoring`).
* **And the refutation does not reopen the deformation.** The confinement never needed rigidity:
  `MDF` is the right invariant (`mdf_of_balanced`, `mdf_d_t_of_two_balanced_layers`,
  `mdf_eq_zero_of_skel`, `card_skel_le`, `card_mdf_pairs_le`) and `Sched.balanced_union_le` gives
  upper density `≤ dmin^{−H/2}`, subsuming `G4DeformationVerdict` for `K′ ≥ 2`.
* **Sharpness**: `one_balanced_layer_insufficient` — one balanced layer imposes nothing
  (`t := j d` makes the layer constant for a `d` outside `MDF`), so the two-layer hypothesis
  cannot be weakened.

### R's three "still open" items — all moved
1. **(E), the error budget** (laps 133, 136–145): was a prose estimate the design declined to
   formalize; now proved except for instantiation.  See the chain below.
2. **A different matrix `A`** (lap 134): `card_pairs_le_of_determining` abstracts the count away
   from `D_s^{⊗K}` — a new matrix needs only a small determining set for its own balance
   relations, not a new confinement proof.
3. **The single-`n` joint sample** (lap 135): `Grouped.grouped_union_card_le` quantifies it —
   with `G` groups of minimum size `w`, density coefficient `G H dmax/(2 dmin^w)`; confinement
   survives iff `w ≳ 2 log H / log dmin`.  The sample may be broken into `H/w` blocks; they must
   be that large.

### The (E) chain — `src/NormalNumbers/G4RowVariance.lean` (new module)
Every link machine-checked:

    avg_indicator_dvd_progression   frequencies on the real progression sample, δ = O(1/N)
      ← card_filter_modEq_sub_le, avg_indicator_modEq_sub_le, exists_class_of_coprime,
        avg_image_progression; avg_indicator_dvd_two_progression + exists_class_of_two (CRT pairs)
    → rough_variance_lower          v = Σ_p (1/p)(1−1/p) − 3|S|²/N   (input 1)
      ← avg_sq_centred_sum (exact identity), avg_sq_centred_sum_approx (δ-slack version)
    → cross_shift_corr_le           ε ≤ Σ_{p∣Δ} 4/p + Σ 3/p² + 3|S|²/N   (input 2)
      ← not_both_dvd, avg_centred_mul_of_disjoint, avg_centred_dvd_nonpos
    → sampleAvg_sq_lower, rowVariance_half     the anti-concentration deduction
    → Budget.RoughRowVarianceLower             the named (E) interface
    → Budget.budget_forces_two_layers          K′ ≥ 2 at K ≥ 8
      ← Budget.released_coeff_sum, Budget.released_budget_exceeded
    → Sched.balanced_union_le                  union density ≤ dmin^{−H/2}

## Next lap: the final assembly (no new mathematics)
Feed `rough_variance_lower` (v) and `cross_shift_corr_le` (ε) into `rowVariance_half` at the row's
released pairs `(α, j)`, `j > K′`, with weights `c_{α,j} = A_{να} 4^{-j}`:
1. index by released pairs; `ratio := (Σ|c|)²/Σc² ≈ 2^K` for that weight vector;
2. discharge `ε · ratio ≤ v/2` using the gap-divisor count (`≤ log|Δ|/log T` primes `p ∣ ρ_i − ρ_j`,
   each `≤ 1/T`) and `N ≫ R²`;
3. conclude `Budget.RoughRowVarianceLower` outright, which closes (E).

## Working notes for whoever picks this up
* **Do not patch long proofs by string-slicing** — a slice pattern matched text a previous
  replacement had just inserted and silently corrupted a branch (lap 145).  Rewrite the theorem.
* **`linarith`/`nlinarith` fail on goals over `set`-bound atoms** even when the inequality is
  linear in the right atoms.  Factor the numeric core into an abstract standalone lemma and apply
  it (`abs_diag_bound`, `abs_disj_bound`, `abs_offdiag_bound` are the pattern).
* `avg_double_sum'` and the `avg_sq_centred_sum*` family carry `omit [Fintype ι]` so they apply at
  `ι = ℕ`.  An `omit ... in` must precede the docstring, not sit between docstring and declaration.

## State of `src/`
`src/` carries only the two pre-expedition off-path `sorry`s
(`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_drift_one_background`), both on
DIRECTION's forbidden-drift list.  Nothing this session touched them.

Nothing in this session is a claim about the normality of `G₄`.
