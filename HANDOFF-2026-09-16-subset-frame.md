# HANDOFF 2026-09-16 — campaign A: the whole G4 route is now weight-generic; conditional headline for `c_S` proved

Branch `wip/g5-prime-subset`, HEAD `1f6089f`, working tree clean, `lake build` green (9051 jobs).
Every new declaration prints `[propext, Classical.choice, Quot.sound]`; no `sorry` in any new module.

## What landed this session (11 green commits)

1. **`G4TransportW.lean`** — `TWeight`: the four properties §4A actually uses (integrality,
   `w(dm)+ov(d,m)=w(m)+w(d)`, `ov ≤ ω(d)` and periodic mod `rad d`, summability).  §4A re-proved
   once generically (`tailB_eq`, `dilatedTailB_eq`, `corrB_congr`, `coe_tailB`) plus
   `Frame.propA_of_progressionW`.  Instances `TWeight.omega`, `TWeight.subset S`.
2. **`G4FrameW.lean`** — `gridFrameW W …`; with `W = TWeight.omega` it is *definitionally* the old
   `gridFrame` (`gridFrameW_omega := rfl`), so nothing downstream moved.  `gridFrameW_propA`,
   `gridFrameW_propC_gen`, `exists_cover_of_omit_gen`, `gridFrameW_propB_of_bound`.
3. **`G4RemainderW.lean`** — `omegaSN_split` / `omegaS_split` / `omegaBigS_le_omegaBig`;
   `blockSum_omegaS_split` (**the structural point: the `S`-local layer is `Sval` of the FILTERED
   finset `(smallPrimes R P₀).filter S`**, so §4C needs no new arithmetic); `tailFromW`,
   `farPartW`, `gridFrameW_Ffull_eq`, `tailFrom_splitW`, `frozenGammaS`,
   `gridFrameW_subset_Ffull_decomp`, `bigAvgS`/`farAvgS`, `gridFrameW_subset_propD`.
4. **`G4SubsetJunk.lean`** — `sum_sq_blockSum_sub_le` / `sampleAvg_abs_blockSum_sub_le` (the §4D
   moments for ANY `T ⊆ medPrimes R Y P₀`), `omegaVLS`, `omegaBigS_split`,
   `abs_blockSum_omegaVLS_le`, `bigAvgS_le`, `bigAvgS_le'`, `sum_abs_farPartW_subset_le`,
   `farAvgS_le`, `gridFrameW_subset_propD_of_bounds` — **the S-junk meets the same two closed
   inequalities as the ω-junk**.
5. **`G4SubsetWitness.lean`** — `ScheduleWitnessS` (= `ScheduleWitnessB` with the small primes
   filtered by `S`), `separatingFrameExistsW_subset_of_witness`, and
   **`isDisjunctive_subsetLambert_of_witness : IsDisjunctive bb (subsetLambert S bb)`**.
6. **`G4SchedBE.lean`** — A3: the schedule's parameter layer in a **free cutoff exponent `e`**.
   `HypE b K e = Hyp b K + (m₁ b K ≤ e) + (10⁵·T·e ≤ 2^{m₂})` — exactly the audit's floor and cap.
   Ported sorry-free: both harmonic bounds, `dyadic_factor_leE`, `log_log_RE_ge`,
   `RE_pow_two_McE_le`, `Kr_le_T_mul_e`, the XE-monotone facts, `farC_leE`, `inv_card_leE`,
   `log_Mx_div_leE`, `P₀_le_two_powE`, `two_pow_div_leE`, **`main_term_leE`** (the gain term — the
   only place the Mertens supply enters), `term_a_leE`, `term_d_leE`.

## Where campaign A stands

In kernel: Mertens-in-AP (`G4MertensAP`), subset arithmetic (`G4SubsetWeight`), the cutoff/feasibility
layer (`G4SubsetSchedule`), the **entire analytic route A–D for `ω_S`**, the conditional headline,
and most of the `e`-parametrized schedule.

## Resume here (in order)

1. **`term_b_leE` / `term_c_leE`** in `G4SchedBE.lean` — port from `G4SchedBBudget` lines 249–345
   the same way (`R b K → RE e`, `Mc b K → McE K e`, `m b K → mE K e`, `Hyp b K → HypE b K e`,
   `sum_inv_smallPrimes_le → sum_inv_smallPrimes_leE`, `3 * m₁ b K + 5 → 3 * e + 5`).  These two
   are where the *upper* harmonic bound is consumed; `Mc ≳ 44·T·e` is why the cap exists.
2. **`hbudget_holdsE`** (from `G4SchedBBudget.hbudget_holds`), then the `e`-version of
   `G4SchedBAssembly`'s witness construction, with the small primes replaced by
   `(smallPrimes (RE e) P₀).filter S` in the `δ₃` slot of `ScheduleWitnessS`.
3. Feed `G4SubsetSchedule.exists_cutoff_subset` (gives the `e` meeting the demand from a
   `MertensRate`) and `moment_cap_subset` (gives `HypE.hi`) to build `ScheduleWitnessS`, then
   `isDisjunctive_subsetLambert_of_witness` ⇒ **`isDisjunctive_residueClass`** via
   `mertensRate_residueClass`.
4. Sanity instance: `S = fun _ => True` must re-derive `isDisjunctive_base`'s statement
   (`subsetLambert_univ` is already proved).

Design map: `DESIGN-2026-09-16-prime-subset.md`.  Note its standing finding: bare divergence of
`∑_{p∈S} 1/p` is NOT enough for this route — a *rate* is, and any fixed `c > 0` suffices.
