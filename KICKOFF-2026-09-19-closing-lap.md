# KICKOFF 2026-09-19 — closing lap: W4 + L1 + assembly (PREPARED, not fired)

Branch `wip/g5-prime-subset`.  Engine Opus/low.  Design: `DESIGN-2026-09-19-bcr-wiring.md` §3b.
Goal: `src/NormalNumbers/G4WiringCRT.lean` and `src/NormalNumbers/DyadicToPrefix.lean` sorry-free.
Then `NormalNumbers.G4.isNormal_G4_of_CRTConstant` is a theorem: normality of G₄ from the two
frozen Props `CRTConstant` (all h ≠ 0) and `SiteDecayFull`.  **Do not touch the two Props' statements.**

## Leaves, in order (each a named `sorry` already in the file; commit after each)

1. `DyadicToPrefix.prefixMean_tendsto_zero_of_dyadic` — `KICKOFF-2026-09-19-dyadic-to-prefix.md`.
2. `orbit_eq_fract_tailB`: `orbit 4 G₄ n = Int.fract (TWeight.omega.tailB 4 n)`.  Repo has
   `TWeight.coe_tailB` (equality in `UnitAddCircle`) and `TWeight.lambert_omega`; both sides lie in
   `[0,1)` (`orbit_mem_Ico`, `Int.fract_nonneg/lt_one`), and equal images in `UnitAddCircle` of two
   reals in `[0,1)` are equal (`AddCircle.coe_eq_coe_iff_of_mem_Ico` or `AddCircle.equivIco`).
3. `tail_error_le`: `tailB 4 n − truncTail J n = ∑' i, ω(n+J+i+1)/4^{J+i+1}` (split the tsum,
   `sum_add_tsum_nat_add`), then `ω(m) ≤ log₂ m` (`PrimeLambert.omegaR_le_log`),
   `log₂(n+J+i+1) ≤ log₂(n+J+2) + i` (mirror `PrimeLambertTail.log_add_le`), and the base-4 analogue of
   `PrimeLambertTail.tsum_majorant` (`∑ (A + i)/4^{i+1} ≤ (A + 1)/…`; any constant works since the
   statement allows `+ 3`).
4. `tail_error_uniform`: `windowJ N = log₂ log₂ N + 1`, so `4^{windowJ N} ≥ 4 · log₂ N`-ish and the
   numerator is `≪ log₂ N`; conclude with `tendsto_const_div_atTop_nhds_zero_nat`-style lemmas or
   squeeze by `(log₂ N + …)/(log₂ N)^2 → 0`.  Any clean route; the schedule is yours to tweak if
   `windowJ` is inconvenient (it must be `≥ 1` and `→ ∞`, with `4^{-J_N} log N → 0`).
5. `fullWindowMean_tendsto_zero`: from `hLaw h hh` get `c, B, C`; for `N` large `windowJ N ≥ 1` and
   site `j = 1` has `h/4 ∉ ℤ` unless `4 ∣ h`; in general pick the least `j` with `4^j ∤ h`
   (`j ≤ padicValNat 2 h / 2 + 1`), which is `≤ windowJ N` eventually.  Then
   `‖W‖ ≤ (B + C/log N) ∏‖m_j‖ ≤ (B + C/log N) ‖m_j₀‖` (all `‖m_j‖ ≤ 1`), and `hSite` finishes.
   ⚠️ The law is stated at fixed `J` with `∀ᶠ N`; applying it at `J = windowJ N` needs the
   eventual bound to hold uniformly in `J` — it does, because `C` does not depend on `J`, but the
   `∀ᶠ N` threshold may.  If that blocks, **strengthen the Prop to `∀ᶠ N, ∀ J`** (state the change in
   the handoff; it is the intended reading, KB verdict §2f) rather than weakening the theorem.
6. `dyadic_fourier_tendsto_zero`: `ePhase(h · orbit) = ePhase(h · tailB)` (fract drops integers,
   `Complex.exp_int_mul_two_pi_mul_I`), `‖ePhase(h tailB) − ePhase(h truncTail)‖ ≤ 2π|h| · tail error`
   (`PrimeLambertAnalytic.norm_e_sub_one_le` is the same estimate with `4π`), average over `[N,2N)`,
   then leaf 5.
7. The two `sorry`s in `isNormal_G4_of_CRTConstant`: `fourierMean u h n = prefixMean (fun n => ePhase (h * u n)) n`
   (unfold both; `ePhase` is literally the summand) and `‖ePhase x‖ ≤ 1` (`Complex.norm_exp_ofReal_mul_I`).

## Rules
Report the advance, not the sorry count.  `box done --green` when both files are sorry-free.  Nothing
else in the repo is in scope; the two frozen Props are guarded by name and statement.
