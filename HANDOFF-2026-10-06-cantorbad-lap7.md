# HANDOFF 2026-10-06 cantorbad lap 7 (branch proof/cantor-bad-normal)

Target unchanged: `exists_mem_cantorSet_bad_isNormal_coprime_three`.  Build green, no uncommitted edits.
Headline `#print axioms`: trust base + `sorryAx` + `J_lt`/`J_inj` native_decide artifacts.

## Done (all in CantorBadNormal.lean, all proved)
- Generic `ae_cesaro_of_secondMoment(_bdd)` (2nd moment O(N²W), W summable along `sched` ⇒ a.s. Cesàro).
- Martingale leaf closed: `condDiff_secondMoment_le` (`integral_orth`, `norm_integral_cross`), so
  `ae_cesaro_condDiff` proved.
- Cantor leaf closed: `cesaro_contChar_small` (`tendsto_fourierMean_linear`, `irrational_logb_three`,
  `norm_muK_le_GC`, liftIco circle function, `tendsto_integral_GC` via `int_of_close`).
- Crux splits: `LocalDeadBias` ⇐ `LocalBiasRate` (`localDeadBias_of_rate`) ⇐ `LocalBiasMixing`
  (`localBiasRate_of_mixing`, via `condMean`, tower `integral_comp_mul_condMean`, `biasMix`).
- Toward the obstacle-phase node: `condMean_condMean`, `condMean_sub`, `condMean_localBias`,
  `muK_succ/iter/stage`, `rhoS_eq_prod`, `real_child`, `setIntegral_buildU_succ`,
  `setIntegral_contChar_succ` (one-stage identity: next-stage contChar averages to contChar − deadCorr).

## Open in CantorBadNormal.lean
- On-path: ONLY `localBiasMixing_resLaw` (crux, believed 60%).
- Off-path: `midStages`, `fourierPairRate_descent_of_deadRateDecay`.

## Next
1. Telescope: `E[B_m|w_s] = −Σ_{t∈[s_m,T)} E[D_t|w_s] + O(|ξ|3^{−10T})`, `D_t = ee(ξ cylLeft w_t)·deadErr·muK(ξ/3^{10t+10})`
   (a.e. version of the one-stage identity + `condMean_condMean`; `|1 − muK η| ≤ 2π|η|`).
2. State the obstacle-phase node on `E‖E[D_t | w_{s_n}]‖` (t near s_m) and prove `LocalBiasMixing` from it
   (tail t ≥ s_m + R via `norm_deadErr_le`).
3. Difficulty (PENDING_WORK): the node is an exponential sum `Σ e(hbᵐ p/q)` over rationals near K, q ≈ 3^{5t};
   any proof with a rate likely needs input on digits of bᵐ (Baker-type) — DIRECTION forbids midStages-style tails,
   flag to the altitude lap if the node can't avoid it.
