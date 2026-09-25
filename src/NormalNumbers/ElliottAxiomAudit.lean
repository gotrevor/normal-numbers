import NormalNumbers.ElliottTwoPointLog
import NormalNumbers.ElliottZetaOmegaPretentious
import NormalNumbers.ElliottTwistBootstrap
import NormalNumbers.ElliottCharRigidity
import NormalNumbers.ElliottArchimedeanRefuted
import NormalNumbers.ElliottTwistRepair
import NormalNumbers.ElliottSmallShift
import NormalNumbers.ElliottArchBands
import NormalNumbers.ElliottDamped
import NormalNumbers.ElliottLogIntegral
import NormalNumbers.ElliottGeneral
import NormalNumbers.ElliottHall
import NormalNumbers.ElliottPretentiousTransfer
import NormalNumbers.ElliottProgression
import NormalNumbers.ElliottCaseAThin
import NormalNumbers.ElliottLeafTwo
import NormalNumbers.ElliottRankin
import NormalNumbers.ElliottReindex
import NormalNumbers.ElliottDivisorTail
import NormalNumbers.ElliottExpand
import NormalNumbers.ElliottZetaPole
import NormalNumbers.ElliottPrimePower
import NormalNumbers.ElliottBridge
import NormalNumbers.ElliottRestricted
import NormalNumbers.ElliottScaleDescent
import NormalNumbers.ElliottCaseB
import NormalNumbers.ElliottWindowTruncate
import NormalNumbers.ElliottTruncAssemble

/-!
# Axiom audit surface for the Elliott campaign

This file contains no mathematics.  It exists so that a single
`lake build NormalNumbers.ElliottAxiomAudit` prints the real `#print axioms` base of every
load-bearing theorem of the campaign, for the STATUS.md ledger.

`#print axioms` certifies PROOFS, not STATEMENTS.  The statement-fidelity anchor is that the
headline's TYPE is the dependency's own `Erdos67b.NonasymptoticLogElliott`, which this repo never
edits; see the fidelity note in `STATUS.md`.
-/

-- the headline
#print axioms NormalNumbers.ElliottGeneral.nonasymptoticLogElliottMult
#print axioms NormalNumbers.ElliottGeneral.nonasymptoticLogElliott

-- the ladder
#print axioms NormalNumbers.ElliottLadder.affineCM_of_dilatedCM
#print axioms NormalNumbers.ElliottDilatedRung.dilatedCMLogElliott
#print axioms NormalNumbers.ElliottDilatedRung.dilatedNatShiftCMLogElliott
#print axioms NormalNumbers.ElliottDilatedRung.dilatedNatShiftCMLogElliottMirror
#print axioms NormalNumbers.ElliottTwistedGraph.shiftCMLogElliott
#print axioms NormalNumbers.ElliottTwoShift.twoShiftCMLogElliott

-- leaf 2's proved pieces
#print axioms NormalNumbers.ElliottCaseA.exists_caseA_threshold
#print axioms NormalNumbers.ElliottCaseA.norm_elliottLogCorrelation_le_caseA
#print axioms NormalNumbers.ElliottHall.sum_Icc_normFun_le
#print axioms NormalNumbers.ElliottHall.sum_Icc_dyadic_le
#print axioms NormalNumbers.ElliottEulerBound.sum_Icc_le_log_mul_exp_neg_defect

-- leaf 2: the two-point unimodular cover (lap 54)
#print axioms NormalNumbers.ElliottRandomize.lift_add_lift
#print axioms NormalNumbers.ElliottRandomize.norm_lift
#print axioms NormalNumbers.ElliottRandomize.re_lift_mul_conj
#print axioms NormalNumbers.ElliottRandomize.sum_cover
#print axioms NormalNumbers.ElliottRandomize.sum_sum_elliottLogCorrelation_cover
#print axioms NormalNumbers.ElliottRandomize.exists_cover_pair_ge

-- leaf 2, Case B step 1: the pretentious transfer to the cover
#print axioms NormalNumbers.ElliottPretentiousTransfer.pretentiousDistSq_triangle_bounded
#print axioms NormalNumbers.ElliottPretentiousTransfer.pretentiousDistSq_cover_le
#print axioms NormalNumbers.ElliottPretentiousTransfer.mrtNonpretentious_transfer

-- leaf 2, Case B step 3: the ABSOLUTE squarefull tail bound
#print axioms NormalNumbers.ElliottSquarefull.local_factor_squarefull_le
#print axioms NormalNumbers.ElliottSquarefull.sum_Icc_le_exp_two
#print axioms NormalNumbers.ElliottSquarefullConv.squarefullPart_prime_pow
#print axioms NormalNumbers.ElliottSquarefullConv.sum_norm_squarefullPart_div_le_exp_two

-- leaf 2, Case B step 4: the progression substitution (arithmetic core)
#print axioms NormalNumbers.ElliottProgression.integerAffine_progression
#print axioms NormalNumbers.ElliottProgression.det_progression

-- leaf 2, step 5: Case A in the THIN window (no regime hypothesis)
#print axioms NormalNumbers.ElliottCaseAThin.sum_window_le_transfer_ge
#print axioms NormalNumbers.ElliottCaseAThin.le_integerAffine_of_mem_window
#print axioms NormalNumbers.ElliottCaseAThin.norm_elliottLogCorrelation_le_caseA_thin
#print axioms NormalNumbers.ElliottCaseAThin.div_le_four_mul
#print axioms NormalNumbers.ElliottCaseAThin.natLog_mul_log_two_le

-- leaf 2, the assembly (COMPLETE: every half below is trust-triple)
#print axioms NormalNumbers.ElliottLeafTwo.nonasymptotic_of_affineCM

-- the Rankin shift: ingredients for the uniformly small squarefull tail
#print axioms NormalNumbers.ElliottRankin.local_factor_geom_le
#print axioms NormalNumbers.ElliottRankin.sum_Icc_inv_mul_sqrt_le
#print axioms NormalNumbers.ElliottRankin.sum_primesBelow_inv_mul_sqrt_le
#print axioms NormalNumbers.ElliottRankin.sum_Icc_shifted_le
#print axioms NormalNumbers.ElliottRankin.exists_squarefull_tail_bound

-- the progression reindexing: the analytic half of the Case-B substitution
#print axioms NormalNumbers.ElliottReindex.progression_image
#print axioms NormalNumbers.ElliottReindex.sum_progression_eq
#print axioms NormalNumbers.ElliottReindex.norm_sum_sub_reindexed_le
#print axioms NormalNumbers.ElliottSquarefullConv.squarefullPart_mul_cmExt
#print axioms NormalNumbers.ElliottSquarefullConv.U_eq_sum_divisors

-- the divisor tail over the window: the cost of truncating the expansion at D
#print axioms NormalNumbers.ElliottDivisorTail.sum_Icc_multiples_inv_le
#print axioms NormalNumbers.ElliottDivisorTail.sum_window_le_transfer_nonneg
#print axioms NormalNumbers.ElliottDivisorTail.sum_window_divisor_tail_le

-- the squarefull expansion of the correlation, and its truncation at D
#print axioms NormalNumbers.ElliottExpand.posExt_eq_sum_divTerm
#print axioms NormalNumbers.ElliottExpand.elliottLogCorrelation_expand
#print axioms NormalNumbers.ElliottExpand.norm_elliottLogCorrelation_le_truncated

-- each restricted correlation becomes genuine correlations at the reduced scale
#print axioms NormalNumbers.ElliottRestricted.det_newShift
#print axioms NormalNumbers.ElliottRestricted.norm_restrictedCorr_le

-- non-pretentiousness descends to the reduced scale at an absolute cost
#print axioms NormalNumbers.ElliottScaleDescent.pretentiousDistSq_descend
#print axioms NormalNumbers.ElliottScaleDescent.mrtNonpretentious_descend
#print axioms NormalNumbers.ElliottLeafTwo.exists_squarefull_tail

-- leaf 2, the two halves of the dichotomy
#print axioms NormalNumbers.ElliottLeafTwo.exists_caseA_thin_threshold
#print axioms NormalNumbers.ElliottLeafTwo.exists_caseB_threshold
#print axioms NormalNumbers.ElliottCaseB.exists_caseB_threshold

-- leaf 2, Case B: the cost-shaped expansion steps and the threshold family
#print axioms NormalNumbers.ElliottStageStep.norm_le_of_reduced
#print axioms NormalNumbers.ElliottStageStep.norm_le_of_reduced_second
#print axioms NormalNumbers.ElliottStageCost.norm_le_cost_first
#print axioms NormalNumbers.ElliottStageCost.norm_le_cost_second
#print axioms NormalNumbers.ElliottStageCost.mrtNonpretentious_cmExt
#print axioms NormalNumbers.ElliottThresholdFamily.det_final
#print axioms NormalNumbers.ElliottThresholdFamily.memberThreshold_spec
#print axioms NormalNumbers.ElliottZeroExt.norm_sub_posExt_le
#print axioms NormalNumbers.ElliottMertensIterate.reciprocalPrimeInterval_iter
#print axioms NormalNumbers.ElliottMertensIterate.mrtNonpretentious_descend_iter

-- leaf 2, the truncation of the window from below (the dichotomy-scale repair)
#print axioms NormalNumbers.ElliottWindowTruncate.norm_le_truncated
#print axioms NormalNumbers.ElliottTruncAssemble.discarded_mass_bound
#print axioms NormalNumbers.ElliottTruncAssemble.X_le_thinScale_pow

-- the dependency's proved special case
#print axioms Erdos67b.unitCircleLogElliott

/-! ### The downstream consumer (`DIRECTION.md` item 4) -/
#print axioms NormalNumbers.ElliottTwoPointLog.twoPointElliottLog_of_nonPretentious
#print axioms NormalNumbers.ElliottTwoPointLog.isCoprimeMult_zetaOmegaInt
#print axioms NormalNumbers.ElliottZetaOmegaPretentious.zetaOmegaDistSq_eq
#print axioms NormalNumbers.ElliottZetaOmegaPretentious.exists_norm_twistCorr_sub_primeMass_le
#print axioms NormalNumbers.ElliottZetaOmegaPretentious.exists_mertensOne
#print axioms NormalNumbers.ElliottZetaOmegaPretentious.twoPointElliottLog_of_dichotomy
#print axioms NormalNumbers.ElliottTwistBootstrap.twistDefect_pow_le
#print axioms NormalNumbers.ElliottTwistBootstrap.exists_unimodular_twistDefect_le
#print axioms NormalNumbers.ElliottTwistBootstrap.dirichletChar_pow_totient
#print axioms NormalNumbers.ElliottTwistBootstrap.norm_powCorr_sub_archCorr_le
#print axioms NormalNumbers.ElliottTwistBootstrap.norm_twistCorr_le_of_archCorr_le
#print axioms NormalNumbers.ElliottTwistBootstrap.exists_charDefect_le
#print axioms NormalNumbers.ElliottTwistBootstrap.twistModulusDichotomy_of_inputs
#print axioms NormalNumbers.ElliottTwistBootstrap.twoPointElliottLog_of_classical_inputs
#print axioms NormalNumbers.ElliottCharRigidity.eq_one_of_pow_eq_one_of_norm_lt
#print axioms NormalNumbers.ElliottCharRigidity.exists_characterClusterRigidity
#print axioms NormalNumbers.ElliottCharRigidity.twoPointElliottLog_of_archimedean_and_density

/-! ### The refutation of input (c) (lap 92) -/
#print axioms NormalNumbers.ElliottArchimedeanRefuted.not_archimedeanCorrelationBound

/-! ### The repaired decomposition (lap 92) -/
#print axioms NormalNumbers.ElliottTwistRepair.re_phase_mul_twistCorr_le
#print axioms NormalNumbers.ElliottTwistRepair.twistAlmostRealDichotomy_of_old
#print axioms NormalNumbers.ElliottTwistRepair.uniformlyNonPretentious_zetaOmega_of_almostReal
#print axioms NormalNumbers.ElliottTwistRepair.twistAlmostRealDichotomy_of_inputs
#print axioms NormalNumbers.ElliottTwistRepair.twoPointElliottLog_of_repaired_inputs

/-! ### Input (e) discharged by scale reduction (lap 93) -/
#print axioms NormalNumbers.ElliottSmallShift.abs_primeMass_sub_logLog_le
#print axioms NormalNumbers.ElliottSmallShift.norm_twistCorr_sub_le
#print axioms NormalNumbers.ElliottSmallShift.uniformlyNonPretentious_zetaOmega_of_almostRealProp
#print axioms NormalNumbers.ElliottSmallShift.almostRealProp_or_far_of_reductionScale
#print axioms NormalNumbers.ElliottSmallShift.exists_reductionScale
#print axioms NormalNumbers.ElliottSmallShift.twistAlmostRealPropDichotomy_of_inputs
#print axioms NormalNumbers.ElliottSmallShift.twoPointElliottLog_of_archimedean_and_rigidity
#print axioms NormalNumbers.ElliottSmallShift.twoPointElliottLog_of_archimedean_and_primeDensity

/-! ### (c′) split into bands: the soft band and the isolated Vinogradov wall (lap 95) -/
#print axioms NormalNumbers.ElliottArchBands.shortWindow_bounds
#print axioms NormalNumbers.ElliottArchBands.archimedeanCorrelationBoundAbove_of_bands
#print axioms NormalNumbers.ElliottArchBands.twoPointElliottLog_of_bands
#print axioms NormalNumbers.ElliottArchBands.archCorrLargeShift_of_moderate_and_nearMax
#print axioms NormalNumbers.ElliottArchBands.twoPointElliottLog_of_three_bands

/-! ### The damping step towards (c′-I)/(c′-II-a) (lap 97) -/
#print axioms NormalNumbers.ElliottDamped.sum_log_div_primesUpTo_le
#print axioms NormalNumbers.ElliottDamped.norm_archCorr_sub_dampedArchCorr_le
#print axioms NormalNumbers.ElliottDamped.dampedBlock_le
#print axioms NormalNumbers.ElliottDamped.dampedTail_le
#print axioms NormalNumbers.ElliottDamped.norm_archCorr_sub_dampedPrefix_le

/-! ### The calculus core and the reduction of the soft inputs (lap 99) -/
#print axioms NormalNumbers.ElliottLogIntegral.integral_le_one_add_log
#print axioms NormalNumbers.ElliottDamped.shiftedMertensSmall_of_dampedSeriesBound
#print axioms NormalNumbers.ElliottDamped.archCorrModerate_of_dampedSeriesBound
#print axioms NormalNumbers.ElliottLogIntegral.integral_rpow_neg_Ioi
#print axioms NormalNumbers.ElliottDamped.dampedPrefix_eq_integral
#print axioms NormalNumbers.ElliottDamped.norm_logWeightedSlice_le_decay

/-! ### The soft inputs reduced to a ζ'/ζ slice bound (lap 102) -/
#print axioms NormalNumbers.ElliottLogIntegral.integral_le_one_add_log_add_const
#print axioms NormalNumbers.ElliottDamped.norm_dampedPrefix_le_of_slice_le'
#print axioms NormalNumbers.ElliottDamped.dampedSeriesBoundSmall_of_sliceBound
#print axioms NormalNumbers.ElliottDamped.dampedSeriesBoundModerate_of_sliceBound

/-! ### The cutoff is free: the ζ'/ζ inputs are stated at a large cut (lap 103) -/
#print axioms NormalNumbers.ElliottDamped.norm_dampedPrefix_sub_le
#print axioms NormalNumbers.ElliottDamped.norm_dampedPrefix_transfer

/-! ### The log-weighted tail bricks (lap 104) -/
#print axioms NormalNumbers.ElliottDamped.sum_log_div_primesUpTo_ge
#print axioms NormalNumbers.ElliottDamped.sum_log_div_primesInInterval_le
#print axioms NormalNumbers.ElliottDamped.logBlock_le
#print axioms NormalNumbers.ElliottDamped.logTail_blocks

/-! ### The tail bound, closed (lap 105) -/
#print axioms NormalNumbers.ElliottDamped.sum_geom_shift_le
#print axioms NormalNumbers.ElliottDamped.sum_rpow_neg_two_pow_half_le
#print axioms NormalNumbers.ElliottDamped.logTail_term_le
#print axioms NormalNumbers.ElliottDamped.tailNumeric_le
#print axioms NormalNumbers.ElliottDamped.logTail_le

/-! ### Mertens I discharges the harmonic clause with sharp constant 1 (lap 106) -/
#print axioms NormalNumbers.ElliottDamped.integral_id_mul_exp_neg_Ioi
#print axioms NormalNumbers.ElliottDamped.sum_log_rpow_le
#print axioms NormalNumbers.ElliottDamped.norm_logWeightedSlice_le_trivial
#print axioms NormalNumbers.ElliottDamped.sliceBoundSmall_of_cap
#print axioms NormalNumbers.ElliottDamped.sliceBoundModerate_of_cap

/-! ### The pole-local ζ'/ζ bound, no zero-free region (lap 107) -/
#print axioms NormalNumbers.ElliottZetaPole.analyticAt_zetaG
#print axioms NormalNumbers.ElliottZetaPole.logDeriv_riemannZeta_eq
#print axioms NormalNumbers.ElliottZetaPole.exists_pole_local_bound
#print axioms NormalNumbers.ElliottZetaPole.exists_far_band_bound
#print axioms NormalNumbers.ElliottZetaPole.exists_subunit_logDeriv_bound

/-! ### The prime-power correction (lap 109) -/
#print axioms NormalNumbers.ElliottPrimePower.sum_log_mul_rpow_neg_two_le
#print axioms NormalNumbers.ElliottPrimePower.sum_half_pow_le
#print axioms NormalNumbers.ElliottPrimePower.sum_pairs_le

/-! ### The slice is a partial sum of L Λ (lap 110) -/
#print axioms NormalNumbers.ElliottBridge.conj_archimedeanTwist
#print axioms NormalNumbers.ElliottBridge.term_eq_slice_summand
#print axioms NormalNumbers.ElliottBridge.slice_eq_sum_term
