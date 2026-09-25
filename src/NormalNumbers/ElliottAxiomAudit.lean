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
import NormalNumbers.ElliottRestricted

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

-- leaf 2, the assembly (gap-free itself; the three halves below carry sorryAx)
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
#print axioms NormalNumbers.ElliottLeafTwo.exists_squarefull_tail

-- the dependency's proved special case
#print axioms Erdos67b.unitCircleLogElliott
