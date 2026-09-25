import NormalNumbers.ElliottGeneral
import NormalNumbers.ElliottHall
import NormalNumbers.ElliottRandomize

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

-- the dependency's proved special case
#print axioms Erdos67b.unitCircleLogElliott
