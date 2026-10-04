/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Barriers
import NormalNumbers.PairDecoupleProve
import NormalNumbers.PairDecoupleRefute
import NormalNumbers.SwingC1Log
import NormalNumbers.SwingC1
import NormalNumbers.SwingC2
import NormalNumbers.SwingC3Leaf
import NormalNumbers.TwoPointBet
import NormalNumbers.ExplicitSquareNonNormal
import NormalNumbers.GrowingLocalizedLogDiagonal
import NormalNumbers.Hertling
import NormalNumbers.CPrimeSiteFactorization
import NormalNumbers.JointLambertAGPRange
import NormalNumbers.Erdos257AllPrimes
import NormalNumbers.MahlerDriftOne
import NormalNumbers.LevinSparse
import NormalNumbers.DeterministicBD
import NormalNumbers.PrimeLambertOscillation
import NormalNumbers.SwingC3Rotation

/-!
# Barrier audit: every open crux names a sibling it must fail on

`#barrier_audit` (`Barriers/Core.lean`) fails the build unless every declaration of the default
target with a direct `sorry` is one of:

* a **crux** in `cruxLinks`, naming at least one registered barrier (`Barriers.lean`) and saying
  how its mechanism must use something the sibling lacks;
* a **waiver** in `waivers`, with the reason no barrier applies (a leaf lemma, a
  literature-strength analytic input, a wiring step, a refutation bet), or the candidate sibling
  that is not yet in Lean;
* the declaration of a `frozen` barrier.

It also checks every barrier's tier against `collectAxioms`.

The run below sees only what this file imports, as a quick local check.  The authoritative run
is the last command of the root file `src/NormalNumbers.lean`, which imports every module, so a
`sorry` in a module not imported here still fails the default build.  Link it here, importing
its module.

**A new `sorry` in the build fails this file** until it is linked or waived.  A crux or waiver
whose `sorry` disappears fails it too, so both lists track the open frontier.  Converting a
waiver into a crux means stating its sibling in Lean (`Barriers/Siblings.lean`).
-/

namespace NormalNumbers.Barriers

/-- Each frozen headline `sorry` and the barriers its mechanism must fail on. -/
def cruxLinks : List CruxLink := [
  ⟨``LevinSparse.exists_absNormal_base2_fast,
   [``stoneham_two_not_six, ``cantorLiouville_three_dvd],
   "base-2 discrepancy o(N^{-1/2}) does not reach bases 2^a·m: stoneham23 is base-2 normal and \
    fails base 6, so the Schmidt-type transfer must use something stoneham23 lacks"⟩,
  ⟨``Hertling.blockForcing, [``richExactly_two_impossible],
   "the forcing must use DepClosed R: without it, it would build a real rich exactly in {2}"⟩,
  ⟨``CastingOut.conjC1Log, [``log_normal_not_simply_normal, ``order_k_normal_not_normal],
   "a log-averaged law must not yield natural frequencies, and fixed-L laws must not be read as \
    normality"⟩,
  ⟨``CastingOut.castLawLog_one, [``log_normal_not_simply_normal],
   "log-simple normality of G4_b is strictly weaker than simple normality; the proof must stay \
    on the log rung"⟩,
  ⟨``CastingOut.hDepthAll, [``castUniform_false, ``tt_noExc_constOne],
   "window correlations of ω must use non-pretentiousness (fails for g = 1) and must not imply \
    the uniform casting-out law, which every normal number violates"⟩,
  ⟨``CastingOut.hAutoCorrAll, [``castUniform_false, ``tt_noExc_constOne],
   "the lag-L autocorrelation must come out b^{-L}, not uniform, and must use the nontrivial \
    character j"⟩,
  ⟨``CastingOut.multiElliott_all, [``tt_noExc_constOne],
   "Elliott-type cancellation must use that the twists are non-pretentious"⟩,
  ⟨``CastingOut.twoPointWeightedAvg_all, [``tt_noExc_constOne],
   "the averaged two-point bound must use m ≢ 0 mod b (the twist is non-pretentious)"⟩,
  ⟨``PrimeLambert.phaseOscillation, [``fermat_lambert_rational],
   "phase oscillation must use the prime index set: the doubling-set Lambert series is rational"⟩,
  ⟨``Erdos257.erdos257_allPrimes,
   [``hypE_logRate, ``squarefree_powTwo_encoding, ``fermat_lambert_rational],
   "gap sets need a frame other than HypE, single-survivor encodings fail at base 2, and the \
    argument must use primality or unit weights (a weighted doubling-set series is rational)"⟩,
  ⟨``GrowingLocalizedLog.exists_unbounded_of_constant, [``normal_prefix_limit],
   "the diagonal must control Weyl means on the windows between stages, not only prefixes"⟩,
  ⟨``ExplicitSquare.inv_logDecay_squares, [``sparse_logDecay_wall, ``sparse_polyDecay_wall],
   "squares give ~√n free digits, above Barrier 2's log n; power decay is impossible (Barrier 1), \
    so the proof must land on a logarithmic rate"⟩,
  ⟨``Adder.Background.exists_prime_nonresidue, [``driftOne_fails_at_71],
   "the statement is false at p = 71, so the argument must use p ≥ 73"⟩]

/-- Open `sorry`s that are not cruxes, and why no barrier applies. -/
def waivers : List Waiver := [
  ⟨``CastingOut.not_pairDecouple_all,
   "refutation bet against the C1 swing's input; if proved it becomes a barrier itself"⟩,
  ⟨``CastingOut.weylLambertTwist_holds,
   "no sibling in Lean yet; candidate: a Lambert constant over primes in a progression mod Q, \
    whose ×b orbit correlates with a character mod Q"⟩,
  ⟨``CastingOut.tailLargeDecouple_holds,
   "sieve decoupling (fundamental lemma plus level of distribution), no digit mechanism"⟩,
  ⟨``SwingC2.shiftedDivisorIncidence_holds,
   "analytic input: Brun–Titchmarsh plus a Linnik-type lower bound"⟩,
  ⟨``SwingC2.constructionInputs_even, "off the headline path (quadratic-residue layer)"⟩,
  ⟨``JointLambert.exceptionalModulus_gt_log, "analytic input: exceptional (Siegel) zeros"⟩,
  ⟨``JointLambert.agpExpRange_holds, "analytic input, blocked on exceptionalModulus_gt_log"⟩,
  ⟨``PrimeModel.SiteFactor.twistedSiegelWalfisz,
   "literature-strength analytic input (Selberg–Delange with characters)"⟩,
  ⟨``PrimeModel.SiteFactor.multBVResidue_of, "wiring from cited Bombieri–Vinogradov inputs"⟩,
  ⟨``PrimeModel.SiteFactor.card_siteAssignments, "combinatorial identity (a leaf)"⟩,
  ⟨``PrimeModel.SiteFactor.siteFactorization_of,
   "walled route, recorded in Maze (site factorization via log-power BV)"⟩,
  ⟨``PrimeModel.SiteFactor.siteFactorization_of_depthUniform,
   "C′-quantitative chain; candidate sibling: all primes (ρ = log 2), where the bound must go \
    trivial (HEADLINES H1), not yet a Lean statement"⟩,
  ⟨``PrimeModel.SiteFactor.pairSecondOrder_of,
   "C′-quantitative chain; same candidate sibling (ρ = log 2) as siteFactorization_of_depthUniform"⟩,
  ⟨``PrimeModel.SiteFactor.cprimeResidueQuad_of,
   "C′-quantitative assembly; same candidate sibling (ρ = log 2), not yet a Lean statement"⟩,
  ⟨``Erdos257.towerGapPrimes_gapSet, "Mertens with error term per block (a leaf)"⟩,
  ⟨``Erdos257.squareBlockPrimes_weakRate, "Mertens with error term per block (a leaf)"⟩,
  ⟨``Erdos257.squareBlockPrimes_not_mertensRate, "Mertens with error term per block (a leaf)"⟩,
  ⟨``ExplicitSquare.ae_isNormal_of_logDecay,
   "known theorem (Davenport–Erdős–LeVeque) transcribed; no new mechanism"⟩,
  ⟨``ExplicitSquare.oneFreqZero_sparseReal_squares, "a leaf of the squares construction"⟩,
  ⟨``ExplicitSquare.sparseReal_pos, "a leaf of the squares construction"⟩,
  ⟨``Deterministic.quadraticLogWitness_of_cor14, "wiring from cited Manai 2026 Cor 1.4"⟩]

#barrier_audit allBarriers, cruxLinks, waivers

end NormalNumbers.Barriers
