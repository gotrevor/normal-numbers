/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Barriers
import NormalNumbers.LiteratureDigitsOfPowers
import NormalNumbers.ErdosTriples
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
import NormalNumbers.ConjugateEntropy
import NormalNumbers.IndependenceRelative
import NormalNumbers.PrimeLambertOscillation
import NormalNumbers.SwingC3Rotation
import NormalNumbers.LinearFormsScales
import NormalNumbers.LogCastingOutStretch
import NormalNumbers.EntropyProfilesStretch
import NormalNumbers.FiniteStateSelectionStretch
import NormalNumbers.SchmidtGamesStretch
import NormalNumbers.CantorBadNormal
import NormalNumbers.CantorBadNormalRetired
import NormalNumbers.CantorExactExponentStretch
import NormalNumbers.StretchBFR
import NormalNumbers.CantorExactExponentProfile
import NormalNumbers.CantorRepetition
import NormalNumbers.QSpanCriterion
import NormalNumbers.ComputableReal
import NormalNumbers.KurtzRandom
import NormalNumbers.MahlerProductBlock

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
   "the statement is false at p = 71, so the argument must use p ≥ 73"⟩,
  ⟨``LinearFormsScales.furstenbergLogAvoid_holds,
   [``furstenberg_constAvoid_false, ``powersOfTwo_constAvoid],
   "the rate c / log q must tend to 0 (a constant rate is false by Furstenberg), and the \
    argument must use the independence of 2 and 3: for the dependent pair {2ᵏ} a constant rate \
    holds, so a lacunarity-only avoidance argument would prove the false constant rate for Σ"⟩,
  ⟨``LogCastingOut.simplyNormalLog_of_growingDepth, [``log_normal_not_simply_normal],
   "the log Weyl criterion yields log equidistribution only; the conclusion must stay on the log \
    rung, since a log-normal number need not be simply normal"⟩,
  ⟨``EntropyProfiles.ae_isNormal_self_base_sq_of_timesP_ergodic, [``cantor_not_normal_three_pow],
   "with x in place of (x + 1)² the claim is false (the Cantor measure is ×3-ergodic and no Cantor \
    point is 3-normal), so the mechanism must use the curvature of the map"⟩,
  ⟨``CantorBadNormal.midStages,
   [``cantor_not_normal_three_pow, ``perStage_dead_not_enough],
   "the cancellation must use 3 ∤ b (3ⁿp/q does not cancel for q | 3ᵏ) and the arithmetic of \
    the centres p/q (dyadic centres give e(2ⁿp/2ᵏ) = 1, and per-stage dead counts alone admit a \
    never 2-normal descent)"⟩,
  ⟨``CantorBadNormal.aliveOffMix_resLaw,
   [``cantor_not_normal_three_pow, ``perStage_dead_not_enough],
   "the same-cylinder obstacle pairs must cancel by the arithmetic of the centres p/q: for dyadic \
    centres every dead child sits on a binary zero run, so the excess phase is coherent (probe: \
    coherence 0.96); per-stage dead counts alone do not suffice.  Whether the b = 3 barrier \
    binds this node or only the Cantor main term is undecided.  Averaging over the obstacle \
    numerators gives only a constant saving on the preperiodic families \
    (PreperiodicNumeratorDispersion, believed false), so their decay must come from the middle \
    ternary digits of h b^m"⟩,
  ⟨``CantorBadNormal.fourierPairRate_descent_of_deadRateDecay,
   [``cantor_not_normal_three_pow, ``perStage_dead_not_enough],
   "the pair-averaged Cantor products must use 3 ∤ b, and the dead-stage hypothesis must be a \
    probability decay, not a per-stage dead count (counts alone admit a never 2-normal descent)"⟩,
  ⟨``QSpan.qSpanNormal_sqrt_two_sqrt_three, [``liouville_pair_qSpan],
   "the argument must use something √2, √3 have and the sparse Liouville pair lacks (algebraicity, \
    bounded partial quotients, …): a pair-universal argument would put a normal number in the \
    Liouville pair's span"⟩]

/-- Open `sorry`s that are not cruxes, and why no barrier applies. -/
def waivers : List Waiver := [
  ⟨``ErdosTriples.tripleTrivial_of_sum_le_160,
   "a finite computation: 12403 exact carry-automaton decisions (experiments/erdos-triples, \
    known-answer suite test_triple.py); discharge is a Lean automaton with a soundness lemma"⟩,
  ⟨``ErdosTriples.exceptionalSet_eq_zero_of_gapTriplesEventually,
   "wiring lemma (a leaf): the proved integer wiring erdos406_of_gapTriplesEventually lifted to \
    3-adic digits (parity, valuation shift, residues); English proof in the docstring"⟩,
  ⟨``IndependenceRelative.not_isRelativeBlock_small,
   "a finite computation stated as a sibling: the blocksearch probe's non-certification over \
    small direction sets; it closes a route, no open crux uses it"⟩,
  ⟨``IndependenceRelative.ternary_line,
   "a leaf: a borrow-propagation case split with a full English proof in the docstring; the \
    independence-relative probe agrees (witness 2X - Y)"⟩,
  ⟨``IndependenceRelative.exists_counterexample_on_line,
   "a sibling: X = sum 3^(-k!), Y = 2X shows the line obstruction is real; no open crux uses it"⟩,
  ⟨``ConjugateEntropy.fsDimUpper_le_of_sum_rat,
   "a leaf: the span_dimension_budget block-entropy argument with both terms upper (Fekete in ℓ); \
    B–D 2506.12929 Prop. 4.9(d) for point entropy, bridge to Dim_FS not formalized"⟩,
  ⟨``ConjugateEntropy.fsDim_le_of_sum_rat,
   "a leaf: the span_dimension_budget argument itself with a rational third term; B–D Prop. 4.9(b)"⟩,
  ⟨``ConjugateEntropy.exists_sum_zero_normal_half,
   "a sibling: the base-4 digit split showing the 1/2 in half_of_normal_of_sum_rat is sharp for \
    abstract triples; no open crux uses it"⟩,
  ⟨``Adder.IsProductBlock.liouville_cover,
   "a leaf: the B–B 1994 Thm 3.1 Liouville witness with 'digit d absent from m·B' in place of a \
    run of g−1 (orbit_liouvilleMul_lt's argument)"⟩,
  ⟨``Adder.isRung_five_two_three,
   "a finite computation: rung checker (carry automaton, label-filtered SCCs)"⟩,
  ⟨``Adder.not_isRung_five_four_five_small,
   "a finite computation: an avoided-digit-set assignment with a live SCC for each small T"⟩,
  ⟨``Adder.IsWordSetBlock.runs_liouville_cover,
   "a leaf: liouville_cover's argument for runs of ones"⟩,
  ⟨``Adder.not_isWordSetBlock_runs_three_small,
   "a finite computation: word-channel carry automaton (mahler_block among/runs)"⟩,
  ⟨``Adder.isWordSetBlock_runs_three_nine,
   "a finite computation: word-channel carry automaton (mahler_block among/runs)"⟩,
  ⟨``Adder.not_isWordSetBlock_extremeDigits,
   "a finite computation: word-channel carry automaton (mahler_block among/runs)"⟩,
  ⟨``Adder.isWordSetBlock_four_extreme,
   "a finite computation: word-channel carry automaton (mahler_block among/runs)"⟩,
  ⟨``Adder.IsWordBlock.liouville_cover,
   "a leaf: liouville_cover's argument with words for digits"⟩,
  ⟨``Adder.IsWordBlock.exists_ge,
   "a leaf: liouville_cover at B = 1 plus a window count on 0^k m 0^k"⟩,
  ⟨``Adder.isWordBlock_two_three_thirteen,
   "a finite computation: word-channel carry automaton collapse"⟩,
  ⟨``Adder.isWordBlock_two_two_one_three_five,
   "a finite computation: word-channel carry automaton collapse"⟩,
  ⟨``Adder.not_isWordBlock_two_two_pair,
   "a finite computation: a non-collapsing word-channel SCC for each pair"⟩,
  ⟨``Adder.not_isProductBlock_five_twelve_erase,
   "a finite computation: 12 non-collapsing carry-automaton core cycles, each an irrational witness"⟩,
  ⟨``Adder.isProductBlock_five_twelve,
   "a finite computation: carry-automaton collapse certificates, needs a sparse checker"⟩,
  ⟨``Adder.isProductBlock_five_thirteen,
   "a finite computation: carry-automaton collapse certificates, needs a sparse checker"⟩,
  ⟨``Adder.isProductBlock_five_fourteen,
   "a finite computation: carry-automaton collapse certificates, needs a sparse checker"⟩,
  ⟨``Adder.isProductBlock_five_fifteen,
   "a finite computation: carry-automaton collapse certificates, needs a sparse checker"⟩,
  ⟨``Adder.isProductBlock_five_seventeen,
   "a finite computation: carry-automaton collapse certificates, needs a sparse checker"⟩,
  ⟨``Adder.IsProductBlock.base5_card_ge_five,
   "a finite computation: liouville_cover over B ≤ 300 plus an exact set cover (ILP optimum 5)"⟩,
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
  ⟨``ComputableReal.not_isKurtzRandom_of_isComputableReal,
   "known theorem (Kurtz 1981: computable ⇒ not Kurtz random); Primrec bookkeeping, no new mechanism"⟩,
  ⟨``ExplicitSquare.ae_isNormal_of_logDecay,
   "known theorem (Davenport–Erdős–LeVeque) transcribed; no new mechanism"⟩,
  ⟨``ExplicitSquare.oneFreqZero_sparseReal_squares, "a leaf of the squares construction"⟩,
  ⟨``ExplicitSquare.sparseReal_pos, "a leaf of the squares construction"⟩,
  ⟨``Deterministic.quadraticLogWitness_of_cor14, "wiring from cited Manai 2026 Cor 1.4"⟩,
  ⟨``LogCastingOut.omegaModDigit_logTwoWord_of_zetaExponent,
   "corollary of Tao 2016 log Elliott (proved in the repo) plus the ledger's zeta input, for the \
    carry-free sibling of G4_b; low novelty, English proof in the docstring"⟩,
  ⟨``EntropyProfiles.exists_strictMono_biLipschitz_cantorSet_not_isNormal_two,
   "construction lemma (known embedding, Mattila–Saaranen 2009 / Deng–Wen–Xiong–Xi 2011); a \
    sharpness guard for HochmanShmerkinCantorDiff1, not a new mechanism"⟩,
  ⟨``EntropyProfiles.exists_strictMono_biLipschitz_cantorSet_absAbnormal,
   "construction: the headline's tree embedding with scale-dependent digit targets; extends the \
    sharpness guard, no new mechanism"⟩,
  ⟨``FiniteState.isNormal_cpSeq,
   "believed literature-strength leaf: Champernowne counting (Becher–Carton 2018 Thm 7.7.1); \
    Carton–Perifel is cited for k ≥ 7 (Literature.cartonPerifel_normal), needed for k ≤ 6"⟩,
  ⟨``FiniteState.not_isNormal_of_zeroFreqHalf,
   "a leaf: zero-frequency 1/2 ≠ 1/k contradicts simple normality"⟩,
  ⟨``FiniteState.k_dvd_scaled_delayEnum, "a leaf: arithmetic of the one-letter delay relabeling"⟩,
  ⟨``FiniteState.not_kAdicEquidist_delayEnum,
   "a leaf: residue 1 mod k is never hit, from k_dvd_scaled_delayEnum"⟩,
  ⟨``Literature.DigitsOfPowers.persistence_bounded_of_smoothDigitOmission,
   "wiring lemma (a leaf): digit-product arithmetic from the open node SmoothDigitOmission; \
    English proof in the docstring"⟩,
  ⟨``QSpan.exists_pair_exponentTwo_qSpan_not_normal,
   "a sibling, stated for the Maze row on Diophantine inputs (registered as a Maze witness, not a \
    barrier: it refutes a route, no open crux uses it); proof from span_dimension_budget plus \
    Bénard–He–Zhang"⟩,
  ⟨``QSpan.span_dimension_budget,
   "a leaf: block-entropy subadditivity through bounded carries, plus the block-entropy \
    characterization of dim_FS/Dim_FS (BHV 2005); possibly literature-adjacent (Doty–Lutz–Nandakumar \
    2007 treat one number and rational arithmetic)"⟩,
  ⟨``StretchBFR.windowCount_of_inverseSum,
   "conditional wiring (Fourier expansion over the q-interval); records that single-sum \
    cancellation reaches only m > b − δ b' (singleSum_insufficient)"⟩,
  ⟨``StretchBFR.card_near_cantor_le, "a leaf: the classical covering count of rationals near K"⟩,
  ⟨``CantorExactExponentProfile.ae_isNormal_of_profileOK,
   "open node; the elementary orbit port is blocked in the run shadow (Maze row 'elementary orbit \
    port to 3 | b'); live route via the Baker discrepancy input"⟩,
  ⟨``CantorExactExponentProfile.exists_computable_mem_cantorSet_irrExponent_normalProfile,
   "the unconditional form of exists_computable_normalProfile_of_baker (proved); open only for \
    the cited Baker–Wüstholz + Erdős–Turán input Literature.BakerLogDiscrepancyEff"⟩,
  ⟨``CantorExactExponentProfile.ae_isNormal_of_profileOK_of_gelfond,
   "believed implication (55%): a Gelfond-strength two-log bound suffices for the run shadows; \
    the elementary t^k ≠ 3^j rate does not"⟩,
  ⟨``CantorRepetition.runOrbitDecay_of_sparse,
   "a counting leaf of the sparse-pair route (2026-10-07): cyclic_pair_identity (proved) plus \
    SparseIdentityBound give clusters, card_cluster_le counts them; English proof in the docstring"⟩,
  ⟨``CantorRepetition.card_degRows_le,
   "a leaf: lifting the exponent bounds gcd(3^A − 1, t^∞); degenerate shifts are multiples of an \
    order ≥ A/(2 log₃ b)"⟩,
  ⟨``CantorRepetition.copyRun_psi,
   "a leaf: pair_sum_le rows, RunOrbitDecay on non-degenerate rows, card_degRows_le on the rest"⟩,
  ⟨``CantorRepetition.repPairArith_of_runDecay,
   "wiring: repPairPos_explicit with the copy term from copyRun_psi; summability along sched by a \
    sum swap"⟩,
  ⟨``CantorRepetition.repPairArith_of_three_dvd,
   "open crux of liouvilleCantorFullProfile: repPairArith_of_literature applied to cited Baker \
    (two logs) and Matveev (three logs), which enter only as hypothesis Props; the conditional \
    liouvilleCantorFullProfile_of_literature carries them honestly"⟩,
  ⟨``FiniteState.isFNormal_delayEnum_of_normal,
   "a leaf: O(1) cost of composing with the delay transducer and its finite-state right inverse"⟩]

#barrier_audit allBarriers, cruxLinks, waivers

end NormalNumbers.Barriers
