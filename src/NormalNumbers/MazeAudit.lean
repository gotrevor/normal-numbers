/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Maze
import NormalNumbers.CPrimeSiteFactorization
import LeanLedger.MazeLinks
import NormalNumbers.MasterMaze
import NormalNumbers.LogCastingOutStretch
import NormalNumbers.PairDecoupleProve
import NormalNumbers.StonehamBase6
import NormalNumbers.LinearFormsScalesStretch
import NormalNumbers.EntropyProfiles
import NormalNumbers.CantorExactExponentStretch
import NormalNumbers.QSpanNormal
import NormalNumbers.Barriers

/-!
# Maze audit: every closed route cites declarations

`#maze_audit` (shared, `lean-agent-skills/lean`) fails the build unless every `register` row
outside `mazeLegacy` has a `Link` to the declarations its verdict rests on.  Names are
``` ``Foo.bar ``` literals, so a missing or renamed declaration breaks the build.

* **New rows** need a link.  A `wall` row dated `2026-10-01` or later must also name its reopen
  condition as a `def … : Prop`.  Older walls are grandfathered for that one requirement.
* **`mazeLegacy`** holds rows whose reasons are still prose only, as of 2026-10-01.  It only
  shrinks.  When a legacy row gains a link, the audit demands its deletion from this list.
  Converting a legacy row means stating its obstruction in Lean, which is real work: the Lean
  form of each row's mechanism sentence.
-/

namespace NormalNumbers.Maze

open LeanLedger
open NormalNumbers.PrimeModel.SiteFactor

/-- The audit's view of the register. -/
def mazeRows : List RowInfo :=
  register.map fun h => ⟨h.name, decide (h.verdict = Verdict.wall) && decide ("2026-10-01" ≤ h.date)⟩

/-- Each linked row and the declarations it rests on. -/
def mazeLinks : List Link := [
  ⟨"pair-universal mechanism for a normal element of a Q-span",
   [``QSpan.exists_pair_qSpan_not_normal, ``QSpan.qSpanNormal_sqrt_two_sqrt_three,
    ``Barriers.liouville_pair_qSpan], []⟩,
  ⟨"Diophantine (exponent-2) input for a normal element of a Q-span",
   [``QSpan.exists_pair_exponentTwo_qSpan_not_normal, ``QSpan.span_dimension_budget,
    ``QSpan.qSpanNormal_sqrt_upperDim], []⟩,
  ⟨"He-Liao local count on the forced-run measure",
   [``CantorExactExponentStretch.endpoint_sep, ``CantorExactExponentStretch.thickening_cost_ge_one,
    ``CantorExactExponentStretch.Literature.HeLiao2026Cor65,
    ``CantorExactExponent.bcTerm_red_mu_three],
   [``CantorExactExponentStretch.EndpointRationalCount]⟩,
  ⟨"log-averaged casting-out via the Elliott ledger",
   [``hall_logavg_casting_out, ``LogCastingOut.TaoTeravainen2019FixedDepth,
    ``CastingOut.carry_correction_unbounded, ``CastingOut.castLawLog_one_iff,
    ``CastingOut.multiElliott_all, ``LogCastingOut.simplyNormalLog_of_growingDepth],
   [``LogCastingOut.GrowingDepthLogElliott]⟩,
  ⟨"log-averaged word frequencies of an unconstructed constant as new",
   [``hall_log_rung_distinct, ``LogCastingOut.tendsto_logFreq_dyadicBit,
    ``LogCastingOut.TaoTeravainen2019LiouvilleThree], []⟩,
  ⟨"linear forms in logarithms as the avoidance input",
   [``LinearFormsScales.band_unique_u, ``LinearFormsScales.gap_of_scaleSeparation,
    ``LinearFormsScales.not_scaleSeparation_two_four, ``LinearFormsScales.Literature.BakerScaleSeparation],
   []⟩,
  ⟨"Stoneham profile beyond the Bailey-Borwein region",
   [``Failures.not_isNormal_six_stoneham23, ``stoneham_base6_readout,
    ``LinearFormsScales.StonehamBase3Normal, ``LinearFormsScales.StonehamBase18Normal],
   [``LinearFormsScales.ShortPowerOrbitEquidist]⟩,
  ⟨"log-rate avoidance along Furstenberg's semigroup",
   [``LinearFormsScales.furstenbergLogAvoid_holds, ``LinearFormsScales.moshchevitinPeresSchlag_of_logAvoid,
    ``LinearFormsScales.badziahinHarrap_of_logAvoid, ``LinearFormsScales.not_constAvoid_of_furstenberg,
    ``LinearFormsScales.constAvoid_powersOfTwo],
   [``LinearFormsScales.FurstenbergLogAvoid]⟩,
  ⟨"bi-Lipschitz stability of Hochman-Shmerkin as new",
   [``EntropyProfiles.exists_strictMono_biLipschitz_cantorSet_not_isNormal_two,
    ``EntropyProfiles.not_biLipschitz_stable, ``EntropyProfiles.HochmanShmerkinCantorDiff1], []⟩,
  ⟨"CRT freezing for density of the binary words of E",
   [``EDensity.eCount_power, ``JointLambert.jointWords_quantitative, ``EDensity.RungPolylog,
    ``EDensity.RungRich], [``EDensity.ResidualSmallPolylog]⟩,
  ⟨"free 2-adic kill plus forced band for E",
   [``EDensity.two_pow_oddExpCount_dvd_card_divisors,
    ``EDensity.fract_card_divisors_div_two_pow_eq_zero, ``EDensity.card_odd_card_divisors_le,
    ``Erdos257Squarefree.SqfreeBinaryDisjunctive],
   [``EDensity.ResidualSmallOften, ``EDensity.ResidualSmallPolylog]⟩,
  ⟨"Erdős #257 for squarefree / k-free A via the Chowla-Erdős kill",
   [``Erdos257Squarefree.DuverneyTachiya2019KFree, ``Erdos257Squarefree.erdos257_squarefree_of_literature,
    ``Erdos257Squarefree.erdos257_kFree_of_literature], []⟩,
  ⟨"squarefree #257 single-survivor encoding at base 2",
   [``hall_sqfree_single_survivor, ``Erdos257Squarefree.fract_two_pow_div_two_pow],
   [``Erdos257Squarefree.SqfreeBinaryDisjunctive]⟩,
  ⟨"Erdős #257 gap sets via an S-restricted moment cap alone",
   [``G4.SchedB.hypE_frame_excludes_logRate], [``G4.SchedB.SRestrictedFrame]⟩,
  ⟨"site factorization via log-power BV",
   [``card_siteAssignments, ``siteFactorization_of], [``DepthUniformMultBV]⟩,
  ⟨"old Good.sep", [``hall_good_sep], []⟩,
  ⟨"T_E sample-entropy transfer", [``hall_T_E], []⟩,
  ⟨"E-T8 chunking", [``hall_chunking], []⟩,
  ⟨"certified-granule assembly", [``hall_granularity_wall], []⟩,
  ⟨"pointwise frequency from deficit", [``hall_pointwise_deficit], []⟩,
  ⟨"axis-skeleton sharpening", [``hall_axis_skeleton], []⟩,
  ⟨"normality on the quantized sampler", [``hall_quantized_normality], []⟩,
  ⟨"base two, §4D design family", [``hall_base_two_design], []⟩,
  ⟨"psi-pushed Chebyshev variance", [``hall_psi_pushed_variance], []⟩,
  ⟨"Mahler block-occurrence analogue", [``hall_mahler_block_occurrence], []⟩,
  ⟨"T3c critical-slice run cap", [``hall_t3c_block5_true_run_is_one], []⟩,
  ⟨"alpha_{2,3} abelian-normal in base 6", [``hall_stoneham_six_abelian], []⟩,
  ⟨"TT (3.3) as TTNonPretentious", [``hall_tt_nonpretentious_vacuous], []⟩,
  ⟨"K-point no-exceptional-set input as stated", [``hall_kpoint_noexc_false], []⟩,
  ⟨"the named open problem TwoPointNaturalCorrelationNoExc", [``hall_two_point_noexc_false], []⟩,
  ⟨"Lebesgue-measured exceptional set of scales", [``hall_lebesgue_exceptional_scales], []⟩,
  ⟨"TT 3.1(i) with a Lebesgue-measured exceptional set", [``hall_tt_equidistributed_vacuous], []⟩,
  ⟨"uniform casting-out law (C1 draft)", [``hall_uniform_casting_out], []⟩,
  ⟨"Moshchevitin-Shkredov hot-spot criterion for continued fractions", [``hall_moshchevitin_shkredov_cf_false], []⟩,
  ⟨"low/high split for UniformResonantMass", [``hall_urm_low_high_split], []⟩,
  ⟨"min-rule descent of Vandehey 2017 Lemma 2.1", [``hall_vandehey_lemma21_min_rule], []⟩,
  ⟨"synchronizing word for the CF det-D transducer", [``hall_vandehey_synchronizing_transducer], []⟩,
  ⟨"emitted digit as a window function of the input", [``hall_emit_digit_window_function], []⟩,
  ⟨"Hecke approximation of phi by Fibonacci ratios", [``hall_hecke_approximation], []⟩,
  ⟨"BlockForget repaired to CF-normal inputs", [``hall_blockforget_cfnormal], []⟩,
  ⟨"BlockForget in the uniform-z form", [``hall_blockforget_uniform_z], []⟩,
  ⟨"the block-forgetting crux as a reduction of Vandehey S7 Problem 1", [``hall_blockforget_is_restatement, ``hall_blockforget_implies_goal], []⟩,
  ⟨"the TransducerData bundle as the S7 front", [``hall_transducerdata_vacuous], []⟩,
  ⟨"the StateData repair of the bundle", [``hall_statedata_restatement], []⟩,
  ⟨"StateClock below the width scale", [``hall_stateclock_below_width], []⟩,
  ⟨"the one-digit-per-read throttle behind the S7 scalar debts", [``hall_one_digit_throttle], []⟩,
  ⟨"predictable target sets from marginals alone", [``hall_predictable_from_marginals], []⟩,
  ⟨"Hypothesis A as weaker",
   [``NormalNumbers.MasterConjectures.equidistributed_lnTwoOrbit_iff], []⟩,
  ⟨"KickBootstrap", [``NormalNumbers.MasterConjectures.equidistributed_lnTwoOrbit_iff],
   [``NormalNumbers.MasterConjectures.BaileyCrandallHypA]⟩]

/-- Rows whose reasons are still prose only (as of 2026-10-01).  Only shrinks. -/
def mazeLegacy : List String := [
  "(BL) bias-loss criterion",
  "per-band contraction",
  "late-band regeneration as feedback",
  "OneSiteRatioBounded (CRT form)",
  "signed sum (7)",
  "absolute propagated budget B",
  "free-count sparse constructions",
  "elementary Mertens / Brun-Titchmarsh",
  "any digit-local sample premise",
  "averaging repair over families",
  "scale-gap repairs (four)",
  "tower-separation wall (REVERSED)",
  "delta_K asymptotic sharpening",
  "Mprod / primorial for a P0 bound",
  "base-2^k step 3 read-class split",
  "Wall + Maxfield for base 2^k",
  "coprimality sharpening",
  "counting-based rate sharpening",
  "counting bound below w = 8E+5",
  "grouped sampling escape",
  "phaseOscillation / base-two irrationality",
  "B6 two-stream cylinder nesting",
  "navigate-then-select",
  "cfK-control as the fix",
  "digit-capped steering",
  "conditional-at-wz z-route",
  "post-hoc deep-cylinder witness",
  "target-shrink inside the hull",
  "L4 self-hull steer",
  "SchedABlockLinear",
  "hdom dominance (RE-OPENED)",
  "goodC suffices (Khinchin)",
  "naive Khinchin assembly",
  "Khinchin from frequencies alone",
  "Fermat-quotient coordinate",
  "e kick-barrier",
  "T3 ShortOrbitCancel",
  "CRT stacking to a sqrt(n) threshold",
  "LnTwoLatticeAvoid (alien R1)",
  "SliverEscape is Diophantine-free",
  "Lagarias footnote-1",
  "beta below 9 (run cap)",
  "beta = 8 sharpening",
  "kick-floor-only lemma",
  "irrationality-measure route",
  "2-adic Kurschak trick",
  "(mu-1)n run corollary as novel",
  "first quantitative digit statement",
  "Bugeaud-Kim complexity from mu",
  "abc path A (non-Wieferich)",
  "abc path B (S-unit)",
  "unrestricted-word adder collapse",
  "factory to a single constant",
  "universal clauses to disjunctivity",
  "universality-preserving methods",
  "C1 two-elements-per-digit",
  "C4 / C5 / C8 as independent",
  "C2 one-multiplier-all-digits",
  "float-prefilter negatives",
  "automaton no-k-set lower bounds",
  "decimal digit-7 wall",
  "restricted-class middle rung",
  "divisor-bound conjecture",
  "prime-base upper side",
  "universal constant below 1",
  "constant-is-sharp as new",
  "orbit-free Mahler cycles",
  "multi-offset single background",
  "closed-form background at b = 2",
  "drift minus one",
  "structural D dividing p+1",
  "closed-form burst families",
  "quarter target at k >= 2",
  "no new idea required at k >= 2",
  "exists_prime_nonresidue",
  "measure-theoretic non-disjunctive witness",
  "Furstenberg-intersection route",
  "Martin abnormal number as witness",
  "Axiom Lambda as weaker",
  "carry-free attacks on Axiom C",
  "dimension bounds imply Axiom M",
  "pattern-side repetition threshold",
  "single-tail radix extraction",
  "hexagon positivity / mean retention",
  "single-coordinate carry isolator",
  "oscillation implies disjunctivity",
  "second Katai differencing",
  "typical-set shortcut",
  "Omega-transfer by sparse edits",
  "full prime-incidence independence",
  "density-only coefficient transfer",
  "fixed-window conductor at depth",
  "periodic search for the prime cube",
  "Gowers positivity from the relations",
  "phi-product density recurrence",
  "sparse Stoneham relative as open",
  "Stoneham base-6 as a new method",
  "Hertling direct substitution",
  "Vandehey Lemma 3.2",
  "Fisher-Schmidt as the solution",
  "BBP extraction for pi normality",
  "finite C2 implies slow growth",
  "G4 sectors as digit characters",
  "x3 abelian lifting",
  "bounded-error decomposition of the image count",
  "Diophantine good-denominator detour for the tail cell",
  "route B's unweighted cover of the state-dependent target"]

/-- info: maze audit: 156 rows, 49 cite declarations, 107 legacy (prose only) -/
#guard_msgs in
#maze_audit mazeRows, mazeLinks, mazeLegacy

end NormalNumbers.Maze
