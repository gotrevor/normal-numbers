/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Barriers.Core
import NormalNumbers.Barriers.Siblings
import NormalNumbers.Stoneham
import NormalNumbers.StonehamBoundary
import NormalNumbers.StonehamSixFailure
import NormalNumbers.CantorLiouvilleAll
import NormalNumbers.UniformBad
import NormalNumbers.ExplicitPQ
import NormalNumbers.ExplicitSquareNonNormal
import NormalNumbers.Hertling
import NormalNumbers.DeterministicBD
import NormalNumbers.G4EntropyBarrier
import NormalNumbers.G4Base2GapObstruction
import NormalNumbers.CastingOut
import NormalNumbers.C3MrtTTDefect
import NormalNumbers.VandeheyS7QuadDigit
import NormalNumbers.EDensityAudit
import NormalNumbers.Erdos257Squarefree
import NormalNumbers.LinearFormsScales
import NormalNumbers.EntropyProfiles
import NormalNumbers.SchmidtGames
import NormalNumbers.CantorExactExponent
import NormalNumbers.QSpanNormal

/-!
# Barrier library: the registry

One definition per known-false sibling.  Each carries its statement, evidence of that statement
(so the elaborator checks the cited theorem proves exactly the claim), the declarations that
carry the evidence, and the mechanism shape it refutes.  `allBarriers` lists them for
`#barrier_audit` (`BarrierAudit.lean`), which links each frozen crux to at least one.

**Adding a barrier.**  State the sibling in Lean first: a theorem (`Barrier.proved`), a
derivation from a cited `Literature` Prop (`Barrier.cited`), or a frozen `sorry` statement with a
confidence and an English construction (`Barrier.frozen`, new ones in `Barriers/Siblings.lean`).
Then add a definition here and its name to `allBarriers`.  The tier is checked: `proved` and
`cited` evidence must be `sorryAx`-free, and a `frozen` barrier that gets proved must be promoted.
-/

namespace NormalNumbers.Barriers

open NormalNumbers.Literature.BergelsonDownarowicz

/-! ## Base transfer -/

/-- Stoneham's `α_{2,3} = Σ 1/(3^k 2^{3^k})`. -/
def stoneham_two_not_six : Barrier :=
  .proved "Stoneham α_{2,3}: normal in base 2, not normal in base 6"
    (And.intro isNormal_two_stoneham23 Failures.not_isNormal_six_stoneham23)
    [``isNormal_two_stoneham23, ``Failures.not_isNormal_six_stoneham23]
    "base-2 statistics (frequencies, discrepancy) transferring to another base"

/-- Cantor–Liouville points never normal to a base divisible by 3. -/
def cantorLiouville_three_dvd : Barrier :=
  .proved "Cantor–Liouville points: never normal to a base divisible by 3"
    @CantorLiouvilleAll.not_isNormal_of_three_dvd
    [``CantorLiouvilleAll.not_isNormal_of_three_dvd]
    "constructions or a.e. arguments that ignore the base's arithmetic relation to the seed base"

/-- Cassels–Schmidt: the Cantor measure makes a.e. point normal to bases not powers of 3. -/
def cassels_cantor_ae_normal : Barrier :=
  .cited "Cassels 1959: Cantor-measure-a.e. point normal to every base not a power of 3"
    CantorLiouvilleAll.Literature.Cassels1959 id
    [``CantorLiouvilleAll.Literature.Cassels1959]
    "claims that a measure on a base-3 Cantor set cannot charge normal numbers in other bases"

/-! ## Rungs of the ladder are distinct -/

/-- Stoneham in base 6: disjunctive, not normal. -/
def stoneham_six_disjunctive_not_normal : Barrier :=
  .proved "Stoneham α_{2,3} in base 6: disjunctive, not normal"
    (And.intro isDisjunctive_six_stoneham23 Failures.not_isNormal_six_stoneham23)
    [``isDisjunctive_six_stoneham23, ``Failures.not_isNormal_six_stoneham23]
    "upgrading disjunctive (rich, every word occurs) to normal for an explicit constant"

/-- Hertling's construction: disjunctive in every base, normal in none. -/
def rich_not_normal_everywhere : Barrier :=
  .proved "a real disjunctive in every base and normal in none"
    Hertling.exists_rich_and_not_normal_everywhere
    [``Hertling.exists_rich_and_not_normal_everywhere]
    "occurrence (positive count) arguments read as frequency arguments"

/-- Irrational and disjunctive in no base. -/
def irrational_not_disjunctive : Barrier :=
  .proved "an irrational number disjunctive in no base"
    UniformBad.exists_irrational_not_isDisjunctive
    [``UniformBad.exists_irrational_not_isDisjunctive]
    "irrationality or irrationality-measure input promoted to digit occurrence"

/-- Sibling (a): order-`k` statistics. -/
def order_k_normal_not_normal : Barrier :=
  .proved "a rational with correct frequencies for all words of length ≤ k (de Bruijn period)"
    Siblings.exists_rat_isNormalUpTo_not_isNormal
    [``Siblings.exists_rat_isNormalUpTo_not_isNormal]
    "mechanisms that verify finitely many orders (fixed L or word length), then conclude normality"

/-- Sibling (b): log rung versus natural rung. -/
def log_normal_not_simply_normal : Barrier :=
  .proved "a number normal under logarithmic averaging, not simply normal"
    Siblings.exists_isLogNormal_not_isSimplyNormal
    [``Siblings.exists_isLogNormal_not_isSimplyNormal]
    "log-averaged inputs (log-Elliott, log-Chowla) yielding natural-average digit frequencies"

/-! ## Correlation, sampling and decay -/

/-- The constant function `1` refutes the no-exceptional-set two-point correlation claim. -/
def tt_noExc_constOne : Barrier :=
  .proved "the constant function 1 against the no-exceptional-set two-point correlation"
    CastingOut.not_twoPointNaturalCorrelationNoExc
    [``CastingOut.not_twoPointNaturalCorrelationNoExc]
    "correlation bounds stated for all multiplicative g without a non-pretentiousness hypothesis"

/-- The first draft of C1 (uniform casting-out law) fails for every normal number. -/
def castUniform_false : Barrier :=
  .proved "every normal number: window digit sums are not uniform mod b − 1"
    @CastingOut.not_castUniform_of_isNormal
    [``CastingOut.not_castUniform_of_isNormal]
    "casting-out laws strong enough that normal numbers themselves violate them"

/-- A digit-local premise on a set of density `< 1/2` cannot force normality. -/
def digitLocal_sparse_vacuous : Barrier :=
  .proved "masked reals: any premise reading digits on a density < 1/2 set"
    @G4Entropy.not_satisfiable_of_forces_normal
    [``G4Entropy.not_satisfiable_of_forces_normal]
    "a digit-local (schedule, sample, subsequence) premise implying normality of the whole"

/-- Barrier 1 of `ExplicitSquareNonNormal`: density-zero sparse sets have no power decay. -/
def sparse_polyDecay_wall : Barrier :=
  .frozen "sparse-digit Cantor measures with density-zero free set: no power Fourier decay"
    @ExplicitSquare.not_polyDecay_sparse_of_densityZero
    [``ExplicitSquare.not_polyDecay_sparse_of_densityZero]
    "power-rate Fourier decay for deterministic (dimension-zero) digit sets"

/-- Barrier 2 of `ExplicitSquareNonNormal`: `o(log n)` free digits have no log decay. -/
def sparse_logDecay_wall : Barrier :=
  .frozen "sparse-digit Cantor measures with o(log n) free digits: no logarithmic Fourier decay"
    @ExplicitSquare.not_logDecay_sparse_of_littleLog
    [``ExplicitSquare.not_logDecay_sparse_of_littleLog]
    "Davenport–Erdős–LeVeque decay for digit sets thinner than log n"

/-- Baker–Banaji: `√` of a quarter-Cantor point normal, its square not. -/
def sqrt_normal_square_not : Barrier :=
  .cited "√(cantorReal e) normal in base 2 while its square is not"
    ExplicitSquare.BakerBanajiQuarterCantor ExplicitSquare.exists_sqrt_normal_sq_not_normal
    [``ExplicitSquare.exists_sqrt_normal_sq_not_normal]
    "normality preserved by algebraic maps (squaring, inversion) of a normal number"

/-- Sibling (c): limits of normal numbers. -/
def normal_prefix_limit : Barrier :=
  .proved "normal numbers agreeing with 0 on prefixes of every length"
    Siblings.exists_normal_prefix_limit_not_normal
    [``Siblings.exists_normal_prefix_limit_not_normal]
    "diagonal or limit arguments that match prefixes of normal stages without window control"

/-! ## Arithmetic and specific constructions -/

/-- `UniformBad` fails in base 2 alone for `c ≤ log₂ 3`. -/
def uniformBad_base_two : Barrier :=
  .proved "UniformBad with 2^{−c} ≥ 1/3: refuted at base 2, n ∈ {0, 1}"
    @UniformBad.not_uniformBad_of_third_le
    [``UniformBad.not_uniformBad_of_third_le]
    "uniform-in-base bad approximability below exponent log₂ 3"

/-- The computable-approximation claim for GP families is false. -/
def approxGPfam_false : Barrier :=
  .proved "the quadratic-branch GP family Qbad: no primitive-recursive dyadic approximation"
    ExplicitPQ.not_approxGPfamClaim
    [``ExplicitPQ.not_approxGPfamClaim]
    "uniform computable approximation of every polynomial GP family"

/-- Dependence closure is necessary for Hertling-type rich-exactly sets. -/
def richExactly_two_impossible : Barrier :=
  .proved "a real rich exactly in base 2 (R = {2}, not dependence-closed)"
    Hertling.not_exists_richExactly_two
    [``Hertling.not_exists_richExactly_two]
    "block forcing that never uses dependence closure of the rich set R"

/-- Bergelson–Downarowicz: the reciprocal of a deterministic number need not be deterministic. -/
def reciprocal_question_false : Barrier :=
  .cited "a deterministic s with 1/s not deterministic (Bergelson–Downarowicz)"
    (DetSub 2 ∧ DetSqNotDet) (fun h => Deterministic.not_reciprocalQuestion h.1 h.2)
    [``Deterministic.not_reciprocalQuestion]
    "closure of deterministic (zero-entropy) numbers under field operations"

/-- Products of deterministic numbers form a dimension-zero set. -/
def deterministic_products_null : Barrier :=
  .proved "products of two deterministic numbers: a set of Hausdorff dimension 0"
    @Deterministic.dimH_detProducts
    [``Deterministic.dimH_detProducts]
    "writing a generic (or normal) real as a product of deterministic ones"

/-- The parity bit of `τ` (binary `Σ 2^{−k²}`) has density zero. -/
def tau_parity_sibling : Barrier :=
  .proved "Σ_k 2^{−k²}: the parity bit of τ, whose 1s have density zero"
    EDensity.card_odd_card_divisors_le
    [``EDensity.card_odd_card_divisors_le]
    "E-density arguments that read only the 2-adic (parity) information of τ"

/-- The single-survivor encoding misses `101` for squarefree sets at base 2. -/
def squarefree_powTwo_encoding : Barrier :=
  .proved "squarefree #257 at base 2: no single survivor in the cylinder of 101"
    Erdos257Squarefree.not_powTwoEncoding
    [``Erdos257Squarefree.not_powTwoEncoding]
    "single-survivor (power-of-two) encodings of words in #257 sums"

/-- The `HypE` frame cannot serve prime sets of logarithmic reciprocal growth. -/
def hypE_logRate : Barrier :=
  .proved "prime sets with Σ 1/p ≤ A log e + C over 2^{2^e}: excluded by the HypE frame"
    @G4.SchedB.hypE_frame_excludes_logRate
    [``G4.SchedB.hypE_frame_excludes_logRate]
    "the HypE schedule frame applied to gap sets (towerGapPrimes-like)"

/-- Sibling (d): a rational Lambert-type series. -/
def fermat_lambert_rational : Barrier :=
  .proved "Σ_k 2^k/(2^{2^k}+1) = 1: a rational Lambert-type series"
    Siblings.tsum_two_pow_div_fermat
    [``Siblings.tsum_two_pow_div_fermat]
    "irrationality of Lambert sums from the series shape alone (sparse index set, phase averages)"

/-- The drift-one arithmetic crux fails at `p = 71`. -/
def driftOne_fails_at_71 : Barrier :=
  .proved "p = 71: a square mod both primes 29, 31 in (71/3, 71/2)"
    Siblings.not_exists_prime_nonresidue_71
    [``Siblings.not_exists_prime_nonresidue_71]
    "a short-interval nonresidue argument that does not use p ≥ 73"

/-! ## Avoidance along `{2ᵘ3ᵛ}` and self-similar measures -/

/-- Furstenberg: an irrational point cannot avoid `0` at a constant rate along `{2ᵘ3ᵛ}`. -/
def furstenberg_constAvoid_false : Barrier :=
  .cited "irrational α with ‖qα‖ ≥ c > 0 for every q = 2ᵘ3ᵛ: none exists (Furstenberg 1967)"
    LinearFormsScales.Literature.Furstenberg1967 LinearFormsScales.not_constAvoid_of_furstenberg
    [``LinearFormsScales.not_constAvoid_of_furstenberg]
    "avoidance along {2ᵘ3ᵛ} at a rate bounded below, with no decay in q"

/-- The dependent pair: along `{2ᵏ}` the point `1/3` avoids `ℤ` at the constant rate `1/3`. -/
def powersOfTwo_constAvoid : Barrier :=
  .proved "dependent pair {2ᵏ}: ‖2ᵏ/3‖ ≥ 1/3 for every k, a constant avoidance rate"
    LinearFormsScales.constAvoid_powersOfTwo
    [``LinearFormsScales.constAvoid_powersOfTwo]
    "avoidance arguments blind to the independence of 2 and 3 (lacunarity or scale counting \
     alone), which would give the constant rate Furstenberg forbids"

/-- Cantor points fail every base `3ᵏ`: a `×3`-invariant measure is not normal in its own base. -/
def cantor_not_normal_three_pow : Barrier :=
  .proved "every middle-third Cantor point is not normal in any base 3ᵏ"
    @EntropyProfiles.not_isNormal_three_pow_cantorPt
    [``EntropyProfiles.not_isNormal_three_pow_cantorPt]
    "normality of a ×p-invariant measure in the dependent base p without a nonlinear input"

/-! ## Potential games (Schmidt-games lane) -/

/-- Normality is not potential winning: the winning set `U` meets no normal number. -/
def schmidt_normal_not_winning : Barrier :=
  .cited "base-b normal numbers: not (α, 1/4, 1/2, 1/2)-potential winning for every α > 0"
    SchmidtGames.Literature.BFSDimInterval
    (fun hJ (b : ℕ) (hb : 2 ≤ b) =>
      SchmidtGames.not_potentialWinning_isNormal SchmidtGames.potentialWinning_E hJ hb)
    [``SchmidtGames.not_potentialWinning_isNormal, ``SchmidtGames.potentialWinning_E]
    "game or potential-guided descent arguments aimed at normality: Alice's deletions only \
     avoid, they cannot force digit frequencies"

/-- One fixed exponent `C` is not potential winning at scale `2^{−C}/2`: `E C` misses a gap. -/
def schmidt_fixedC_not_winning : Barrier :=
  .cited "E C for one fixed C ≥ 0: not (α, 1/4, 1/2, 2^{−C}/2)-potential winning for small α"
    SchmidtGames.Literature.BFSDimInterval
    (fun hJ (C : ℝ) (hC : 0 ≤ C) => SchmidtGames.not_potentialWinning_E_small hJ C hC)
    [``SchmidtGames.not_potentialWinning_E_small]
    "potential-game arguments for one exponent C that start below scale 2^{−C}; they need the \
     union over C or a start scale well above 2^{−C}"

/-- BFS Theorem 5.5 with the starting scale `ρ` unrestricted is false. -/
def bfs_unrestricted_scale_false : Barrier :=
  .proved "BFS 5.5 dimension bound with ρ unrestricted (S = [0,1]ᶜ is winning at ρ = 1/α)"
    SchmidtGames.not_BFSDimInterval_unrestricted
    [``SchmidtGames.not_BFSDimInterval_unrestricted]
    "dimension transfers from a potential game whose opening scale exceeds the regularity scale \
     of the support measure"

/-! ## Rationals near the Cantor set -/

/-- The trivial numerator count fails below `2 + log₂ 3` on the real forced-run schedule. -/
def cantorExp_trivialCount_mu_three : Barrier :=
  .proved "μ₀ = 3 forced-run schedule: 108 free places in the window [108, 324), 2^108 < 3^108"
    CantorExactExponent.bcTerm_red_mu_three
    [``CantorExactExponent.bcTerm_red_mu_three]
    "Borel–Cantelli with the trivial count (2^F numerators per denominator) in windows that \
     enter a forced run"

/-- A ℚ-independent Liouville-type pair whose ℚ-span holds no normal number. -/
def liouville_pair_qSpan : Barrier :=
  .frozen "sparse Liouville pair x, y (1, x, y ℚ-independent): no c₁x + c₂y is normal"
    @QSpan.exists_pair_qSpan_not_normal
    [``QSpan.exists_pair_qSpan_not_normal]
    "pair-universal mechanisms (carry coupling, ℚ-span or Wall-type closure arguments) aimed at \
     normality of some element of a ℚ-span"

/-- Every registered barrier, for `#barrier_audit`. -/
def allBarriers : List Lean.Name := [
  ``stoneham_two_not_six, ``cantorLiouville_three_dvd, ``cassels_cantor_ae_normal,
  ``stoneham_six_disjunctive_not_normal, ``rich_not_normal_everywhere,
  ``irrational_not_disjunctive, ``order_k_normal_not_normal, ``log_normal_not_simply_normal,
  ``tt_noExc_constOne, ``castUniform_false, ``digitLocal_sparse_vacuous,
  ``sparse_polyDecay_wall, ``sparse_logDecay_wall, ``sqrt_normal_square_not,
  ``normal_prefix_limit, ``uniformBad_base_two, ``approxGPfam_false,
  ``richExactly_two_impossible, ``reciprocal_question_false, ``deterministic_products_null,
  ``tau_parity_sibling, ``squarefree_powTwo_encoding, ``hypE_logRate,
  ``fermat_lambert_rational, ``driftOne_fails_at_71, ``furstenberg_constAvoid_false,
  ``powersOfTwo_constAvoid, ``cantor_not_normal_three_pow, ``schmidt_normal_not_winning,
  ``schmidt_fixedC_not_winning, ``bfs_unrestricted_scale_false, ``cantorExp_trivialCount_mu_three,
  ``liouville_pair_qSpan]

end NormalNumbers.Barriers
