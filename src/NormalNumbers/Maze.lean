/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.CFScheduleARefuted
import NormalNumbers.G4Base2GapObstruction
import NormalNumbers.VandeheyRaney
import NormalNumbers.G4EntropyBarrier
import NormalNumbers.G4EntropySubsample
import NormalNumbers.G4EntropyMixture
import NormalNumbers.G4EntropyPointwise
import NormalNumbers.G4EntropyDiagonal
import NormalNumbers.G4RowVariance
import NormalNumbers.G4RowMassOptimal
import NormalNumbers.G4WiringSparse
import NormalNumbers.StonehamSixFailure
import NormalNumbers.CastingOut
import NormalNumbers.LogCastingOut
import NormalNumbers.C3MrtTTDefect
import NormalNumbers.LiteratureTTEquidistributedDefect
import NormalNumbers.C3MrtBlockDefect
import NormalNumbers.Walsh
import NormalNumbers.WalshBase
import NormalNumbers.WallRational
import NormalNumbers.MoshchevitinShkredovRefuted
import NormalNumbers.VandeheyAutomaton
import NormalNumbers.VandeheyS7Memory
import NormalNumbers.VandeheyS7Hecke
import NormalNumbers.VandeheyS7Predict
import NormalNumbers.VandeheyS7Quadratic
import NormalNumbers.VandeheyS7BlockRefute
import NormalNumbers.VandeheyS7BlockGenRefute
import NormalNumbers.VandeheyS7Circular
import NormalNumbers.VandeheyS7StateCouple
import NormalNumbers.VandeheyS7StateAudit
import NormalNumbers.VandeheyS7Audit
import NormalNumbers.VandeheyS7WidthDensity
import NormalNumbers.VandeheyS7ArchWidthFree
import NormalNumbers.Erdos257Squarefree
import NormalNumbers.EDensityAudit

/-!
# `Maze.lean` — the halls we have walked, encoded

A machine-checked register of routes this programme has **walked and closed**, so that a
future session does not re-enter a hall someone already walked.  Trevor, 2026-09-20:
*"I'd argue that it's worth writing down, so that future us never revisits it... a set of
Lean formulations that encode all of the conclusions drawn."*

The programme's expensive failure mode is not a wrong proof.  It is a month spent
re-deriving a verdict that is already on disk, in a handoff file numbered 147.  Prose rots
silently; this file does not, because **it must compile**.  Every `Tier.kernel` row below is
an `alias` onto a theorem that lives in this build: rename or delete that theorem and this
file stops building.  That is the whole design.

## How to use it

Two passes, in this order.

1. **Match your route against `Verdict`** (§1).  Most closed halls closed for one of eight
   structural reasons, and the shape is recognisable *before* any work.  The doc-comment on
   each constructor carries its tell.
2. **Grep `register`** (§4) for the object you are about to touch.

If your route is not here, it is genuinely unwalked — say so out loud, because that is rarer
than it feels.

**Adding a row?**  State its obstruction in Lean first (a theorem, a `¬`, or a `sorry` statement
with a confidence), and for a `wall` its reopen condition as a `def … : Prop`.  Then add a `Link`
in `MazeAudit.lean`.  `#maze_audit` fails the build on a row with no link: its reasons would be
prose only.

## The three tiers

* `Tier.kernel` — the verdict is a **theorem in this build**, re-exported below by `alias`.
* `Tier.frozen` — the statement is precise Lean but **undischarged**: a `def ... : Prop`
  with no proof and no `sorry`.  A frozen row claims a *statement*, never a truth value.
* `Tier.cited` — the objects are not formalized; the verdict lives in the `evidence` field
  with its file pointer.  Weakest tier; promote when the objects arrive.

⚠️ A `Tier.cited` row is **not** machine-checked.  Do not read this file as if every row
carried the kernel's authority; read the `tier` field.

## What this file is not

Not a status file (`STATUS.md`), not a plan (`ROADMAP.md`), not a list of open problems
(`PENDING_WORK.md`).  Every row here is CLOSED or PARKED.  A row is never deleted: if a hall
re-opens, the row stays and gains a note, because the fact that we once closed it is itself
evidence.  (`hdom` is the live example — refuted 2026-08-24, reversed 2026-08-27.)

## The orientation: why most halls close

Three external doors exist, and only three (`docs/tower-2026-08-29.md` §0a): **Diophantine**
(separation of powers, linear forms in logs), **dynamical** (×2×3 rigidity, equidistribution)
and **internal counting** (the digit combinatorics itself).  A fourth is always tempting and
is always a mirror: a **mod-p / quotient coordinate** on a constant defined by its own digits
re-imports the unknown, because the quotient *is* the digit prefix.

Behind all three real doors stands one wall: nothing in current mathematics lower-bounds the
Weyl sums of a *natural* constant.  Furstenberg's ×2×3 is its best-known name.  So the
cheapest test of a new idea is: **which of the three doors supplies its estimate?**  If the
honest answer is "none, it is self-contained", the idea is a `Verdict.restatement` and §1's
first tell will show it in one step.
-/

namespace NormalNumbers.Maze

/-! ## 1. The eight shapes of a dead end

Each constructor's doc-comment carries its **tell** — the thing visible before the work, not
after.  Match your route against these before grepping the register. -/

/-- The shape of a closed route. -/
inductive Verdict where
  /-- **RESTATEMENT.** The criterion is logically equivalent to the target.
  🚨 Tell: you cannot name a proof route for your criterion that avoids the target.  Ask
  "what would I do to *prove* this hypothesis?"  If the honest answer is "bound the same
  Weyl sum", stop.  The extra apparatus (thresholds, constants, positive parts) adds no
  leverage; it disguises the equivalence. -/
  | restatement
  /-- **VACUOUS.** True, but only in the regime where the conclusion is already known, or
  carrying no information about the object.
  🚨 Tell: split into cases and one branch makes the hypothesis hold trivially.  A criterion
  that cannot *fail* on a hard instance is not a criterion. -/
  | vacuous
  /-- **REFUTED.** A counterexample or a computation kills the mechanism.
  🚨 Tell: none needed — this is the healthy outcome of a probe.  Record the witness. -/
  | refuted
  /-- **FALSE-AS-STATED.** The frozen `Prop` is wrong, usually at a boundary index or a
  parameter value.
  🚨 Tell: the statement quantifies over all `i` and you checked it at `i = 1`.  Probe
  endpoints first.  Laps refuting their own frozen Props is a healthy rate, not a failure. -/
  | falseAsStated
  /-- **WALL.** The route is sound and needs an estimate nobody has.
  🚨 Not a mistake — the honest frontier.  Name the missing estimate and the nearest
  literature, then park.  A wall row exists so the next session recognises the wall on sight,
  and so a new external theorem can be checked against the list cheaply. -/
  | wall
  /-- **PARKED.** Deliberately set down with a reason; not closed.
  🚨 Tell: the reason is usually "needs an unavailable input" or "low odds, high cost". -/
  | parked
  /-- **PRIOR-ART.** Already in the literature.
  🚨 Tell: the statement is clean and the construction is natural.  Clean + natural means
  someone got there.  Sweep before building, and sweep the *generalisation* too. -/
  | priorArt
  /-- **PROVABLE-BUT-EMPTY.** A real theorem whose bound is orders of magnitude from reality.
  🚨 Tell: compute the bound and the truth side by side *before* the lap.  A cap of 15 077 on
  a quantity that measures 1 is not a result, whatever its provenance. -/
  | provableEmpty
  deriving DecidableEq, Repr

/-- Evidence tier of a register row.  See the module doc-comment. -/
inductive Tier where
  /-- The verdict is a theorem in this build, re-exported by `alias` in §2. -/
  | kernel
  /-- A precise but undischarged statement (§3).  Claims a statement, never a truth value. -/
  | frozen
  /-- Prose verdict with a file pointer; objects not formalized.  NOT machine-checked. -/
  | cited
  deriving DecidableEq, Repr

/-- One walked hall. -/
structure Hall where
  /-- Short name, in the programme's own vocabulary. -/
  name : String
  /-- What was tried, one sentence. -/
  tried : String
  /-- The shape of the closure. -/
  verdict : Verdict
  /-- How much authority this row carries. -/
  tier : Tier
  /-- Why it closed: the mechanism, one sentence. -/
  mechanism : String
  /-- File pointer, and for `Tier.kernel` the theorem name. -/
  evidence : String
  /-- ISO date of the verdict. -/
  date : String
  deriving Repr

/-! ## 2. Tier `kernel` — verdicts that are theorems in this build

Each `alias` below is load-bearing: if the target theorem is renamed or deleted, **this file
fails to build**, and the register can never silently drift from the mathematics. -/

/-- **HALL: ψ-pushed Chebyshev variance** (`falseAsStated`, 2026-08-25).
The single-stream z-side crux of the B6 route.  On a deep cylinder the pushed block count is
near-constant, so the cylinder-restricted second moment about the *global* mean is `Θ(n²)`,
not `O(n)`: a restricted Chebyshev must centre at the *conditional* mean.  Everything
downstream (`psi_pushed_chebyshev_brick` → `_aggregate` → `_poly`) is therefore vacuous. -/
alias hall_psi_pushed_variance := NormalNumbers.varianceBlockCountPsiPushed_false

/-- **HALL: sample-entropy → ordinary frequency (`T_E`)** (`falseAsStated`, 2026-09-14).
The entropy expedition's primary transfer target.  `maskedReal G₄` meets the exact premise —
its joint sample law equals `G₄`'s at every scale — yet at most a quarter of its digits are
`1`.  Generalises: the sample is digit-local and reads density `≤ 1/4 < 1/2`, so *any*
satisfiable `S`-local premise admits a non-normal mask. -/
alias hall_T_E := NormalNumbers.G4.Sched.not_T_E'

/-- **HALL: E-T8 / chunking to a strictly increasing subsample** (`refuted`, 2026-09-14).
Replace repetition by `c` disjoint certified chunks per scale.  A chunk is certifiable only
if its digit count exceeds the collection's total entropy deficit, and there are never enough
chunks; the barrier is dimension-independent. -/
alias hall_chunking := NormalNumbers.G4.Sched.chunks_insufficient

/-- **HALL: certified-granule assembly (the granularity wall)** (`wall`, 2026-09-14).
Read `G₄`'s sampled digits in position order as a concatenation of certified granules.  The
first non-vacuously certified granule of scale `i+1` already outreads everything scale `i`
produced, however the granule is cut. -/
alias hall_granularity_wall :=
  NormalNumbers.G4.Sched.certified_granule_exceeds_previous_scale

/-- **HALL: pointwise frequency from the entropy deficit** (`refuted`, 2026-09-14).
A `t`-wise bound at each fixed position vector rather than averaged.  A law with a
one-bit-per-window deficit still admits a probability-zero pattern at a fixed position
vector — maximal deviation under a tiny deficit. -/
alias hall_pointwise_deficit := NormalNumbers.G4Entropy.no_pointwise_bound_from_deficit

/-- **HALL: normality of `G₄` on the quantized sampler** (`wall`, closed by theorem,
2026-09-14).  A quantized digit-local sampler forces normality **iff** it reads a density-one
position set; this schedule reads `≤ ½(3/K⁴)^K`.  This is why the exact-cancellation routes
(`G4DeformationVerdict`, `G4BalancedRigidity`, `G4GroupedVerdict`) could not have worked. -/
alias hall_quantized_normality := NormalNumbers.G4Entropy.qForces_normal_iff_density_one

/-- **HALL: axis-skeleton sharpening** (`refuted`, 2026-09-15).
Shrink `skel` to the polynomial axis skeleton `skel₁` to sharpen the `dmin^{-H/2}` density
rate.  `pairWit α = [α₁=1 ∧ α₂=1]` is balanced, nonzero, and vanishes on all of `skel₁`. -/
alias hall_axis_skeleton := NormalNumbers.G4.RowVariance.balance_not_determined_by_axes

/-- **HALL: base two for the §4D disjunctivity design** (`refuted`, whole design family,
2026-09-14, sharpened 2026-09-16).  Any line-sum-annihilating array has `∑|μ| ≥ 2^K`, so
`rowL1 2 K = 1` while §4D needs `< 1`.  No re-tuning of the cutoff `Y` escapes: the medium
range needs `Y ≲ √X` and a non-cancelling far range needs `Y ≥ X^{1-o(1)}`.  ⚠️ This is a
no-go for the **mass-minimizing design family**, NOT a universal impossibility — do not
promote it into one. -/
alias hall_base_two_design := NormalNumbers.G4.two_pow_le_sum_abs

/-- **HALL: old `Good.sep` (sparse wiring)** (`falseAsStated`, 2026-09-20).
`Good.ε_range` and `Good.sep` are jointly unsatisfiable at `i = 0`; the repair is `1 ≤ i`.
Do not "restore" the old field. -/
alias hall_good_sep := NormalNumbers.G4Sparse.sep_eps_incompatible

/-! ### The T3c emptiness, as arithmetic

`Verdict.provableEmpty` is the one shape whose evidence is a *pair*: the bound, and the
truth.  Here both are checkable.  Block `K = 5` of the base-6 expansion of `α₂,₃` has its
critical slice at `(n*, a, c) = (97, 92, 146)` (`experiments/t3c_critical_runs.py`).  A run
of `L` copies of the digit `5` starting there means `D · 6^L ≤ 2^c` for `D = 2^c − 3^a`.

The theorem below shows the true run is **exactly 1**.  The cap available from
`rhinLite_log23_measure` (collatz-moonshot) at this block exceeds **16 000**.  That gap is
the verdict: the theorem is real, one wiring lap away, and says nothing. -/

/-- **HALL: T3c critical-slice run cap** (`provableEmpty`, 2026-09-20).
At block `K = 5` the true base-6 run at the critical slice has length exactly `1`: one copy
of the digit `5` fits (`6·D ≤ 2^146`) and two do not (`36·D > 2^146`).  The polynomial
Diophantine cap at this block is `> 16 000`.  Parked as node `CriticalSliceRunCap`;
see `DESIGN-2026-09-20-t3c-verdict.md`. -/
theorem hall_t3c_block5_true_run_is_one :
    6 * (2 ^ 146 - 3 ^ 92) ≤ 2 ^ 146 ∧ 2 ^ 146 < 36 * (2 ^ 146 - 3 ^ 92) := by
  constructor <;> norm_num

/-- **HALL: α₂,₃ abelian-normal in base 6** (`refuted`, 2026-09-23).
The "natural separation" hope was that `α₂,₃`, normal in base 2, would still be
abelian-normal in base 6 — a weaker statistic surviving the base change.  It does not: the
base-6 expansion carries forced zero blocks on `(3ᵐ, 1.16·3ᵐ]`, because there the head
`6ᵖ·Σ_{k≤m}` is an integer divisible by 6 while the tail `6ᵖ·Σ_{k>m}` is below 1.  A block
of `0.1·3ᵐ` forced zeros pushes freq(0) at `N = 1.1·3ᵐ` up to `8/33 > 1/6`, so `α₂,₃` is not
even **simply** normal in base 6, let alone abelian-normal.  (Bailey–Borwein 2012 proved
base-6 non-normality first; this is that mechanism, formalized.) -/
alias hall_stoneham_six_abelian := NormalNumbers.Failures.not_simplyNormal_six_stoneham23


/-- **HALL: `TTNonPretentious` as TT's hypothesis (3.3)** (`vacuous`, 2026-09-25).
The formal non-pretentiousness hypothesis put `∃ A > 0` *inside* the `∀ X L`, so `A = 1/L`
discharges it for **every** 1-bounded `g`, `g = 1` included: every summand of
`ttPretentiousSum` is `≥ 0`.  TT's implied constant is absolute.  Restated faithfully as
`CastingOut.TTNonPretentiousUnif` (constant outside, Dirichlet characters of conductor
`≤ (log X)^{1/125}` included, twists up to `X²`), which `g = 1` provably fails
(`not_ttNonPretentiousUnif_one`). -/
alias hall_tt_nonpretentious_vacuous := NormalNumbers.CastingOut.ttNonPretentious_trivial

/-- **HALL: a synchronizing word for the det-±D CF transducer** (`falseAsStated`, 2026-09-28).
`VandeheyAut.exists_jointFreq_limit` replaced Vandehey 2017 Theorem 3.1 by a PATHWISE
merging argument: after a synchronizing word the automaton forgets its initial state, so the
state is a function of the last `L` digits and the joint (window, state) count becomes a
finite sum of ordinary cylinder counts.  The mechanism is sound; its hypothesis is
unsatisfiable.  The transducer's reachable states fibre over `ℙ¹(ℤ/D)` by the row-lattice
class of the state matrix, the class evolves by `c ↦ c · B_a`, and each `B_a` lies in
`GL₂(ℤ/D)` and so acts BIJECTIVELY -- a bijective quotient never forgets, and there are
`D + 1 ≥ 3` classes to separate.  Decided by `probes/cf_transducer_sync.py` (no synchronizing
word to length 20; 1953 of 3160 state pairs unmergeable at `D = 2`) and then proved in
general as `not_synchronizing_of_injective_quotient`.  The sorried
`exists_jointFreq_limit` is removed; the live replacement is
`VandeheyCocycle.tendsto_jointCount_of_classEquidistribution`, whose hypothesis
`ClassEquidistribution` is the crux the class cocycle actually poses. -/
alias hall_vandehey_synchronizing_transducer :=
  NormalNumbers.VandeheyAut.not_synchronizing_of_injective_quotient

/-- **HALL: the emitted digit as a window function of the input** (`falseAsStated`,
2026-09-29).  The §7 assembly planned to compute the image digit at a position from a bounded
window of the input digits, `F w := emitDigit (wordState w)`, citing the merging bound
`spread_runWord_le` for independence of the initial state.  `spread_runWord_le` bounds the
DIAMETER of the image of `[0,1]`, uniformly in the initial state; it says nothing about the
image's LOCATION, and `runWord s w = s.comp (wordState w)` puts the location entirely in the
initial state.  Witnesses: `⟨1,3;0,8⟩` and `⟨1,7;0,32⟩` map `[0,1]` into the digit-`2` and
digit-`4` cylinders, so after reading ANY word they both emit, and emit `2` and `4`.  Both
have distortion `1`, so the bounded-distortion compact fiber does not evade it.  What
survives is `cfDigit_mob_eq_emitDigit`: the digit is a function of the STATE, so the
decomposition must be indexed by (state class, input word), as `JointStateFreq` is in the
proved integer case. -/
alias hall_emit_digit_window_function :=
  NormalNumbers.VandeheyS7.MobState.no_window_function

/-- **HALL: Hecke approximation of `φ` by Fibonacci ratios** (`refuted`, 2026-09-29).  The repo
owns Vandehey 2017 Theorem 1.1, so the most natural route to §7 is to approximate: each
`(F_{k+1}/F_k)·x` is CF-normal, the ratios converge to `φ`, nearby reals share a long CF prefix,
so take a diagonal limit.  It dies on the *cost* of the approximation.  `φ` is the
worst-approximable real — `|p − qφ| ≥ 1/(4q)` (`abs_sub_mul_goldenRatio_ge`), from the nonzero
integer norm form `p² − pq − q² = (p − qφ)(p − qψ)` — so buying agreement of the images to CF
depth `N` forces `q² > cᴺ` (`pow_lt_den_sq_of_image_approx`) and hence a determinant
`pq ≥ q² > cᴺ` (`sq_le_det_of_approx`).  Theorem 1.1's automaton then carries `e^{Ω(N)}` states
while only `N` input digits are read: its equidistribution, an asymptotic statement about that
automaton, says nothing about the prefix the diagonal argument needs.  Note where the content
sits: for a *rational* target the norm form vanishes identically, which is exactly why Theorem 1.1
itself is provable and this is not. -/
alias hall_hecke_approximation :=
  NormalNumbers.VandeheyS7.pow_lt_den_sq_of_image_approx

/-- **HALL: predictable target sets from marginals alone** (`refuted`, 2026-09-29).  The crux
`OrbitCellBound` unwinds to a bound on `#{n<N : Gⁿx ∈ A n}` where `A n = s_n⁻¹(E)` is determined by
`x₁…x_n` and is small, and the input orbit has the correct marginal frequencies.  Those three
facts do not suffice, and the witness is elementary: the grid `u n = n/k` is *exactly* uniform on
the `k` cells of width `1/k` — perfect marginals, zero error — yet `u n` lies in
`(u_{n−1}, u_{n−1} + δ)` for every `n ≥ 1` as soon as `1/k < δ`, a hit frequency of `(k−1)/k`
against an interval of length `δ`.  At `δ = 1/2`, `k = 10`: `9/10` observed against `6/10`
allowed.  Consequence for the route: any proof of `OrbitCellBound` must use the specific
arithmetic of `s_n = O_n⁻¹ Φ P_n`, never predictability plus size.  With
`hall_emit_digit_window_function` this closes both soft routes: the state cannot be forgotten, and
it cannot be ignored. -/
alias hall_predictable_from_marginals :=
  NormalNumbers.VandeheyS7.not_predictableHitPrinciple

/-- **HALL: `BlockForget` in the uniform-`z` form** (`falseAsStated`, 2026-09-29).  Route A's
crux asked the block time-average `blockAvg s T w z` to forget the initial state `s` uniformly
over ALL input points `z ∈ (0,1)`.  It does not.  The run from state `s` on input `z` emits the
CF of `s.mob z`, so at a FIXED `z` the block average is the frequency of `w` in that CF (up to
the clock rate).  Take `z = √2 − 1`, a fixed point of the Gauss map, so every digit is `2`
(`cfDigit_sqrtTwoSub`): the digit `1` has frequency `0` from the identity state.  The state
`shiftState : t ↦ 2/(t+2)` has rational entries and width `1/3`, and sends `√2 − 1` to
`2√2 − 2` (`shiftState_mob_sqrtTwoSub`), a `2`-cycle of the Gauss map whose digits alternate
`1, 4` (`cfDigit_twoSqrtTwoSub_even/odd`): the digit `1` has frequency `1/2`.  Two distinct
periodic orbits never merge — they lie in different `GL₂(ℤ)` cycles of `ℚ(√2)` (discriminants
`8` and `32`) — so time-averaging cannot help and this is not probe trap #2.

**Kernel, as of the same day**: `not_blockForget` (S7-BX) discharges the row outright, by never
going through digit frequencies at all.  The skew-product orbit of `(shiftState, √2−1)` is a
`2`-cycle — `shiftState ∘ read 2 = read 1 ∘ midState` and `midState ∘ read 2 = read 4 ∘ shiftState`,
with the emission unique (`emitStep_unique`) — so the even phase's image `2√2−2` has first digit
`1` and the odd phase's `(√2−1)/2` has first digit `4`: the block average is `⌈T/2⌉/T ≥ 1/2` for
every `T`, against `0` from the reference state.  **The repair costs nothing**: the architecture only ever evaluates the crux at
the orbit points `Gᵐx` of a CF-normal `x`, and a quadratic irrational is never CF-normal.  The
live crux is `BlockForgetGen` (S7-BG), the same statement with `z` restricted to CF-normal
points; `BlockForget.gen` records that the refuted form is the stronger one. -/
alias hall_blockforget_uniform_z := NormalNumbers.VandeheyS7.MapState.not_blockForget

/-- Companion witness of `hall_blockforget_uniform_z`: the shifted point is a `2`-cycle. -/
alias hall_blockforget_uniform_z_cycle :=
  NormalNumbers.VandeheyS7.cfDigit_twoSqrtTwoSub_even

/-- Companion witness of `hall_blockforget_uniform_z`: the two states meet at one input. -/
alias hall_blockforget_uniform_z_state :=
  NormalNumbers.VandeheyS7.MapState.shiftState_mob_sqrtTwoSub

/-- **HALL: the CF-normal repair of `BlockForget`** (`falseAsStated`, 2026-09-29, same day as the
row above).  Once the uniform-`z` crux fell, the natural repair was to restrict the input
quantifier to CF-normal `z` (`BlockForgetGen`, S7-BG), since a quadratic irrational is never
CF-normal and the architecture only ever evaluates the crux at orbit points of a CF-normal input.
The repair is FALSE, and for a reason that no further repair of this shape survives: the crux's
quantifier order is `∃ T, ∀ z`, so the block length is fixed BEFORE the input, while
`blockAvg s T w z` at a fixed `T` is decided by the state cycle alone once the first `T` digits of
`z` are known — and CF-normality is a tail property, so a CF-normal `z` may open with any
prescribed prefix.  Feed it `T` copies of the digit `2`: the state cycle is the S7-BX cycle, whose
two phases send ALL of `(0,1)` into `(2/3,1)` and `(1/6,1/4)` respectively, so the block average
is `≥ 1/2` from `shiftState` against `0` from the reference state.

Consequence: any surviving crux must let `T` depend on the input, i.e. be asymptotic in `T` — at
which point the transducer-correctness bridge, and with it the headline, re-enters, so route A's
`BlockForget` step was never a reduction. -/
alias hall_blockforget_cfnormal := NormalNumbers.VandeheyS7.MapState.not_blockForgetGen

/-- **HALL: the block-forgetting crux as a REDUCTION of §7 Problem 1** (`restatement`, 2026-09-29).
Route A factors the headline through a crux (`BlockForget` → `BlockForgetGen` → `BlockForgetRun` →
`BlockForgetAll`, S7-BF/S7-BR/S7-AW) that compares the run's block statistics with the reference
state's, and reads that comparison as the remaining analytic input.

**Kernel**: it is not an input, it is the theorem.  S7-RR computes the reference run to be the Gauss
shift itself, so the comparison is against the INPUT's own statistics; S7-NR then proves both
directions of the signed form — the crux's Cesàro sum with the absolute value removed holds exactly
when `slotCount Φ x w p / p → γ(I_w)`, i.e. exactly when the conclusion holds
(`signedForget_iff_slotCountFreq`).  What the absolute values add is local information and nothing
else, and `abs_gap_witness` (this row's alias) shows that step is not free: two `[0,1]`-valued
sequences can have equal Cesàro means while the Cesàro mean of `|difference|` is `1`.

So the crux is the headline PLUS local clock regularity PLUS window concentration: strictly
stronger, hence never a reduction.  The architecture (`isCFNormal_image_of_blockForgetAll`, S7-AW)
remains a correct and useful FACTORISATION — it isolates exactly what locality would buy — but no
lap should treat proving the crux as easier than proving the theorem. -/
alias hall_blockforget_is_restatement := NormalNumbers.VandeheyS7.abs_gap_witness

/-- **HALL: the `TransducerData` bundle** (`vacuous`, 2026-09-27).  Route B's §7 front was packaged
as an existential over a family of sets `S n j` said to carry the transducer's block structure.
Nothing in `BlockCoupling` ties `S n j` to the state, so `S n j = univ`/`∅` according to whether the
slot hits the target satisfies it whenever the conclusion holds (`blockCoupling_trivial`): the
bundle is a restatement of `OrbitWordBound`, not a reduction of it.  The repair pins the sets to a
state family (`StateCoupling`/`StateData`) — and that repair is itself vacuous, next row. -/
alias hall_transducerdata_vacuous := NormalNumbers.VandeheyS7.blockCoupling_trivial

/-- **HALL: the `StateData` repair** (`restatement`, 2026-09-27).  Pinning the coupling sets to a
family of `MobState`s pins nothing: the type is large enough to interpolate any single pair of
points, so `lowState (Gⁿy / Gⁿx)` sends `Gⁿx` to `Gⁿy` exactly and
`stateData_of_orbitWordBound` derives the bundle from its own conclusion.  A transducer hypothesis
has content only when the state family is pinned to the input AS A FUNCTION, by the read/emit
recursion — which is what `runState` (S7-RN) finally supplies. -/
alias hall_statedata_restatement := NormalNumbers.VandeheyS7.stateData_of_orbitWordBound

/-- **HALL: `StateClock` below the width scale** (`vacuous`, 2026-09-27).  `StateClock q r₀ η K`
compares an orbit count against a threshold `T`; at `T < 1/η` the state `lowState η` has its whole
image below `1/T`, so every orbit time is counted and the inequality holds for free
(`blockCount_le_card_lowState`).  The hypothesis has content only at `T ≥ 1/η`. -/
alias hall_stateclock_below_width := NormalNumbers.VandeheyS7.blockCount_le_card_lowState

/-- **HALL: the one-digit-per-read throttle** (`refuted`, 2026-09-29, lap 91).  Every §7 scalar debt
(`WidthAfford`, `MeanSlack`, `ClockLinear`'s uniform floor) was stated for a transducer whose `step`
emits AT MOST ONE digit per read (`runWord_length_le_one`).  That throttle creates a queue of
known-but-unemitted output digits; the queue is a mean-zero random walk, so `log (1/width)` is
null-recurrent of size `≍ √n` and the wide times have density ZERO.  `not_widthAfford_of_wide_sparse`
(this row's alias) then makes `WidthAfford` FALSE, and `crux_sum_le_of_wide_sparse` makes the
width-filtered crux vacuous on the same run.  Vandehey's transducer emits a variable-length word;
with maximal emission (S7-GR's `flushState`) the same exact simulation keeps the slack bounded and
`freq(width < η) ≍ √η`.  **Moral: price the instrument before the hypothesis.** -/
alias hall_one_digit_throttle := NormalNumbers.VandeheyS7.MapState.not_widthAfford_of_wide_sparse

/-- The forward half of the same row: the crux does imply the goal. -/
alias hall_blockforget_implies_goal :=
  NormalNumbers.VandeheyS7.MapState.isCFNormal_image_of_blockForgetAll



/-- **HALL: the `min`-rule descent of Vandehey 2017 Lemma 2.1** (`refuted`, 2026-09-28).
Lemma 2.1's proof (pp. 6-7) normalizes an ingested digit by the Euclidean rule
`d = min(floor(alpha/gamma), floor(beta/delta))`, claiming "no coefficient grows and at least
one drops by 1".  It does not: when the two column ratios have already separated, one of the
two floors is `0`, the `min` emits nothing and the step degenerates to `J`.  Witness (the
smallest, found by `probes/vandehey_lemma21.py`): from the genuine state `[[0,3],[1,1]]` of
`M_3` with `j = 1`, the paper's own `d_0 = 1` lands on `[[2,1],[1,2]]`, and the rule then
two-cycles `[[2,1],[1,2]] -> [[1,2],[2,1]] -> [[2,1],[1,2]]` with neither matrix in `M_3`.
The *statement* of Lemma 2.1 survives (a free search over digit strings rescues every stalled
start), so this refutes the proof, not the lemma.  The live replacement is Raney's balanced
normal form, `Mat2.exists_balanced_decomp` / `Mat2.isRD_ingest_cfString`, whose descent
terminates because stripping `L` or `R` strictly drops the entry sum. -/
alias hall_vandehey_lemma21_min_rule :=
  NormalNumbers.Mat2.vandeheyStep_not_terminating

/-- **HALL: the low/high split as a route to `UniformResonantMass`** (`priorArt`, 2026-09-28).
`C3MrtURMLowHigh.lean` split the resonant primes at `lowHeight t = 16 log(2+|t|)` to tame the
Brun-Titchmarsh error tail (the absolute-height split in `C3MrtWindowMass` costs `O(|t|)`, an
exponential over budget).  The split works, and its low range and wide high range are proved
there; but the narrow high range `|t| < 2δ` needs a dyadic grouping of the per-window Mertens
additive, and before that landed `C3MrtUniformMass.lean` reached the SAME theorem by a
different assembly of the same toolkit.  The route is retired as redundant, not refuted: its
sorry-free lemmas stay, its one open obligation is deleted for want of a consumer.  The C3
headline `conjC3_of_geom_input_band'` now consumes `uniformResonantMass_holds` directly, so
`UniformResonantMass` is no longer a hypothesis anywhere on the archimedean side. -/
alias hall_urm_low_high_split := NormalNumbers.CastingOut.uniformResonantMass_holds

/-- **HALL: single-survivor encoding for squarefree Erdős #257 at base 2** (`refuted`,
2026-10-03).  The joint-Lambert construction reads its word off one survivor coefficient `2a`;
for squarefree `A` the coefficient is `2^{ω}`, a power of two, so one survivor contributes one
bit (`fract_two_pow_div_two_pow`) and the encoding misses the cylinder of `101`.  Disjunctivity
would need one exact-`ω` survivor per `1`-bit along one CRT progression. -/
alias hall_sqfree_single_survivor := NormalNumbers.Erdos257Squarefree.not_powTwoEncoding

/-- **HALL: Moshchevitin-Shkredov Theorem 1, in its CF specialization** (`falseAsStated`,
2026-09-28).  The hot-spot criterion Vandehey 2017 Lemma 3.3 leans on -- "uniformly bounded
upper block frequencies imply normality" -- is FALSE on the non-compact CF alphabet, as
Airey-Mance predicted.  Witness: `x = [0; 1, 2, 3, ...]` (built as the limit of the nested
cylinders `[1,2,...,s+1]`).  Its digits strictly increase, so every genuine block occurs at
most once, every block frequency tends to `0`, and the hypothesis holds VACUOUSLY with
`sigma = 0`; but the digit `1` then has frequency `0`, not `gamma(I_1) = log_2(4/3) > 0`.
Any route through `moshchevitinShkredov_cf` is dead. -/
alias hall_moshchevitin_shkredov_cf_false := NormalNumbers.moshchevitinShkredov_cf_false

/-- **HALL: the `K`-point no-exceptional-set input, as stated** (`falseAsStated`, 2026-09-25).
`KPointNoExcWith cK CstK 2` is FALSE for any `0 < cK 2`: with both factors the constant `1`
(free by the row above), `W = 1`, shifts `1, 2`, `X = exp L`, `N = ⌈√X⌉`, the
progression-restricted mean is exactly `1` while the claimed bound tends to `0`.  Every
consumer of `KPointNoExcWith` / `Roots` / `Depth` / `AllWith` is therefore vacuous until the
hypothesis is rethreaded onto `CastingOut.KPointNoExcAtWith`. -/
alias hall_kpoint_noexc_false := NormalNumbers.CastingOut.not_kPointNoExcWith_const_one

/-- **HALL: "the named open problem" `TwoPointNaturalCorrelationNoExc`** (`falseAsStated`,
2026-09-25).  The `Prop` the whole `C3MrtNoExc` chain and the `D = 2` natural-density rung were
stated over is not open: the constant-one witness refutes it, because its non-pretentiousness
hypothesis is free (`hall_tt_nonpretentious_vacuous`).  Same for
`KPointNaturalCorrelationNoExc 2` (`not_kPointNaturalCorrelationNoExc`). -/
alias hall_two_point_noexc_false :=
  NormalNumbers.CastingOut.not_twoPointNaturalCorrelationNoExc

/-- **HALL: a Lebesgue-measured exceptional set of scales** (`vacuous`, 2026-09-25).
`TwoPointNaturalCorrelation` charged its exceptional set `E ⊆ ℝ` by `∫_E t⁻¹` while asking the
conclusion only at integer scales, so `E = ℕ ∩ [√X, X]` is free and the whole `Prop` is
*provably true* and empty.  The faithful cost is a count of dyadic scales
(`CastingOut.TwoPointDyadicCorrelation`), under which the all-scales set is inadmissible
(`full_exceptional_set_not_admissible`). -/
alias hall_lebesgue_exceptional_scales :=
  NormalNumbers.CastingOut.twoPointNaturalCorrelation_trivially_true

/-- **HALL: TT Theorem 3.1(i) with a Lebesgue-measured exceptional set** (`vacuous`,
2026-10-02).  The frozen `TTEquidistributedCorrelation` repeats the case-(ii) defect: `E ⊆ ℝ`
charged by `∫_E t⁻¹`, conclusion asked only at natural `N`, so `E = ℕ ∩ [√X, X]` is free and the
`Prop` is provably true.  The Erdős #257 base-2 headline conditional on it is therefore the
unconditional statement.  Repair: `CastingOut.TTEquidistributedDyadic`. -/
alias hall_tt_equidistributed_vacuous :=
  NormalNumbers.CastingOut.ttEquidistributedCorrelation_trivially_true

/-- **HALL: a constant-fraction saving on every dyadic block** (`falseAsStated`, 2026-09-25).
Lap 112 reduced the wide archimedean debt to `WideBlockSaving κ`: a saving `1 − κ` on *every*
dyadic block of the twisted prime sum.  FALSE for every `κ > 0`, and structurally so — the top
block of the truncation at `X²` can be a **singleton**, whose weighted sum has norm exactly its
own mass.  Witness `X = 16/5`, `⌈X²⌉₊ = 11`, `j = 3`, block `{11}`.  Repaired as
`CastingOut.WideBlockSavingBand`, which asks for the saving only on complete blocks in a band
(`band_block_complete`, `witness_block_above_band`). -/
alias hall_wide_block_saving_false := NormalNumbers.CastingOut.not_wideBlockSaving

/-- **HALL: the reciprocal-free initial-segment form** (`falseAsStated`, 2026-09-25).
Lap 113's Abel transfer asked for the saving on *every initial segment* `p < m` of every block
(`WideBlockPartial κ`).  FALSE for every `κ > 0`: at `X = 3`, `j = 1`, `m = 3` the segment is the
singleton `{2}` and its character sum has norm exactly `1`.  Abel is sound; what it consumes is
not. -/
alias hall_wide_block_partial_false := NormalNumbers.CastingOut.not_wideBlockPartial

/-- **HALL: the "purely geometric" pairing endpoint** (`falseAsStated`, 2026-09-25).
Lap 114 reduced the debt to `BlockPhasePairing d`: on every initial segment of every block, the
`χ`-surviving primes admit an injective self-map with separated twist phases.  FALSE for every
`d < 1`: an injective self-map of a **singleton** is the identity, and a unit vector is never
separated from itself (`Re(u · conj u) = ‖u‖² = 1`).  So `conjC3_of_geom_input_pairing` — the
lap-114 headline — is vacuous; the pairing *bound* `norm_sum_le_of_pairing` remains true and
reusable. -/
alias hall_block_phase_pairing_false := NormalNumbers.CastingOut.not_blockPhasePairing

/-- **HALL: a CONSTANT bottom threshold for the banded block saving** (`falseAsStated`,
2026-09-25).  The repaired `WideBlockSavingBand J Jtop κ` asks for a constant-fraction saving on the
dyadic blocks of a band; lap 116 shows the bottom of that band cannot be a constant.  On a
**two-prime** block `{p,p'}` the twist `t = 2π/log(p'/p)` makes the two phases COINCIDE, so the
block sum has norm exactly its mass and no `κ > 0` saving holds — and `|t| ≤ X²` is permitted by the
wide range, so `X` can always be taken large enough.  Blocks `j = 1,2,3` are `{2,3}`, `{5,7}`,
`{11,13}`, which refutes every `J₀ ≤ 3`.  The honest statement therefore carries a threshold that
GROWS with `X`, whose cost is paid by `blockBandCost_of_log_bound` (only the `log` of the threshold
is charged).  For `J₀ ≥ 4` the blocks hold `≥ 3` primes, exact alignment is impossible (`ℚ`-
independence of `log p`) and near-alignment needs Kronecker — a conjecture, not a claim. -/
alias hall_const_band_threshold_false :=
  NormalNumbers.CastingOut.not_wideBlockSavingBand_const_le_three

/-- **HALL: uniform casting-out law (C1 draft)** (`falseAsStated`, 2026-09-23).
The first draft of C1 asked that window digit sums of `G4` be uniform mod `b − 1`.  No normal
number satisfies that: each digit value contributes `ζ^d` summing to `1`, not `0`, so the
normal law is `1/(b−1) + b^{−L}((b−1)[r=0] − 1)/(b−1)` (in base 3 a digit is even with
probability 2/3).  C1 was restated as `CastingOut.CastLaw`. -/
alias hall_uniform_casting_out := NormalNumbers.CastingOut.not_castUniform_of_isNormal

/-- **HALL: Mahler block-occurrence analogue** (`vacuous`, 2026-09-27).
Wall's 1949 thesis theorem — `q * x + r` is normal in base `b` whenever `x` is and `q ≠ 0`,
`r` are rational — says that no choice of rational multiplier can make a normal number
abnormal, so a "pick a multiple" normality statement carries no information.  Formerly a
`.cited` prose row; now a theorem of this build. -/
alias hall_mahler_block_occurrence := NormalNumbers.isNormal_rat_mul_add

/-! ## 3. Tier `frozen` — precise statements, undischarged

No proofs and no `sorry`: a frozen row pins down *what was claimed*, so that a future session
arguing about the hall argues about a Lean statement rather than a paraphrase. -/

/-- A criterion is a **restatement** of its target when the two are logically equivalent.
The register's `restatement` rows assert this shape; most are `Tier.cited` because their
objects are not formalized. -/
def IsRestatement (criterion target : Prop) : Prop := criterion ↔ target

/-- A criterion is **vacuous for** a family when every member satisfies it, so that it
separates nothing within the family. -/
def VacuousFor {α : Type*} (criterion : α → Prop) (family : α → Prop) : Prop :=
  ∀ a, family a → criterion a

/-- ✅ **DISCHARGED: the Walsh / parity criterion** (2026-09-20, NOT a hall — recorded here
because the maze's point is that the register and the frontier live in one checkable place).

`Walsh.isNormalSequence_two_iff_parityMean`: binary normality **is** the vanishing of every
nonempty parity correlation.  Both directions proved the same day the node was frozen.
Sufficiency runs through the exact Hadamard expansion of a block indicator; necessity through
the inverse transform, indexing binary words by their one-sets so that the orthogonality
`∑_T (-1)^{|S ∩ T|} = 0` falls out of the same product collapse.

So the digit dual now stands beside `equidistributed_of_weyl` on the circle side, and the
programme has Weyl's criterion and Walsh's criterion in one build.

⚠️ What this does NOT license is the sector identification: see the refuted row "G4 sectors
as digit characters" below.  The criterion is a theorem about an *arbitrary* binary sequence
and says nothing about where the digits came from. -/
alias walsh_criterion := NormalNumbers.Walsh.isNormalSequence_two_iff_parityMean

/-- ✅ **DISCHARGED: the digit-character criterion in every base** (2026-09-20, same day).

`WalshBase.isNormalSequence_iff_digitMean_zeta`: for a base-`b` digit sequence, normality
**is** the vanishing of every nontrivial character mean of `(ℤ/b)^L`, for every `L`.  The
`±1` of the binary case becomes `exp(2πi/b)`; the product collapse becomes the geometric sum
`∑_{j<b} x^j` at a `b`-th root of unity (`sum_inv_char_mul_char`); the powerset of offset
sets becomes `Finset.univ` on `Fin L → Fin b`; `Finset.prod_add` becomes `Fintype.prod_sum`.
Same skeleton, same exactness, no truncation term. -/
alias walsh_criterion_base := NormalNumbers.WalshBase.isNormalSequence_iff_digitMean_zeta

/-- 🔗 **Wiring: base two of the general criterion IS `Walsh.lean`.**  Proved directly (no
digit hypothesis, no pass through normality): `zeta 2 = -1`, the parity character of `S` is
the digit character at the indicator index `kOf L S`, and every `k : Fin L → Fin 2` is such
an indicator.  Recorded so the question "do the two files agree at `b = 2`?" is never
re-litigated. -/
alias walsh_two_files_agree := NormalNumbers.WalshBase.parityMean_criterion_iff_digitMean_criterion

/-- **HALL: log-averaged casting-out via the Elliott ledger (E2)** (`wall`, 2026-10-04).
Given the ledger's single input, the log twin of the C1 pair leaf is EQUIVALENT to the log
decoupling, so consuming `TwoPointElliottLog` removes none of the crux: it all sits in
`WeightDecoupleLog`, growing-depth Elliott with trivial product.  The 2026-09-24 swing
(`SwingC1Log`) reached the same verdict in a docstring only; this row makes it findable. -/
alias hall_logavg_casting_out :=
  NormalNumbers.LogCastingOut.twoPointWeightedLog_iff_weightDecoupleLog_of_zetaExponent

/-- **HALL: the log rung is a natural-average statement in disguise** (`refuted`, 2026-10-04).
It is not: `dyadicBit` has log digit frequency `1/2` and no natural digit frequency. -/
alias hall_log_rung_distinct := NormalNumbers.LogCastingOut.not_tendsto_natFreq_dyadicBit

/-! ## 4. The register

One entry per walked hall.  `Tier.kernel` rows are the aliases and theorem of §2; the rest
carry their evidence as a file pointer.  Sorted by area, newest campaigns first.

⚠️ Read the `tier` field before quoting a row.  Only `Tier.kernel` rows are machine-checked. -/

/-- Every hall this programme has walked and closed.  Never delete a row: a re-opened hall
keeps its row and gains a note (see `hdom` and the tower-separation wall, both REVERSED). -/
def register : List Hall := [
  ⟨"(BL) bias-loss criterion",
   "Prove G4 normality via a per-band feedback-below-dissipation ledger",
   .restatement, .cited,
   "(BL) is equivalent to uniform vanishing of the truncated middle-range means, i.e. the target one prime-cut earlier",
   "projects/normal-numbers-fable-verdict-2026-09-19.md §1", "2026-09-19"⟩,
  ⟨"per-band contraction",
   "Require feedback below dissipation in each active prime band",
   .refuted, .cited,
   "The one-site control z^omega(n+1) violates it at every N, so no such criterion can be true",
   "same leaf §2", "2026-09-19"⟩,
  ⟨"late-band regeneration as feedback",
   "Treat the late-band climb of |a_P| as arithmetic feedback needing a bound",
   .refuted, .cited,
   "It is the Selberg-Delange size budget e^gamma/|Gamma(i)| = 3.41, present identically in a problem whose answer is a theorem",
   "same leaf §2", "2026-09-19"⟩,
  ⟨"OneSiteRatioBounded (CRT form)",
   "Bound the leading one-site mean by the CRT prime prefix",
   .falseAsStated, .cited,
   "At z = -1 the prefix is identically 0 from p = 2; the honest scale is (log P)^(Re z - 1)",
   "same leaf §2c", "2026-09-19"⟩,
  ⟨"signed sum (7)",
   "Drive the exact signed error decomposition to zero as the criterion",
   .restatement, .cited,
   "Once model and far tail are controlled it is equivalent to the cancellation being sought",
   "projects/normal-numbers-prime-peeling-audit-2026-09-19.md §3", "2026-09-19"⟩,
  ⟨"absolute propagated budget B",
   "Require the absolute propagated budget to vanish",
   .refuted, .cited,
   "An explicit four-point dyadic example has EF = 0 while B tends to 2/3, killing universal necessity",
   "same audit §3.1", "2026-09-19"⟩,
  ⟨"free-count sparse constructions",
   "All-primes blocks, residue classes, thin subsets as density-zero sets with divergent reciprocal sum",
   .refuted, .cited,
   "Without prime counting the only count bound is a fraction of the integers, giving mass rate dL/L^2 which converges",
   "HANDOFF-2026-09-20-sparse-subset-lap.md", "2026-09-20"⟩,
  ⟨"elementary Mertens / Brun-Titchmarsh",
   "Supply the sparse-set count without PNT",
   .refuted, .cited,
   "Mertens O(1/L) error swamps the block mass; Brun-Titchmarsh bounds from above while the binding constraint is mass from below",
   "same handoff", "2026-09-20"⟩,
  ⟨"old Good.sep",
   "The earlier separation field on Good in the sparse wiring",
   .falseAsStated, .kernel,
   "eps_range and sep are jointly unsatisfiable at i = 0; the repair is 1 <= i",
   "alias hall_good_sep", "2026-09-20"⟩,
  ⟨"T_E sample-entropy transfer",
   "Bridge the sample-entropy theorems to ordinary digit frequencies",
   .falseAsStated, .kernel,
   "maskedReal G4 meets the exact premise at every scale yet at most a quarter of its digits are 1",
   "alias hall_T_E", "2026-09-14"⟩,
  ⟨"any digit-local sample premise",
   "T_S, T_mix, or any property of the joint sample laws forcing normality",
   .vacuous, .cited,
   "The sample is digit-local and reads density <= 1/4 < 1/2, so any satisfiable S-local premise admits a non-normal mask",
   "HANDOFF-2026-09-14-entropy-lap9.md", "2026-09-14"⟩,
  ⟨"averaging repair over families",
   "Repair the transfer by averaging translated grids, any family, any scales, any scale pairs",
   .refuted, .cited,
   "Multipliers are pinned to a progression by the interface, so the read-set counting bound closes at L/8 < L/2",
   "HANDOFF-2026-09-14-entropy-lap13.md", "2026-09-14"⟩,
  ⟨"E-T8 chunking",
   "Replace repetition by disjoint certified chunks per scale",
   .refuted, .kernel,
   "A chunk is certifiable only if its digit count exceeds the total entropy deficit; there are never enough",
   "alias hall_chunking", "2026-09-14"⟩,
  ⟨"certified-granule assembly",
   "Read the sampled digits in position order as concatenated certified granules",
   .wall, .kernel,
   "The first non-vacuous granule of scale i+1 outreads everything scale i produced, however cut",
   "alias hall_granularity_wall", "2026-09-14"⟩,
  ⟨"pointwise frequency from deficit",
   "Derive an o(1) frequency bound at a fixed position vector",
   .refuted, .kernel,
   "A one-bit-per-window deficit still admits a probability-zero pattern at a fixed position vector",
   "alias hall_pointwise_deficit", "2026-09-14"⟩,
  ⟨"scale-gap repairs (four)",
   "Skip the head, certified annuli, pad the history, raise the previous rung",
   .refuted, .cited,
   "The separation is a tower; every repair is polynomial or P0-bounded, and skipping merely relocates the gap",
   "HANDOFF-2026-09-14-entropy-truncated-scale.md", "2026-09-14"⟩,
  ⟨"tower-separation wall (REVERSED)",
   "Believed the schedule-only read of G4 was blocked by tower separation",
   .refuted, .cited,
   "REVERSAL: the separation was an artifact of pinning m1 to K; a two-dimensional (K,j) ladder tiles the gap and the normal number landed",
   "projects/normal-numbers-entropy-review-2026-09-14.md", "2026-09-14"⟩,
  ⟨"delta_K asymptotic sharpening",
   "Sharpen the entropy deficit order via a better determinant bound",
   .wall, .cited,
   "The log-spectrum is centred, so the sqrt(K) is a genuine CLT-scale spread; only the constant halves",
   "HANDOFF-2026-09-14-entropy-lap33.md", "2026-09-14"⟩,
  ⟨"Mprod / primorial for a P0 bound",
   "Bound P0 below via the product of squared moduli or the primorial",
   .refuted, .cited,
   "A log count: log Mprod(K+4) is about K^6K against the required K^8K",
   "HANDOFF-2026-09-15-entropy-lap125.md", "2026-09-15"⟩,
  ⟨"base-2^k step 3 read-class split",
   "Split the certificate over read classes to transport normality to base 2^k",
   .refuted, .cited,
   "The needed family is neither a sample-time set nor a coordinate set; three repairs all fail",
   "ROUTE-ESCALATION-2026-09-15-base2k-step3.md", "2026-09-15"⟩,
  ⟨"Wall + Maxfield for base 2^k",
   "Get IsNormal 4 from IsNormal 2 via uniform distribution and exponential sums",
   .parked, .cited,
   "The Fourier route yields only the sum over classes, the same gap just refuted; superseded by proving the b to b^K theorem outright",
   "HANDOFF-2026-09-15-entropy-lap126.md", "2026-09-15"⟩,
  ⟨"axis-skeleton sharpening",
   "Shrink skel to the polynomial axis skeleton to sharpen the density rate",
   .refuted, .kernel,
   "pairWit is balanced, nonzero, and vanishes on all of skel1",
   "alias hall_axis_skeleton", "2026-09-15"⟩,
  ⟨"coprimality sharpening",
   "Use pairwise coprimality to shrink the family count",
   .refuted, .cited,
   "Injectivity gives only dmin^H, weaker than the MDF bound by about K/4 in the exponent",
   "HANDOFF-2026-09-15-S-lap166.md", "2026-09-15"⟩,
  ⟨"counting-based rate sharpening",
   "Exhaustively count balanced families to show the skel bound is loose",
   .refuted, .cited,
   "The bound is loose only by a constant factor in the exponent, which moves the coefficient, not the rate",
   "PROBE-2026-09-15-balanced-count.md", "2026-09-15"⟩,
  ⟨"counting bound below w = 8E+5",
   "Extend the confinement counting bound to narrow blocks",
   .vacuous, .cited,
   "Below that width the counting bound says nothing: a block carries fewer atoms than skel needs",
   "HANDOFF-2026-09-15-S-lap166.md", "2026-09-15"⟩,
  ⟨"grouped sampling escape",
   "Cut the joint sample into blocks to escape confinement",
   .wall, .cited,
   "The design prose dropped the family factor; restoring it forces 8KG <= K^2+1, so confinement is untouched",
   "STATUS.md review lap 166", "2026-09-15"⟩,
  ⟨"normality on the quantized sampler",
   "Force normality from a quantized arithmetic sample of G4",
   .wall, .kernel,
   "A digit-local sampler forces normality iff it reads a density-one position set; this schedule reads far less",
   "alias hall_quantized_normality", "2026-09-14"⟩,
  ⟨"base two, §4D design family",
   "Run the disjunctivity machine at b = 2",
   .refuted, .kernel,
   "Any line-sum-annihilating array has L1 mass >= 2^K, so row mass is 1 where the design needs < 1; no re-tuning of Y escapes",
   "alias hall_base_two_design", "2026-09-14"⟩,
  ⟨"phaseOscillation / base-two irrationality",
   "The old base-two prime-Lambert irrationality endpoint",
   .parked, .cited,
   "The same base-two wall, and additionally superseded in the literature by Tao-Teravainen",
   "ESCALATION-g4.md §5", "2026-09-16"⟩,
  ⟨"B6 two-stream cylinder nesting",
   "Build x and z as interleaved CF streams, each stage appending a freq-good steer block",
   .refuted, .cited,
   "The freq-good measure budget forces blocks to grow super-exponentially in the stage index",
   "OBSTRUCTION-2026-08-24-block-measure-budget.md", "2026-08-24"⟩,
  ⟨"navigate-then-select",
   "Place a short prefix into the target first, then frequency-select inside",
   .refuted, .cited,
   "The placement prefix is frequency-uncontrolled and is the majority of the block, diluting goodness",
   "same obstruction", "2026-08-24"⟩,
  ⟨"cfK-control as the fix",
   "Use the cfK selection lemmas to repair the block bound",
   .refuted, .cited,
   "They fix only the resolution cost, not the measure budget; the obstruction survives them",
   "same obstruction", "2026-08-24"⟩,
  ⟨"digit-capped steering",
   "Cap CF digits, fixed then growing, to force the geometric block bound",
   .refuted, .cited,
   "Fixed cap gives badly approximable hence not CF-normal; growing cap makes log cfK super-linear and the bound fails",
   "PENDING_WORK.md route correction", "2026-08-28"⟩,
  ⟨"psi-pushed Chebyshev variance",
   "Bound the cylinder-restricted second moment of the pushed block count",
   .falseAsStated, .kernel,
   "On a deep cylinder the pushed count is near-constant, so the moment about the global mean is quadratic; a restricted Chebyshev must centre conditionally",
   "alias hall_psi_pushed_variance", "2026-08-25"⟩,
  ⟨"conditional-at-wz z-route",
   "Discharge the z-good threshold at the base cylinder and transfer by digit agreement",
   .wall, .cited,
   "Density-versus-coverage: a bounded bridge empties the transfer range, an unbounded one forces an exponential threshold",
   "PENDING_WORK.md", "2026-08-25"⟩,
  ⟨"post-hoc deep-cylinder witness",
   "Select a z-good point inside the deep x-cylinder and transfer",
   .wall, .cited,
   "Scale-regime obstruction: the z-good threshold is exponential in the block while the transfer range is linear, so the interval is empty",
   "PENDING_WORK.md Z-II", "2026-08-25"⟩,
  ⟨"target-shrink inside the hull",
   "Shrink the freq-good steer target below the full cylinder hull",
   .refuted, .cited,
   "It breaks the mass balance the selection needs",
   "STATUS.md", "2026-08-25"⟩,
  ⟨"L4 self-hull steer",
   "Steer x into its own hull to get linear blocks",
   .wall, .cited,
   "The absolute regularization term kills the scaling, making the block count exponential",
   "PENDING_WORK.md", "2026-08-24"⟩,
  ⟨"SchedABlockLinear",
   "Prove the schedule block-linearity Prop from the spec",
   .parked, .cited,
   "schedA is a Classical.choose recursion whose spec carries no block upper bound, so the Prop is choice-opaque",
   "HANDOFF-2026-09-01-cfsched-prop-nodes.md", "2026-09-01"⟩,
  ⟨"hdom dominance (RE-OPENED)",
   "Prove the B6 crux through a dominance hypothesis",
   .refuted, .cited,
   "REVERSAL: refuted 2026-08-24 as steer blocks are linear in the word, then found REMOVABLE 2026-08-27; kept as a row because the closure itself was wrong",
   "STATUS.md and PENDING_WORK.md 2026-08-27", "2026-08-27"⟩,
  ⟨"goodC suffices (Khinchin)",
   "Derive the log-digit average from frequencies plus the goodC total-mass bound",
   .refuted, .cited,
   "Frequencies plus total mass cannot supply the uniform tail control; a frequencies-only counterexample exists",
   "HANDOFF-2026-08-24-0208.md", "2026-08-24"⟩,
  ⟨"naive Khinchin assembly",
   "Tie the log-zone slack to the schedule epsilon, letting the cutoff grow per level",
   .refuted, .cited,
   "A per-level bound at a growing cutoff can never transfer to a fixed external cutoff",
   "HANDOFF-2026-08-24-lap9.md", "2026-08-24"⟩,
  ⟨"Khinchin from frequencies alone",
   "Reach CF-normal plus Khinchin-typical from digit frequencies",
   .refuted, .cited,
   "The planted-digit counterexample in KHINCHIN.md is provably insufficient",
   "projects/normal-numbers.md", "2026-08-24"⟩,
  ⟨"Fermat-quotient coordinate",
   "Use the mod-p checksum as an external arithmetic feed into the ln 2 digit tower",
   .restatement, .cited,
   "The bridge identity makes the quotient cancel, so the test reduces to agreement with the true digits: one bit total",
   "docs/tower-2026-08-29.md", "2026-08-29"⟩,
  ⟨"e kick-barrier",
   "Force long runs of e to survive factorial-threshold kicks",
   .refuted, .cited,
   "Probe: crossed kicks are population-generic and the crossing term moves an integer, invisible on the circle",
   "docs/tower-2026-08-29.md", "2026-08-29"⟩,
  ⟨"KickBootstrap",
   "Self-improving density of the kicked orbit to cascade a seed to full density",
   .parked, .cited,
   "No seed density exists to bootstrap; it is the times-2-times-3 gap in dynamics clothing",
   "docs/tower-2026-08-29.md", "2026-08-29"⟩,
  ⟨"T3 ShortOrbitCancel",
   "Block-level equidistribution of the readout segments via exponential sums over multiplicative subgroups",
   .wall, .cited,
   "BGK-style bounds reach segments of length q^delta; our segments have length log q, sub-polynomial and below every known technique",
   "docs/tower-2026-08-29.md", "2026-08-29"⟩,
  ⟨"CRT stacking to a sqrt(n) threshold",
   "Pin the surrogate numerator via residues for all small primes",
   .refuted, .cited,
   "The quotient needed to access the residues IS the digit prefix, so every mod-p handle re-imports the unknown",
   "docs/new-conjectures-2026-08-29.md", "2026-08-29"⟩,
  ⟨"LnTwoLatticeAvoid (alien R1)",
   "Freeze a lattice-avoidance node claimed not to pass through Diophantine input",
   .restatement, .cited,
   "Proved equivalent to dyadic separation; the window position depends on ln 2 and collapses onto the separation quantity",
   "docs/diophantine-wall.md", "2026-08-29"⟩,
  ⟨"SliverEscape is Diophantine-free",
   "Treat the sliver and kick family as a Diophantine-free front",
   .refuted, .cited,
   "The lattice dig showed the run-window content is Diophantine; soft dynamics is measure-level and says nothing pointwise",
   "docs/diophantine-wall.md", "2026-08-29"⟩,
  ⟨"Lagarias footnote-1",
   "Prove density-one agreement of true and surrogate digits as a fresh target",
   .restatement, .cited,
   "The mismatch event collapses onto the same separation quantity, a density costume for the wall",
   "docs/lnTwo-kick-blueprint.md", "2026-08-29"⟩,
  ⟨"beta below 9 (run cap)",
   "Sharpen the unconditional ln 2 run cap toward 5n",
   .wall, .cited,
   "The pinned mathlib has no PNT and Chebyshev tops out at the bound already used",
   "docs/lnTwo-kick-blueprint.md", "2026-08-31"⟩,
  ⟨"beta = 8 sharpening",
   "Sharpen the run bound to exponent 8 for this method",
   .refuted, .cited,
   "The method needs a ratio constant below what the available lcm bound supplies",
   "HANDOFF-2026-08-29-lane2-target3-done.md", "2026-08-29"⟩,
  ⟨"Hypothesis A as weaker",
   "Use Bailey-Crandall Hypothesis A as a strictly weaker input than normality",
   .restatement, .cited,
   "Lagarias: the surrogate orbit shadows the true orbit, so hypothesis and conclusion are one statement in two coordinate systems",
   "docs/lit-sweep-2026-08-29.md", "2026-08-29"⟩,
  ⟨"kick-floor-only lemma",
   "Conclude equidistribution-or-finite from a kick magnitude floor alone",
   .refuted, .cited,
   "Lagarias adversarial family survives that floor, so conclusions must stay at the structure level",
   "docs/lit-sweep-2026-08-29.md", "2026-08-29"⟩,
  ⟨"irrationality-measure route",
   "Exclude the run-coincidence window using measure bounds",
   .wall, .cited,
   "Measures exclude widths at scale q^(2-mu); the window has width below one integer, structurally out of reach",
   "docs/lit-sweep-2026-08-29.md", "2026-08-29"⟩,
  ⟨"2-adic Kurschak trick",
   "A 2-adic vanishing identity to control the ln 2 surrogate",
   .refuted, .cited,
   "The relevant sum is identically zero in the 2-adics, so the trick carries no information here",
   "docs/lit-sweep-2026-08-29.md", "2026-08-29"⟩,
  ⟨"(mu-1)n run corollary as novel",
   "Claim the measure-to-run-bound corollary for ln 2 as new",
   .priorArt, .cited,
   "Rivoal 2008 has the bits-counting statement; the corollary is folklore",
   "docs/lit-sweep-2026-08-29.md", "2026-08-29"⟩,
  ⟨"first quantitative digit statement",
   "Present the Tier-1 run bound as new mathematics",
   .priorArt, .cited,
   "It is a folklore corollary of the irrationality measure; only formalization-first is defensible",
   "docs/alien-review-2026-08-29.md", "2026-08-29"⟩,
  ⟨"Bugeaud-Kim complexity from mu",
   "Buy superlinear subword complexity for ln 2 from the irrationality exponent",
   .wall, .cited,
   "Nontrivial only below an exponent that is not known for log 2; complexity is the ceiling of all measure roads",
   "docs/lit-sweep-2026-08-29.md", "2026-08-29"⟩,
  ⟨"abc path A (non-Wieferich)",
   "Derive the run-bound node from abc plus known Fermat-quotient results",
   .wall, .cited,
   "Needs two open upgrades: density-one non-Wieferich, and prime-aspect equidistribution of the quotient",
   "docs/abc-sweep-2026-08-29.md", "2026-08-29"⟩,
  ⟨"abc path B (S-unit)",
   "Transfer the abc chain for powers to a transcendental constant",
   .wall, .cited,
   "The mechanism consumes S-unit and radical integer structure, which transcendental constants do not expose",
   "docs/abc-sweep-2026-08-29.md", "2026-08-29"⟩,
  ⟨"unrestricted-word adder collapse",
   "Let the greedy hunt pick any words when driving family entropy to zero",
   .vacuous, .cited,
   "It picks a known-recurring word, mechanically rediscovering the Adamczewski-Rampersad boundary",
   "docs/adder-collapse-hunt-2026-08-29.md", "2026-08-29"⟩,
  ⟨"factory to a single constant",
   "Get a singleton occurrence theorem out of the disjunction factory",
   .refuted, .cited,
   "A singleton clause needs a one-channel collapse, which has positive entropy; pinning an extra track never lowers it",
   "docs/adder-family-2026-08-29.md", "2026-08-29"⟩,
  ⟨"universal clauses to disjunctivity",
   "Accumulate universal word-in-channel clauses to entail that some channel is disjunctive",
   .refuted, .cited,
   "An explicit blocking pair satisfies every universal clause while no channel of the lattice is disjunctive",
   "docs/transversal-ceiling-2026-08-29.md", "2026-08-29"⟩,
  ⟨"universality-preserving methods",
   "Push universality-preserving channel methods up to disjunctivity",
   .wall, .cited,
   "Blocking pairs cap every such method strictly below disjunctivity",
   "projects/normal-numbers.md", "2026-08-30"⟩,
  ⟨"C1 two-elements-per-digit",
   "Headline that every ternary digit recurs in x or 2x",
   .priorArt, .cited,
   "It is exactly Berend-Boshernitzan 1994 M(3,1) = 2",
   "docs/mahler-sets-2026-08-29.md", "2026-08-29"⟩,
  ⟨"C4 / C5 / C8 as independent",
   "Count three further channel results as separate advances",
   .restatement, .cited,
   "Each is elementary, an immediate case split, or the digit-complement involution of the flagship",
   "docs/tower-novelty-audit-2026-08-29.md", "2026-08-30"⟩,
  ⟨"C2 one-multiplier-all-digits",
   "Claim the joint all-digits multiplier statement as new",
   .priorArt, .cited,
   "Mahler 1973 plus Berend-Boshernitzan already give a single small multiplier; only the collapse to a two-element set is ours",
   "docs/citation-sweep-2026-08-30.md", "2026-08-30"⟩,
  ⟨"float-prefilter negatives",
   "Gate exact SCC checks behind a float entropy threshold",
   .refuted, .cited,
   "Power iteration converges slowly, so true zeros read above the threshold and real collapses were silently discarded",
   "docs/mahler-sets-2026-08-29.md", "2026-08-29"⟩,
  ⟨"automaton no-k-set lower bounds",
   "Read a positive-entropy hunt result as a genuine minimality lower bound",
   .vacuous, .cited,
   "The automaton is a carry superset: a surviving symbolic path need not be realizable by any real x",
   "docs/mahler-sets-2026-08-29.md", "2026-08-29"⟩,
  ⟨"decimal digit-7 wall",
   "Run the exact automaton checker up to base 10",
   .wall, .cited,
   "State count is the binding constraint; the needed channel count is far beyond the exact checker",
   "docs/mahler-sets-2026-08-29.md", "2026-08-29"⟩,
  ⟨"restricted-class middle rung",
   "Restrict the quantifier to algebraic irrationals to beat the adversary bound",
   .vacuous, .cited,
   "A short true-carry analysis proved it for all irrationals, so the algebraicity restriction buys nothing",
   "docs/restricted-class-ladder-2026-08-29.md", "2026-08-29"⟩,
  ⟨"divisor-bound conjecture",
   "Conjecture the divisor construction is exact on the base-2^j family",
   .refuted, .cited,
   "A single computation at base 32 disagrees; the small-base agreement was a coincidence",
   "docs/mahler-exact-values-2026-09-07.md", "2026-09-07"⟩,
  ⟨"prime-base upper side",
   "Ask whether prime bases give the weak upper side of the Mahler bound",
   .refuted, .cited,
   "Exact values track a quadratic in the base, so the room is on the lower side and primes cannot move the universal constant",
   "docs/mahler-exact-values-2026-09-07.md", "2026-09-07"⟩,
  ⟨"universal constant below 1",
   "Chase a sharp constant strictly below 1",
   .refuted, .cited,
   "The density of smooth divisors pushes the ratio arbitrarily near 1, so the supremum is exactly 1 and unattained",
   "docs/mahler-universal-constant-is-one-2026-09-07.md", "2026-09-07"⟩,
  ⟨"constant-is-sharp as new",
   "Present that the constant cannot be lowered as this repo result",
   .priorArt, .cited,
   "Berend-Boshernitzan use the same smooth-divisor mechanism; only the fixed-k companion is added",
   "same doc", "2026-09-13"⟩,
  ⟨"orbit-free Mahler cycles",
   "Close a background cycle with all vertex conditions at exponent zero",
   .refuted, .cited,
   "At the maximum the monodromy is parabolic, pinning the scale, so the cost is only linear; the relevant column is empty for every prime checked",
   "PENDING_WORK.md", "2026-09-08"⟩,
  ⟨"multi-offset single background",
   "Use several offsets dividing p+1 for a uniform quadratic floor",
   .refuted, .cited,
   "When p+1 is twice a prime the available offsets collapse the bound to linear",
   "PENDING_WORK.md", "2026-09-08"⟩,
  ⟨"closed-form background at b = 2",
   "Look for a scaling beating the family-II constant",
   .refuted, .cited,
   "The drift is always odd at that junction, so the constant is parity, not slack",
   "PENDING_WORK.md", "2026-09-08"⟩,
  ⟨"drift minus one",
   "Use drift minus one for the one-junction certificate",
   .refuted, .cited,
   "Its trigger sits inside the bad zone, so the key condition fails for every parameter",
   "PENDING_WORK.md", "2026-09-08"⟩,
  ⟨"structural D dividing p+1",
   "Get a drift-one background in closed form from divisors of p+1",
   .refuted, .cited,
   "Every such divisor shares a factor with p+1, which kills drift one",
   "PENDING_WORK.md", "2026-09-08"⟩,
  ⟨"closed-form burst families",
   "Give the single-burst lower-bound family a closed form",
   .refuted, .cited,
   "All candidates are only linear in p: the higher digits kill them; existence is fine, the formula is the obstruction",
   "PENDING_WORK.md", "2026-09-08"⟩,
  ⟨"quarter target at k >= 2",
   "Carry the proved k = 1 constant up to higher k",
   .refuted, .cited,
   "Exact values at k = 2 exceed the target and climb; the shadow denominator can drop by the base when k >= 2",
   "PENDING_WORK.md", "2026-09-07"⟩,
  ⟨"no new idea required at k >= 2",
   "Extend the k = 1 stage argument as the kickoff promised",
   .falseAsStated, .cited,
   "If the base divides the denominator the shadow drops and the stage argument does not increase it",
   "HANDOFF-2026-09-07-mahler-quarter-k1.md", "2026-09-07"⟩,
  ⟨"exists_prime_nonresidue",
   "Find a prime in a short interval with a prescribed Legendre symbol",
   .parked, .cited,
   "Linnik and Burgess-Karatsuba strength: character sums over primes in an interval shorter than the modulus",
   "PENDING_WORK.md", "2026-09-08"⟩,
  ⟨"measure-theoretic non-disjunctive witness",
   "Build an absolutely non-disjunctive irrational from a positive-entropy measure",
   .refuted, .cited,
   "Host 1995: such a measure makes almost every point normal, hence disjunctive, in the other base",
   "docs/disjunctive-vs-normal.md", "undated"⟩,
  ⟨"Furstenberg-intersection route",
   "Squeeze multiplicatively independent forbidden-word sets via the intersection theorems",
   .wall, .cited,
   "Forbidding a long word costs almost no dimension, so the bound is toothless where it is needed",
   "docs/disjunctive-vs-normal.md", "undated"⟩,
  ⟨"Martin abnormal number as witness",
   "Reuse Martin absolutely abnormal number as a non-disjunctivity candidate",
   .refuted, .cited,
   "Its abnormality is a frequency excess, not a missing word",
   "docs/disjunctive-vs-normal.md", "undated"⟩,
  ⟨"Axiom Lambda as weaker",
   "Name a measure-positivity axiom as a strictly weaker route to disjunctivity",
   .restatement, .cited,
   "The Haar zero-one law makes positive measure equal the full circle, so the axiom equals the conclusion",
   "docs/conditional-disjunctivity.md", "undated"⟩,
  ⟨"carry-free attacks on Axiom C",
   "Exploit the quadratic relation symbolically and by digit counting",
   .wall, .cited,
   "In characteristic two squaring is Frobenius so the constraint trivializes; counting saturates and cannot see arrangement",
   "docs/conditional-disjunctivity.md", "undated"⟩,
  ⟨"dimension bounds imply Axiom M",
   "Derive quadratic-irrational disjunctivity from the intersection theorems",
   .wall, .cited,
   "A dimension bound can never exclude a single point, which is why the axiom must stay an axiom",
   "docs/conditional-disjunctivity.md", "undated"⟩,
  ⟨"pattern-side repetition threshold",
   "Push repetition-threshold results down to a specific recurring block",
   .wall, .cited,
   "They already sit at the sharp binary repetition threshold, where complexity arguments go silent",
   "docs/conditional-disjunctivity.md", "undated"⟩,
  ⟨"single-tail radix extraction",
   "Extract one genuine radix tail after cancelling K places",
   .refuted, .cited,
   "Extraction costs at least 2^K in integer coefficient mass, even after aggregating equal arguments",
   "projects/normal-numbers-carries-fourth-push-2026-09-13.md", "2026-09-13"⟩,
  ⟨"hexagon positivity / mean retention",
   "Use a hexagon mean-retention inequality as the cancellation engine",
   .falseAsStated, .cited,
   "Kernel-checked counterexamples: an exact witness has negative correlation with mean above one half",
   "docs/prime-lambert-irrationality.md", "2026-09-14"⟩,
  ⟨"single-coordinate carry isolator",
   "Isolate one coordinate of the carry tail for an independent cancellation test",
   .refuted, .cited,
   "Every compatible integer single-coordinate isolator cancelling K places has mass at least 2^K",
   "docs/prime-lambert-isolator-obstruction.md", "2026-09-14"⟩,
  ⟨"oscillation implies disjunctivity",
   "Infer disjunctivity from the growing affine signed oscillation",
   .refuted, .cited,
   "A base-four countermodel omitting a word satisfies the same oscillation at every fixed frequency",
   "projects/normal-numbers-disjunctivity-frontier-2026-09-14.md", "2026-09-14"⟩,
  ⟨"second Katai differencing",
   "Apply a second common shift after the first difference",
   .refuted, .cited,
   "The signed-multiset matching forces the two primes equal, so no second shift aligns two early places",
   "projects/normal-numbers-middle-primes-fable-handoff-2026-09-19.md", "2026-09-19"⟩,
  ⟨"typical-set shortcut",
   "Conclude that low-entropy measures concentrate on a small typical set",
   .refuted, .cited,
   "An explicit half-and-half measure has positive entropy but no small high-probability set; ergodicity is required",
   "docs/prime-lambert-affine-entropy-draft.md", "2026-09-14"⟩,
  ⟨"Omega-transfer by sparse edits",
   "Get the big-Omega result from the little-omega one by sparse digit edits",
   .refuted, .cited,
   "Sparse digit edits and zero-entropy corrections do not generally preserve disjunctivity",
   "docs/prime-lambert-disjunctivity-multiplicity.md", "2026-09-14"⟩,
  ⟨"full prime-incidence independence",
   "Approximate the joint prime-incidence law by the independent CRT model",
   .refuted, .cited,
   "Total variation tends to 1 at every fixed-power cutoff: actual integers have boundedly many band primes, the model does not",
   "projects/normal-numbers-full-sieve-obstruction-2026-09-13.md", "2026-09-13"⟩,
  ⟨"density-only coefficient transfer",
   "Assume editing coefficients on a density-zero set preserves normality",
   .refuted, .cited,
   "An explicit normal ternary series becomes nonnormal after doubling coefficients on a density-zero set",
   "projects/normal-numbers-carry-research-response-2026-09-13.md", "2026-09-13"⟩,
  ⟨"fixed-window conductor at depth",
   "Extend the fixed-window conductor cancellation to growing level",
   .wall, .cited,
   "A single-factor counterexample shows fixed-level cancellation gives no uniformity at growing depth",
   "projects/normal-numbers-conductor-frontier-2026-09-13.md", "2026-09-13"⟩,
  ⟨"periodic search for the prime cube",
   "Settle the K = 2 prime-cube correlation by searching periodic sequences",
   .vacuous, .cited,
   "Every periodic and limit-periodic sequence has a synchronized prime cube with nonzero correlation, so the search can never refute it",
   "projects/normal-numbers-prime-cube-k2-density-audit-2026-09-13.md", "2026-09-13"⟩,
  ⟨"Gowers positivity from the relations",
   "Build a nonnegative alternating average from the carry commutator relations",
   .wall, .cited,
   "Gowers positivity needs a closed cube of commuting transformations, which the relations do not supply",
   "projects/normal-numbers-carry-commutator-audit-2026-09-13.md", "2026-09-13"⟩,
  ⟨"phi-product density recurrence",
   "Prove or refute positive-density recurrence for the phi-product equation",
   .wall, .cited,
   "Neither theorem nor counterexample; the output is an exact fiber classification plus why energy and commuting-action routes stop",
   "projects/normal-numbers-phi-density-obstruction-2026-09-13.md", "2026-09-13"⟩,
  ⟨"sparse Stoneham relative as open",
   "Treated a sparse Stoneham-like series as a genuinely open normality target",
   .priorArt, .cited,
   "Vandehey 2019 Theorem 7.4 nested-denominator condition already covers it; we mistook the 2002 theorem limit for the literature frontier",
   "ROADMAP.md literature correction", "2026-09-13"⟩,
  ⟨"Stoneham base-6 as a new method",
   "Claim the base-6 disjunctivity proof as a new technique",
   .priorArt, .cited,
   "It is a short weighted adaptation of Hertling separated-block and residue-grid method with one extra lemma",
   "projects/stoneham-prior-art-audit-2026-09-13.md", "2026-09-13"⟩,
  ⟨"Hertling direct substitution",
   "Derive the constant as a literal corollary by substituting parameters",
   .refuted, .cited,
   "The missing factor varies with the summand and no fixed integer base can absorb it",
   "same audit", "2026-09-13"⟩,
  ⟨"Vandehey Lemma 3.2",
   "Rely on it when formalizing the continued-fraction differencing route",
   .falseAsStated, .cited,
   "It cites a theorem that Airey-Mance refute on non-compact spaces, and the CF alphabet is non-compact",
   "projects/normal-numbers.md", "2026-08-24"⟩,
  ⟨"Fisher-Schmidt as the solution",
   "Read it for a Theorem 3.1 analogue with continuous fibers",
   .restatement, .cited,
   "Its fiber is finite and ergodicity is free only because the cover has finite volume, the very hypothesis that dies here",
   "projects/normal-numbers.md", "2026-08-24"⟩,
  ⟨"BBP extraction for pi normality",
   "Use the base-16 digit formula to get normality or disjunctivity of pi",
   .wall, .cited,
   "The reduction holds but the orbit fails: four modulus families at once and a fresh modulus every step",
   "projects/normal-numbers.md", "2026-08-25"⟩,
  ⟨"Mahler block-occurrence analogue",
   "Look for a normality version of the pick-a-multiple statement",
   .vacuous, .kernel,
   "Wall 1949: normality survives rational multiplication, so picking a multiplier says nothing",
   "alias hall_mahler_block_occurrence", "2026-09-27"⟩,
  ⟨"finite C2 implies slow growth",
   "Assume the second sieve-constant growth hypothesis follows from finiteness",
   .falseAsStated, .cited,
   "A doubly exponential constant is an explicit counterexample to the prose claim",
   "projects/normal-numbers-flexible-block-schedule-2026-09-20.md", "2026-09-20"⟩,
  ⟨"G4 sectors as digit characters",
   "Identify G4 base-4 digit characters with omega-characters, reading the SD and Chowla sectors as that split",
   .refuted, .cited,
   "Carries are not a perturbation: the digit-parity to omega-parity correlation decays (0.575, 0.399, 0.238 at N = 50k, 200k, 800k) while the disturbed fraction rises, so the two become asymptotically uncorrelated",
   "experiments/g4_carry_parity.py and its hand-computed test; DESIGN-2026-09-20-walsh-weyl-bridge.md §4", "2026-09-20"⟩,
  ⟨"T3c critical-slice run cap",
   "Cap base-6 digit runs at the critical slice via the two-log separation engine",
   .provableEmpty, .kernel,
   "The cap exceeds 16000 while the true run is 0 or 1 in every block computed; provable in one wiring lap, and worthless",
   "theorem hall_t3c_block5_true_run_is_one", "2026-09-20"⟩,
  ⟨"alpha_{2,3} abelian-normal in base 6",
   "Hope that the base-2-normal Stoneham constant is still abelian-normal in base 6, giving a natural separation",
   .refuted, .kernel,
   "The base-6 expansion has forced zero gaps on (3^m, 1.16*3^m], so freq(0) reaches 8/33 > 1/6 and it is not even simply normal",
   "alias hall_stoneham_six_abelian", "2026-09-23"⟩,
  ⟨"x3 abelian lifting",
   "Hope that abelian-normality of x and of 3x together force genuine normality of x",
   .parked, .frozen,
   "The hexSwap example does not refute it (3*xi is not abelian: probe z about 84 at L = 1), but a dimension count makes a single multiplier implausible; the odd-multiplier version is open",
   "Failures.TimesThreeLifting", "2026-09-23"⟩,
  ⟨"TT (3.3) as TTNonPretentious",
   "Assume TT's non-pretentiousness hypothesis with the implied constant existentially quantified after X and L",
   .vacuous, .kernel,
   "Every summand of ttPretentiousSum is nonnegative, so A = 1/L discharges it for every 1-bounded g including g = 1; TT's constant is absolute, and the faithful restatement also needs Dirichlet characters and twists up to X squared",
   "alias hall_tt_nonpretentious_vacuous; restatement CastingOut.TTNonPretentiousUnif", "2026-09-25"⟩,
  ⟨"K-point no-exceptional-set input as stated",
   "Take KPointNoExcWith cK CstK K as the single open input of the C3/MRT headline",
   .falseAsStated, .kernel,
   "At K = 2 with both factors the constant 1, W = 1, shifts 1 and 2, X = exp L and N = ceil sqrt X the progression mean is exactly 1 while the claimed bound CstK 2 times L to the minus cK 2 tends to 0",
   "alias hall_kpoint_noexc_false; repaired input CastingOut.KPointNoExcAtWith", "2026-09-25"⟩,
  ⟨"the named open problem TwoPointNaturalCorrelationNoExc",
   "Carry the exceptional-set-free form of TT 3.1(ii) as the one named open input of the D = 2 rung",
   .falseAsStated, .kernel,
   "Its non-pretentiousness hypothesis is free, so the constant-one witness refutes it outright; the same holds for KPointNaturalCorrelationNoExc at K = 2",
   "alias hall_two_point_noexc_false", "2026-09-25"⟩,
  ⟨"Lebesgue-measured exceptional set of scales",
   "Charge TT's exceptional set of scales by the Lebesgue integral of 1/t over a measurable subset of the reals",
   .vacuous, .kernel,
   "The conclusion is only asked at integer scales, so E = the integers in [sqrt X, X] has zero cost and excludes every scale: the Prop is provably true and empty",
   "alias hall_lebesgue_exceptional_scales; faithful cost CastingOut.TwoPointDyadicCorrelation", "2026-09-25"⟩,
  ⟨"TT 3.1(i) with a Lebesgue-measured exceptional set",
   "Carry Tao-Teraeväinen Theorem 3.1(i) as TTEquidistributedCorrelation, the one cited input of the Erdos 257 base-2 prime-subset headline",
   .vacuous, .kernel,
   "Same defect as the case-(ii) row: E is charged by the integral of 1/t but the conclusion is asked only at natural N, so E = the naturals in [sqrt X, X] is free; the Prop is a theorem, N6 (VeryLargeCov from TT) cannot be derived from it, and the headline conditional on it is unconditional base-2 disjunctivity. REOPEN IF: the input is restated with counted dyadic scales (TTEquidistributedDyadic) and the headline re-frozen on it",
   "alias hall_tt_equidistributed_vacuous; module LiteratureTTEquidistributedDefect; repair CastingOut.TTEquidistributedDyadic", "2026-10-02"⟩,
  ⟨"uniform casting-out law (C1 draft)",
   "Assume a normal number's window digit sum is uniform mod b-1",
   .falseAsStated, .kernel,
   "The true law is 1/(b-1) + b^{-L}((b-1)[r=0]-1)/(b-1), which is uniform only in the L to infinity limit",
   "alias hall_uniform_casting_out", "2026-09-23"⟩,
  ⟨"Moshchevitin-Shkredov hot-spot criterion for continued fractions",
   "Deduce CF-normality from uniformly bounded upper block frequencies, as Vandehey 2017 Lemma 3.3 does",
   .falseAsStated, .kernel,
   "x = [0;1,2,3,...] has strictly increasing digits, so every block occurs at most once: the hypothesis holds vacuously with sigma = 0 while the digit 1 has frequency 0, not log_2(4/3)",
   "alias hall_moshchevitin_shkredov_cf_false", "2026-09-28"⟩,
  ⟨"low/high split for UniformResonantMass",
   "Reach UniformResonantMass by splitting the resonant primes at height 16 log(2+|t|) and paying the narrow high range |t| < 2*delta separately",
   .priorArt, .kernel,
   "The split is sound and its low and wide-high ranges are proved, but C3MrtUniformMass reached the same theorem first by a different assembly, so the narrow half had no consumer and was retired rather than carried as a sorry",
   "alias hall_urm_low_high_split; the live headline is conjC3_of_geom_input_band'", "2026-09-28"⟩,
  ⟨"min-rule descent of Vandehey 2017 Lemma 2.1",
   "Normalize an ingested CF digit by the paper's rule d = min(floor(alpha/gamma), floor(beta/delta)) and descend into M_D",
   .refuted, .kernel,
   "When the two column ratios have separated, one floor is 0 and the min emits nothing: from [[0,3],[1,1]] in M_3 with j=1 the rule two-cycles [[2,1],[1,2]] <-> [[1,2],[2,1]], neither in M_3; the statement survives but the proof cannot be transcribed",
   "alias hall_vandehey_lemma21_min_rule; probe probes/vandehey_lemma21.py; replacement Mat2.exists_balanced_decomp", "2026-09-28"⟩,
  ⟨"synchronizing word for the CF det-D transducer",
   "Replace Vandehey 2017 Theorem 3.1 by pathwise state-merging after a synchronizing word",
   .falseAsStated, .kernel,
   "The state fibres over P^1(Z/D) by row-lattice class and every letter acts bijectively on that quotient, so no word merges two classes: the Synchronizing hypothesis is unsatisfiable and every statement carrying it is vacuous for this automaton",
   "alias hall_vandehey_synchronizing_transducer; probe archive/probe/PROBE-2026-09-27-transducer-not-synchronizing.md", "2026-09-28"⟩,
  ⟨"emitted digit as a window function of the input",
   "Compute the image CF digit at a position from a bounded window of the input digits, F w = emitDigit (wordState w), with the initial state made invisible by merging",
   .falseAsStated, .kernel,
   "spread_runWord_le bounds the image DIAMETER uniformly in the initial state, not its LOCATION, and runWord s w = s.comp (wordState w) leaves the location entirely to s; the states (1,3;0,8) and (1,7;0,32), both of distortion 1, map [0,1] into the digit-2 and digit-4 cylinders and so emit 2 and 4 after reading ANY word",
   "alias hall_emit_digit_window_function; module VandeheyS7Memory; what survives is cfDigit_mob_eq_emitDigit, so the decomposition must be indexed by (state class, input word)", "2026-09-29"⟩,
  ⟨"Hecke approximation of phi by Fibonacci ratios",
   "Approximate phi by F_(k+1)/F_k, apply the PROVED Vandehey Thm 1.1 to each rational multiple, and pass to a diagonal limit using that nearby reals share a long CF prefix",
   .refuted, .kernel,
   "phi is the worst-approximable real: |p - q phi| >= 1/(4q) from the nonzero integer norm form p^2 - pq - q^2, so agreement of the images to CF depth N costs q^2 > c^N and a determinant pq >= q^2 exponential in N; Thm 1.1's automaton then carries e^(Omega(N)) states while only N input digits are read, so its equidistribution says nothing about that prefix",
   "alias hall_hecke_approximation; module VandeheyS7Hecke; theorems abs_sub_mul_goldenRatio_ge, pow_lt_den_sq_of_image_approx, sq_le_det_of_approx", "2026-09-29"⟩,
  ⟨"BlockForget repaired to CF-normal inputs",
   "Restrict the crux's input quantifier to CF-normal z, on the ground that a quadratic irrational is never CF-normal",
   .falseAsStated, .kernel,
   "The quantifier order is exists T then forall z, so the block length is fixed before the input while blockAvg at a fixed T is decided by the first T digits; CF-normality is a tail property, so a CF-normal z can open with T copies of the digit 2, and then the S7-BX state cycle gives block average at least 1/2 from shiftState against 0 from the reference state",
   "alias hall_blockforget_cfnormal = not_blockForgetGen; module VandeheyS7BlockGenRefute; any surviving crux must be asymptotic in T, which re-imports transducer correctness and hence the headline", "2026-09-29"⟩,
  ⟨"BlockForget in the uniform-z form",
   "Ask the block time-average blockAvg s T w z to forget the initial state uniformly over ALL input points z in (0,1)",
   .falseAsStated, .kernel,
   "At the Gauss fixed point z = sqrt2 - 1 every digit is 2, so the reference block average is exactly 0 for w = [1]; the width-1/3 state t -> 2/(t+2) runs on that input as a 2-cycle through t -> 1/(2t+4), whose two images 2 sqrt2 - 2 and (sqrt2-1)/2 have first digits 1 and 4, so its block average is ceil(T/2)/T >= 1/2 for every T -- a gap of at least 1/2, uniformly in T",
   "alias hall_blockforget_uniform_z = not_blockForget (+_cycle, +_state); modules VandeheyS7Quadratic, VandeheyS7BlockRefute; the repair is BlockForgetGen with z restricted to CF-normal points, which the architecture is all that ever needs since a quadratic irrational is never CF-normal", "2026-09-29"⟩,
  ⟨"the block-forgetting crux as a reduction of Vandehey S7 Problem 1",
   "Factor the headline through BlockForget/BlockForgetGen/BlockForgetRun/BlockForgetAll and treat the block comparison as the remaining analytic input",
   .restatement, .kernel,
   "The reference run IS the Gauss shift (S7-RR), so the comparison is against the input's own statistics, and S7-NR proves both directions of the SIGNED form: the crux without its absolute values holds exactly when slotCount / p tends to gamma(I_w), i.e. exactly when the conclusion holds; abs_gap_witness shows the step from signed to absolute is not free (equal Cesaro means, Cesaro mean of the absolute difference 1), so the crux is the headline plus local clock regularity plus window concentration",
   "alias hall_blockforget_is_restatement = abs_gap_witness, hall_blockforget_implies_goal = isCFNormal_image_of_blockForgetAll; modules VandeheyS7Circular, VandeheyS7NoReduction, VandeheyS7ArchWidthFree, VandeheyS7RefRun; the architecture stays valid as a FACTORISATION of the headline into a local statement", "2026-09-29"⟩,
  ⟨"the TransducerData bundle as the S7 front",
   "Package the transducer's block structure as an existential over sets S n j and treat the bundle as the remaining hypothesis",
   .vacuous, .kernel,
   "Nothing ties S n j to the state, so S n j = univ or empty according to whether the slot hits the target satisfies BlockCoupling whenever the conclusion holds: the bundle is a restatement of OrbitWordBound",
   "alias hall_transducerdata_vacuous = blockCoupling_trivial; module VandeheyS7StateCouple; the repair StateCoupling/StateData is the next row", "2026-09-27"⟩,
  ⟨"the StateData repair of the bundle",
   "Pin the coupling sets to a family of MobStates, so that the bundle is no longer free",
   .restatement, .kernel,
   "Pinning to a TYPE pins nothing: lowState (G^n y / G^n x) is a legitimate MobState sending G^n x to G^n y, so stateData_of_orbitWordBound derives the bundle from its own conclusion; a transducer hypothesis has content only when the state family is pinned to the input as a function, by the read/emit recursion",
   "alias hall_statedata_restatement = stateData_of_orbitWordBound; module VandeheyS7StateAudit; the honest pinning is runState (S7-RN)", "2026-09-27"⟩,
  ⟨"StateClock below the width scale",
   "Use StateClock q r0 eta K at a threshold T without relating T to the width floor eta",
   .vacuous, .kernel,
   "At T < 1/eta the state lowState eta has its entire image below 1/T, so every orbit time is counted by the comparison set and the inequality holds for free",
   "alias hall_stateclock_below_width = blockCount_le_card_lowState; module VandeheyS7Audit; the hypothesis has content only at T at least 1/eta", "2026-09-27"⟩,
  ⟨"the one-digit-per-read throttle behind the S7 scalar debts",
   "State WidthAfford / MeanSlack / ClockLinear for a transducer whose step emits at most one digit per read",
   .refuted, .kernel,
   "The throttle creates a queue of known-but-unemitted output digits whose length is a mean-zero random walk, so log(1/width) is null-recurrent of size sqrt(n) and the wide times have density zero; not_widthAfford_of_wide_sparse then makes WidthAfford false and crux_sum_le_of_wide_sparse makes the width-filtered crux vacuous on the same run, while the GREEDY transducer (maximal emission, S7-GR) keeps the slack bounded with freq(width < eta) of order sqrt(eta)",
   "alias hall_one_digit_throttle = not_widthAfford_of_wide_sparse; modules VandeheyS7WidthDensity, VandeheyS7Greedy; probe experiments/PROBE-2026-09-29-lap91-stall-and-width-walk.md Findings 2-4", "2026-09-29"⟩,
  ⟨"bounded-error decomposition of the image count",
   "Reduce SampledUniformCount to: the image's occurrence count agrees with a finite input-word family's count up to a bounded error C",
   .falseAsStated, .cited,
   "The window function computing the image digit is wrong exactly on the set where the orbit comes within delta of a cylinder endpoint, whose Gauss mass is positive (gaussMeasure_exceptional_le); a CF-normal input meets a positive-mass set with positive frequency, so the decomposition error is Theta(p), never O(1) -- the epsilon-scheme (approxScheme) replaces it",
   "module VandeheyS7Approx header; the surviving engine is tendsto_div_of_approxScheme", "2026-09-29"⟩,
  ⟨"Diophantine good-denominator detour for the tail cell",
   "Turn OrbitCellBound's w = [] case into a count of T-good rational approximations to the image and bound that count",
   .wall, .cited,
   "largeDigitCount_le_goodDenCount is unconditional and exact, but the counting input it needs -- #{q <= Q : ||q y|| <= 2/(Tq)} <= (D/T) log Q for the SPECIFIC image y -- is a Zaremba-strength statement about one real number, not an average, and no such bound is available",
   "module VandeheyS7Dioph; theorems largeDigitCount_le_goodDenCount, tailFreq_le_of_goodDenBound", "2026-09-29"⟩,
  ⟨"route B's unweighted cover of the state-dependent target",
   "Cover the state-dependent target by a FIXED finite family of cylinders, uniformly over the width-at-least-eta state box, and cite GaussACRigidity",
   .refuted, .cited,
   "State-blind is impossible -- over the whole box the targets' union is all of (0,1), so a cover valid for every state has mass 1, not C gamma(I_w); and net-indexed is quantitatively dead -- resolving a target of length gamma(I_w) needs precision rho <= gamma(I_w), so the box carries rho^(-4) cells and the unweighted cover mass is gamma(I_w)^(-3), i.e. C blows up with |w|; the Z[phi]-separation of the reachable states says this is not an artefact of the net",
   "DIRECTION.md fact (epsilon), review lap 88; modules VandeheyS7WD/WD'/CV/FT are finished and must not be extended", "2026-09-29"⟩,
  ⟨"predictable target sets from marginals alone",
   "Conclude OrbitCellBound from: A n = s_n^(-1)(E) is determined by x_1..x_n, has small Gauss mass, and the input orbit has the correct marginal frequencies",
   .refuted, .kernel,
   "Perfect marginals do not stop a sequence landing in its own predicted interval: the grid u n = n/k is exactly uniform on the k cells of width 1/k, yet u n lies in (u_(n-1), u_(n-1) + delta) for every n >= 1 once 1/k < delta, a hit frequency of (k-1)/k against an interval of length delta; at delta = 1/2, k = 10 that is 9/10 observed against 6/10 allowed",
   "alias hall_predictable_from_marginals; module VandeheyS7Predict; theorems cellUniform_grid, hitCount_grid, not_predictableHitPrinciple; any OrbitCellBound proof must use the arithmetic of s_n = O_n^(-1) Phi P_n", "2026-09-29"⟩,
  ⟨"site factorization via log-power BV",
   "Prove C-prime's RelativeFirstOrder (SiteFactorization) by writing the one-site fresh term as the other sites' frozen phase against z^Omega_P - z^Omega_(P,<=y), sieving the other sites into CRT atoms and applying Granville-Shao BV for multiplicative functions",
   .wall, .cited,
   "The reduction is sound and the main term is right, but uniformity in the growing window J fails. The multi-site sieve gives moduli multiplicity (2J)^omega(e), a loss of (log N)^(O(delta J^2)); deep sites cannot be dropped below J1 ~ log_4 log log N; and BV saves only a fixed (log N)^(-A). The |w_j|-weighted expansion (multiplicity C_h^omega(e)) has no level control. This is the fixed-window-conductor-at-depth wall again. REOPEN IF: BV for z^Omega_(P,<=y) at moduli <= x^(3/8) with a super-polylog saving (Delta_A with conductors up to exp(c sqrt log x) plus excision), or a sieve with polylog l1 mass at growing depth",
   "docs/CPRIME-SITE-FACTORIZATION-2026-10-01.md (referee section); CPrimeSiteFactorization.lean: card_siteAssignments (the J^omega(e) multiplicity, kernel target), DepthUniformMultBV (the reopen condition, open node), siteFactorization_of_depthUniform", "2026-10-01"⟩,
  ⟨"Erdős #257 gap sets via an S-restricted moment cap alone",
   "Prove isDisjunctive_subsetLambert_two_of_gapSet by restricting term_b/term_c (the moment order Mc) to S-primes and keeping the HypE frame",
   .refuted, .kernel,
   "HypE forces e <= 2^(8K^2) (HypE.e_le), and four_mul_le_two_pow_NE' independently needs e <= 2^(50K^2) because farC ~ log log X ~ e is an all-primes sum against 2^N, N = 100K^2; a set with F_S(e) <= A log(e+1) + C then has at most O(K^2) mass in the frame against a demand of 1000K^3, so no cutoff works for large K. REOPEN IF: a frame with farC and Mc both S-restricted, or N growing like m_1. REOPENED AND REALIZED 2026-10-02: HypE2 + farCS give isDisjunctive_subsetLambert_two_of_divergent",
   "theorem G4.SchedB.hypE_frame_excludes_logRate; reopen node G4.SchedB.SRestrictedFrame; module G4Base2GapObstruction", "2026-10-02"⟩,
  ⟨"Erdős #257 for squarefree / k-free A via the Chowla-Erdős kill",
   "Rerun the Campbell / joint-Lambert construction with coefficient 2^omega(m) to prove the squarefree (and k-free) #257 sum irrational at base 2",
   .priorArt, .cited,
   "CRT kills (j+1 primes exactly dividing n+j give 2^(j+1) | 2^omega(n+j)) plus the tau tail bound already prove it with no prime input, and that is Duverney-Tachiya, Forum Math. 31 (2019), Cor. 1.2 and Ex. 1.1 (linear independence, every base 2^j; k-free at bases q <= k). Semiprime A is not covered and the kill does not transfer (C(omega,2) is not robust to the cofactor). REOPEN IF: never as irrationality; the live question is SqfreeBinaryDisjunctive",
   "Erdos257Squarefree.lean: DuverneyTachiya2019KFree, erdos257_squarefree_of_literature, erdos257_kFree_of_literature; docs/OPEN-PROBLEMS-SWEEP-2026-10-03.md §4", "2026-10-03"⟩,
  ⟨"squarefree #257 single-survivor encoding at base 2",
   "Prove binary disjunctivity of sum 2^omega(m) 2^-m by replacing EvenEncoding with the survivor value 2^omega(n+r)/2^(r+1)",
   .refuted, .kernel,
   "A power of two over a power of two has fractional part 0 or 2^-t, so one survivor writes one bit and no survivor lands in the 101 cylinder (5/8, 3/4); a word with l ones needs l positions with exactly prescribed omega on one CRT progression, a prime-tuple / joint local Erdos-Kac input",
   "alias hall_sqfree_single_survivor; theorems Erdos257Squarefree.not_powTwoEncoding, fract_two_pow_div_two_pow; open target SqfreeBinaryDisjunctive", "2026-10-03"⟩,
  ⟨"CRT freezing for density of the binary words of E",
   "Count the Campbell / joint-Lambert CRT witnesses more efficiently to reach count_w(N) >= N/(log N)^A (R1) or >= c N (R2) for E = sum 1/(2^n-1)",
   .wall, .cited,
   "Every witness lies on one progression n = R + mA whose modulus kills k positions; k >= log_2 log N is forced because the uncontrolled tail sum tau(n+j)/2^j has mean (log N) 2^-k, and killing position j costs j+1 CRT primes, so log A ~ k^2 log k; the writer n+r = Q p needs a prime for an exact tau, a further 1/log N. Density is at most 1/(A log N) -> 0, topping out at N exp(-C (log log N)^2 log log log N). REOPEN IF: a statistical tail bound replaces killing, i.e. ResidualSmallPolylog (shifted-prime form for general words)",
   "EDensityAudit.lean: eCount_power, RungPolylog, RungRich, ResidualSmallPolylog; JointLambertQuantitative.jointWords_quantitative; docs/EDENSITY-AUDIT-2026-10-03.md", "2026-10-03"⟩,
  ⟨"free 2-adic kill plus forced band for E",
   "Use 2^omega_odd(m) | tau(m) to kill positions j <= (1-eps) log log n for free and force-kill only the band, to reach R1 for the binary words of E",
   .wall, .cited,
   "The free kill is real (two_pow_oddExpCount_dvd_card_divisors) but leaves the band j = log log n +- O(sqrt(log log n)), whose positions carry O(1) random fractions. Force-killing the band needs >> log log N log log log N distinct primes, a primorial of size (log N)^(c (log log log N)^2), so only N/(log N)^(C (log log log N)^2). The statistical alternative is a sieve in dimension ~ log log N with a per-position margin ~ log log log N, giving at best (log log N)^(-C) for the all-zero word, and a general word also needs one exactly prescribed tau (a parity-sensitive joint local Erdos-Kac input). Sibling control: tau mod 2 alone reads only squares, <= sqrt N + 1 ones (card_odd_card_divisors_le). REOPEN IF: ResidualSmallOften or ResidualSmallPolylog is proved, plus a writer input for general words",
   "EDensityAudit.lean: two_pow_oddExpCount_dvd_card_divisors, fract_card_divisors_div_two_pow_eq_zero, card_odd_card_divisors_le, ResidualSmallOften, ResidualSmallPolylog; Erdos257Squarefree.SqfreeBinaryDisjunctive; docs/EDENSITY-AUDIT-2026-10-03.md", "2026-10-03"⟩,
  ⟨"log-averaged casting-out via the Elliott ledger",
   "Consume TwoPointElliottLog (ledger: one zeta-exponent input) through a log-weighted casting-out / Katai route to get log-averaged 1- or 2-word frequencies of G4_b = sum omega(n)/b^n, or of the #257 / Erdos-Borwein Lambert sums",
   .wall, .kernel,
   "Log weighting survives every averaging step (partial summation and the two-point split, proved; Katai by the same linear argument) but not the carries: the digit reads omega(n+1) plus a floor of the whole tail, and the tail's mass b^-K log log X forces depth K -> infinity whatever the weights (carry_correction_unbounded). On the pair route the split is an equivalence given the ledger, so the crux is WeightDecoupleLog = log growing-depth Elliott with trivial product, open already at fixed K = 2. On the direct digit route each fixed depth is Tao-Teravainen 2019 (product a nontrivial root of unity to the omega), so the exact gap is uniformity in K. The #257 sums are worse (divisor tails, mass log X). REOPEN IF: GrowingDepthLogElliott (then simplyNormalLog_of_growingDepth is the wiring)",
   "alias hall_logavg_casting_out; LogCastingOut.lean: twoPointWeightedLog_iff_weightDecoupleLog_of_zetaExponent, TaoTeravainen2019FixedDepth, GrowingDepthLogElliott; SwingC1LogCarry.carry_correction_unbounded; SwingC1Log.castLawLog_one_iff; PairDecoupleProve.multiElliott_all; docs/LOG-AVERAGE-AUDIT-2026-10-04.md", "2026-10-04"⟩,
  ⟨"log-averaged word frequencies of an unconstructed constant as new",
   "Present log-averaged word frequencies of an arithmetically defined constant as the first positive-frequency statement about a constant defined without a construction",
   .priorArt, .cited,
   "Tao-Teravainen 2019 already give the log density 1/8 of every Liouville sign pattern of length 3, i.e. log 3-word frequencies of the carry-free binary constant sum [lambda(n)=1] 2^-n; and log Chowla is exactly log-normality of lambda (Sarnak's framing). The rung itself is genuinely weaker than normality (dyadicBit), so the novelty must come from a constant WITH carries, which is the wall row above",
   "alias hall_log_rung_distinct; LogCastingOut.lean: TaoTeravainen2019LiouvilleThree, tendsto_logFreq_dyadicBit, not_tendsto_natFreq_dyadicBit; docs/LOG-AVERAGE-AUDIT-2026-10-04.md", "2026-10-04"⟩,
  ⟨"linear forms in logarithms as the avoidance input",
   "Feed Baker / Matveev separation of 2^m from 3^n into UniformBad-type avoidance along {2^u 3^v} to get a rate the potential engine cannot",
   .vacuous, .cited,
   "The engine consumes the per-stage obstacle COUNT, which is elementary (band_unique_u: one u per v in a dyadic band); separation only bounds near-coincident scales, which neither add nor remove obstacles (overlap only helps avoidance). Its one honest consumer is Tijdeman's gap principle (gap_of_scaleSeparation), which no avoidance step uses; the dependent sibling (2,4) has no separation at all (not_scaleSeparation_two_four)",
   "LinearFormsScales.lean: band_unique_u, gap_of_scaleSeparation, not_scaleSeparation_two_four, Literature.BakerScaleSeparation; docs/LINEAR-FORMS-AUDIT-2026-10-04.md §2", "2026-10-04"⟩,
  ⟨"Stoneham profile beyond the Bailey-Borwein region",
   "Decide normality of alpha_{2,3} in bases outside 6 | B, B < 8^(v_2 B) (3, 5, 10, 18, ...) with scale separation as the new input",
   .wall, .cited,
   "Outside the region no Stoneham term becomes integral before the next one is live: in base 3 every earlier term stays a nonzero fraction with a power-of-2 denominator, in base 18 two terms are live at every position and the later one is a high-bit readout of 9^x mod 2^(Theta(3^m)). Both need equidistribution of 3^n mod 2^c over a window exponentially shorter than its period (Korobov / Erdos #406 regime), which separation of scales does not touch. REOPEN IF: ShortPowerOrbitEquidist",
   "LinearFormsScalesStretch.lean: StonehamBase3Normal, StonehamBase18Normal, ShortPowerOrbitEquidist; region facts Failures.not_isNormal_six_stoneham23, stoneham_base6_readout; Bailey-Borwein, Ramanujan J. 29 (2012) Thm 2 and Sec. 5; docs/LINEAR-FORMS-AUDIT-2026-10-04.md C1", "2026-10-04"⟩,
  ⟨"log-rate avoidance along Furstenberg's semigroup",
   "Remove the log log loss from the Moshchevitin / Peres-Schlag bound inf log q log log q ||q alpha|| > 0 over q = 2^u 3^v (frozen as furstenbergLogAvoid_holds, 7%)",
   .parked, .frozen,
   "Each K-adic stage carries about k obstacles of relative size c/k with total length O(c), but every known carrying rule pays: square-root potential (log q)^-2, exponent-gamma potential (log q)^(-1/gamma) (Badziahin-Harrap strength), local lemma log q log log q. Homogeneity is the only extra lever and no mechanism uses it; Moshchevitin expects the inhomogeneous order may be optimal, so a homogeneity-blind mechanism is suspect. Constant rate is false for an independent pair (Furstenberg) and true for a dependent one",
   "LinearFormsScales.lean: FurstenbergLogAvoid, furstenbergLogAvoid_holds (sorry), moshchevitinPeresSchlag_of_logAvoid, badziahinHarrap_of_logAvoid, not_constAvoid_of_furstenberg, constAvoid_powersOfTwo; docs/LINEAR-FORMS-AUDIT-2026-10-04.md C2", "2026-10-04"⟩,
  ⟨"bi-Lipschitz stability of Hochman-Shmerkin as new",
   "Present a strictly increasing bi-Lipschitz map sending the middle-third Cantor set into non-2-normal numbers as a new negative answer to Hochman-Shmerkin (Invent. 2015, 1.2.1) 'stability under bi-Lipschitz transformations remains open'",
   .priorArt, .cited,
   "The reading is faithful (their Thm 1.4/1.5 give pointwise normality for every C^1 diffeomorphism), but the mechanism is a bi-Lipschitz embedding of K into the no-hex-digit-15 set F, which Mattila-Saaranen 2009 and Deng-Wen-Xiong-Xi 2011 Thm 1 already provide; only monotonicity is extra. Kept as the C^1 sharpness guard, not as outreach",
   "EntropyProfiles.lean: exists_strictMono_biLipschitz_cantorSet_not_isNormal_two (sorry), not_biLipschitz_stable, HochmanShmerkinCantorDiff1; docs/ENTROPY-REFEREE-2026-10-04.md", "2026-10-04"⟩,
  ⟨"pair-universal mechanism for a normal element of a Q-span",
   "Find a normal number among the nonzero rational combinations of sqrt 2 and sqrt 3 by an argument that works for every Q-independent pair, as the six-fold adder disjunction works for every pair not both rational",
   .refuted, .frozen,
   "Witness: a supersparse Liouville pair whose every rational combination has long periodic stretches dominating its prefixes, so none is normal. A mechanism must use something sqrt 2, sqrt 3 have and the pair lacks",
   "QSpanNormal.lean: exists_pair_qSpan_not_normal (sorry, 90%), qSpanNormal_sqrt_two_sqrt_three; Barriers.liouville_pair_qSpan", "2026-10-05"⟩,
  ⟨"Diophantine (exponent-2) input for a normal element of a Q-span",
   "Use Roth-type information (every element of the span of sqrt 2, sqrt 3 has irrationality exponent 2), which kills the Liouville witness, to force a normal element of the span",
   .refuted, .frozen,
   "Witness: a random pair from the product of {0,1}-digit Cantor measures in base 10. Every nonzero rational combination has exponent 2 (Benard-He-Zhang), yet the joint digit entropy log 4 < log 10 caps every combination below normal (span_dimension_budget). The missing input is digit entropy, not Diophantine quality",
   "QSpanNormal.lean: exists_pair_exponentTwo_qSpan_not_normal (sorry, 80%), span_dimension_budget (sorry, 85%), qSpanNormal_sqrt_upperDim", "2026-10-05"⟩,
  ⟨"x3-invariant measure on K cap BAD",
   "Get a point of K cap BAD normal to every base prime to 3 from Host / Hochman-Shmerkin, by a x3-ergodic positive-dimension measure carried by BAD",
   .refuted, .frozen,
   "Einsiedler-Fishman-Shapira: such a measure gives BAD zero mass, so the measure on K cap BAD must be non-invariant (the deletion descent) and normality must come from a Cassels-type second moment",
   "CantorBadNormal.lean: not_exists_timesThree_law_on_bad, Literature.EFSTimesThreeNotBad, fourierPairRate_resLaw (the open crux; old choose-based crux now the node FourierPairRateChoose)", "2026-10-06"⟩,
  ⟨"numerator averaging for the preperiodic obstacle families",
   "Get the AliveOffMix cancellation of the preperiodic obstacles (3-free denominator dividing 3^l +- 1) by averaging their phases over the obstacle numerators mod 3^j, where the full-residue mean square has square-root cancellation for free, instead of averaging over m",
   .wall, .frozen,
   "Pairs with equal 3-adic numerators keep a phase periodic in m (pow_phase_recur), and their share does not decay (probe: collision ratio .157, .144 at L = 12, 14; b = 2, 5, 7 mean .09, .08 flat; controls b = 3 and dyadic exactly 1). So numerator averaging gives a constant saving only; the decay must come from the middle ternary digits of h b^m, a digits-of-powers statement beyond every Korobov range",
   "CantorBadNormal.lean: PreperiodicNumeratorDispersion (believed false, 10%), pow_phase_recur, obstacle_phase_crt, ThreeAdicWindowAvg (open), not_threeAdicWindowAvg_three; scripts/cantorbad_numdisp.py", "2026-10-07"⟩,
  ⟨"schedule redesign for the trivial count",
   "Re-time the forced runs (previous run ending at lambda b) so that deterministic avoidance with the spacing count Q^2 3^-a + Q reaches tau below 2 + log2 3",
   .refuted, .frozen,
   "The two constraints 2x < lambda + (1-lambda) L and x < (1-lambda) L (x = 1/(tau-1), L = log3 2) force x < L/(1+L), i.e. tau > 2 + log2 3, for every lambda",
   "CantorExactExponentStretch.lean: trivial_count_barrier", "2026-10-05"⟩,
  ⟨"per-q residue counting below 1 + log2 3",
   "Push the exact residue count (P q mod 3^b within 3^k of 0: at most 2^(k+1) Cantor numerators per q) below mu0 = 1 + log2 3",
   .wall, .frozen,
   "Uniform in q it costs 3^m 2^-(tau-1)m per window, which does not decay for tau <= 1 + log2 3; below, the count must average over q (digits of r q-bar mod 3^b on a box of density 3^-(tau-2)m), a restricted-digit Kloosterman estimate with no known input. The Riesz-product L1 bound (Lambda <= 4/3, numerically 1.2966) reaches only m < 0.394 b. REOPEN IF: RunEnteringCount",
   "CantorExactExponentStretch.lean: card_lowResidue_le, exactCount_rho_ge_one, RunEnteringCount; experiments/stretch_exact_count.py", "2026-10-05"⟩,
  ⟨"exact residue count as a BFR input",
   "Read the stretch lane's exact residue count (at most 2^(k+1) Cantor numerators per q) as new information about rationals near the Cantor set (Broderick-Fishman-Reich, Bugeaud-Durand)",
   .vacuous, .frozen,
   "In BFR terms the count is the classical covering bound: K at scale 1/q has 2^n pieces holding at most 4 fractions p/q each, so N_K(Q, 1/Q) << Q^(1 + dim K), the known trivial bound",
   "StretchBFR.lean: card_near_cantor_le (sorry, 95%); CantorExactExponentStretch.card_lowResidue_le", "2026-10-05"⟩,
  ⟨"Bugeaud-Durand count as the stretch input",
   "Derive RunEnteringCount from a Bugeaud-Durand-strength count of rationals near K, or the reverse",
   .vacuous, .cited,
   "BD-type counts see rationals near K at resolution at least the cylinder scale; RunEnteringCount counts rationals within q^-tau < 3^-b of the 2^b discrete endpoints P/3^b, a measure-zero set. Neither statement carries information about the other's regime as stated",
   "StretchBFR.lean module doc; CantorExactExponentStretch.RunEnteringCount; endpoint_sep", "2026-10-05"⟩,
  ⟨"single-sum inverse cancellation for the run-entering count",
   "Prove RunEnteringCount from a power saving for exponential sums over inverses of Cantor numerators mod 3^b (numerically square-root-like)",
   .refuted, .kernel,
   "The Fourier expansion over the q-interval converts the count into inverse sums with error R 2^b' 3^(-delta b'), which beats the main term only for m > b - delta b'; with at most square-root saving that misses every window m <= b/2, where the binding windows sit. (Corrected 2026-10-06: the conclusion 'a bilinear estimate is needed' was wrong; the union of hitting numerators is bounded elementarily by 3-adic Farey separation, padic_sep / hit_mass_padic, which proved the stretch node)",
   "StretchBFR.lean: singleSum_insufficient (proved), windowCount_of_inverseSum (sorry, 80%), InverseCantorSumBound; experiments/cantor_inverse_sums.py", "2026-10-05"⟩,
  ⟨"He-Liao local count on the forced-run measure",
   "Transfer He-Liao 2602.01307 Cor. 6.5 (local equidistribution of rationals against Cantor-measure cylinders) to the forced-run measure, to push the exact-exponent triple below mu0 = 2 + log2 3",
   .wall, .cited,
   "The transfer to branches is fine, but the trivial count only fails in run-entering windows, where the event concerns the discrete endpoint P/3^b below the cylinder scale (endpoint_sep); thickening to 3^-b costs 3^(2m-b) >= 1 for mu0 <= 3 (thickening_cost_ge_one), and Cor. 6.5's main term needs alpha >= tau - 2 > 1 there while its alpha - 1 is small and non-explicit. A Bugeaud-Durand-strength measure count would reach at best mu0 > 3. REOPEN IF: EndpointRationalCount",
   "CantorExactExponentStretch.lean: endpoint_sep, thickening_cost_ge_one, Literature.HeLiao2026Cor65, EndpointRationalCount; CantorExactExponent.bcTerm_red_mu_three; docs/CANTOR-EXACT-EXPONENT-AUDIT-2026-10-04.md", "2026-10-05"⟩,
  ⟨"3-adic Farey separation as a BFR count",
   "Use padic_sep (bound the union of hitting numerators) to count Cantor points near rationals: the restricted-digit hyperbola #{P in C_b : P q = r mod 3^b, q <= Q, |r| <= R}, in any base",
   .vacuous, .kernel,
   "Proved: at most 2^j with 2RQ < 3^j, i.e. (RQ)^(log3 2), and the base need not be prime (only gcd(q, B) = 1). But it is the 3-adic covering bound, the twin of card_near_cantor_le; through R = delta Q 3^b it returns the trivial count of N_K(Q, delta) again",
   "StretchBFR.lean: card_cantor_hyperbola_le, eq_of_hyperbola_low, card_near_cantor_le", "2026-10-06"⟩,
  ⟨"power saving for N_K(Q, delta) from separation",
   "Combine 3-adic and archimedean Farey separation to beat the covering bound Q delta^(-dim K) for Q^-2 < delta < Q^-1",
   .priorArt, .cited,
   "Both separations are the same cross-determinant >= 1 fact and both return the covering count; a saving needs a Fourier input (Fourier l1 dimension), which is the mechanism of Chow-Varju-Yu arXiv:2402.18395 for missing-digit sets. REOPEN IF: NKPowerSaving by an elementary route",
   "StretchBFR.lean: NKPowerSaving, card_cantor_hyperbola_le", "2026-10-06"⟩,
  ⟨"Independence-relative product blocks",
   "Use independence-relative certificates (fail only on rational lines) to get a small two-track all-digits block: for every Q-independent pair, some combination aX + bY with small (a, b) has every ternary digit i.o., beating the single-track {2, 11}",
   .refuted, .frozen,
   "Every small direction set has an avoided-digit assignment whose live automaton keeps a component not certified degenerate. Product-block counterexamples vary X and Y separately (two-dimensional); a relative certificate only discards one-dimensional failure loci, so the gain is confined to tightly coupled single-word families like ternary_line. Binary 2-word blocks (|coef| <= 3, up to 3 directions) also all fail. REOPEN IF: a complete degeneracy test, or larger coefficients",
   "IndependenceRelative.lean: not_isRelativeBlock_small (sorry, 65%), IsRelativeBlock, ternary_line; experiments/independence_relative.py blocksearch", "2026-10-05"⟩,
  ⟨"elementary orbit port to 3 | b",
   "Prove a.e. normality of the exact-exponent Cantor point to b = 3^s t below the profile threshold by porting secondMoment_le_b, with the orbit of t mod 3^k counting the low ternary digits of h(b^d-1)t^m",
   .wall, .kernel,
   "For m in a run's shadow (a <= sm < E) the forced places hide every digit of the frequency below relative position E - sm, linear in N; orbits mod 3^k with 3^k <= N cannot reach them, and the shadow is a positive fraction of [0, E/s) (shadow_card_ge), so the blind bound costs O(1) per run and the DEL sum diverges. The top digits are free below the threshold (window_covered_imp) and are fixed by {m log3 t}. REOPEN IF: LogDiscrepancy (Baker)",
   "CantorExactExponentProfile.lean: shadow_card_ge, window_covered_imp (proved), LogDiscrepancy, Literature.BakerLogDiscrepancy, ae_isNormal_of_profileOK_of_baker (sorry, 60%)", "2026-10-06"⟩,
  ⟨"Effective dimension as the currency for one-of statements",
   "Measure digit complexity by effective (Kolmogorov) dimension, which is invariant under every computable map (x ^ y, exp, powers), to get one-of theorems through nonlinear transformations",
   .vacuous, .cited,
   "Every computable real has effective dimension 0 (the constant map to it is computable), so pi, e, sqrt 2 and phi are all simple in that currency and no one-of statement about them can hold. The currency must be one the constant cannot be built in: finite-state dimension, which respects only finite-state maps",
   "ConjugateEntropy.lean: invariant_vanishes_of_const_mem", "2026-10-05"⟩,
  ⟨"Entropy budget through squaring",
   "Carry the finite-state entropy budget through x |-> x^k, to get one-of statements from polynomial relations such as (x+y)^2 or Galois power sums used multiplicatively",
   .refuted, .frozen,
   "Squaring is not finite-state and moves entropy both ways: Manai's deterministic X has X^2 normal, so no inequality links h(x) and h(x^2). Powers enter only linearly, through the integer power sums of a Galois orbit (ConjugateDet)",
   "DeterministicBD.lean: detSqNotDet_of_manai, Literature.Manai2026.Cor14; ConjugateDet.lean: not_exactly_one_nondet", "2026-10-05"⟩,
  ⟨"Diophantine input to a carry-automaton certificate",
   "Upgrade a non-collapsing carry-automaton family to a theorem about specific constants using their irrationality measures (Roth for algebraics, known bounds for pi, e, ln 2)",
   .refuted, .frozen,
   "The escape set of an automaton family is omega-regular: either all rational, or it holds two distinct cycles and so a self-similar Cantor set, which contains exponent-2 irrationals. Simplest witness: the escape set of 'X avoids ternary 1' is the middle-thirds Cantor set, which has an exponent-2 point. The only fact about specific constants an automaton can use is a rational linear relation (independence-relative certificates)",
   "CantorExactExponentStretch.lean: exists_mem_cantorSet_irrExponent_two_of_literature (Literature.Weiss2001); IndependenceRelative.lean: ternary_line", "2026-10-05"⟩,
  ⟨"Digit-count ladder for product blocks",
   "Build product blocks in base 5, 7 and up from cheap rungs a -> a+1 (each lifts every irrational with a digits i.o. to a multiple with a+1), composed by multiplying the sets",
   .refuted, .frozen,
   "Rungs do compose (IsRung.mul), and the first base-5 rung is a pair ({2, 11}), but the top rung g-1 -> g is nearly the whole block problem: an irrational avoiding one digit already has dimension log(g-1)/log g, and no T of at most 3 members in [2, 60] (or 2 in [2, 400]) is a base-5 rung 4 -> 5. The ladder costs more than a direct block. REOPEN IF: rungs keyed on WHICH digit is missing whose top step is cheaper than a block",
   "MahlerProductBlock.lean: IsRung.mul, isRung_five_two_three, not_isRung_five_four_five_small; mahler_block lift/rung", "2026-10-06"⟩,
  ⟨"Dimension count as a block-size lower bound",
   "Predict the minimal product-block size from codimensions: each 'm x avoids d' costs 1 - log(g-1)/log g, so a block needs about log g / -log(1 - 1/g) ~ g ln g members (8 in base 5)",
   .refuted, .cited,
   "Base 3 predicts at least 3 (codimension 0.369 each, two constraints leave dimension 0.26), yet {2, 11} is a block: the constraint sets share one base, so their product automaton can have zero entropy while the codimensions sum below 1. The heuristic is not a lower bound, and base 5 may have blocks below 8",
   "MahlerProductBlock.lean: isProductBlock_three_two_eleven", "2026-10-06"⟩,
  ⟨"x, 3x, 5x as the first member of a family",
   "Extend the binary theorem 'x, 3x or 5x has both 00 and 11' along {1, 2^k-1, 2^k+1} for runs 0^k and 1^k, or along {1, g-1, g+1} for digits 0 and g-1 in base g",
   .refuted, .frozen,
   "Both break at the next step: the Liouville number 3 * sum 2^-(i!) beats {1, 2^k-1, 2^k+1} for every k >= 3 (3, 3(2^k-1), 3(2^k+1) have no run of k ones), and {1, g-1, g+1} lets every member avoid digit 0 for g = 4..13, 16. Minimal run-block sizes go 1, 3, then at least 5. REOPEN IF: a family whose members widen a sparse x carry-free and a detector that reads token boundaries, as 3 and 5 do at k = 2",
   "MahlerProductBlock.lean: not_isWordSetBlock_runs_three_one_seven_nine, not_isWordSetBlock_runs_three_small, not_isWordSetBlock_extremeDigits", "2026-10-06"⟩,
  ⟨"counted medium bases over an exact {2,3} core at c = 4",
   "Make bases 2, 3 exact (containment-kill core, certificate ratio 1.669) and charge every base b >= 5 by counting kills against alive ancestors, as in cStar_le_six",
   .wall, .cited,
   "Counting pays m >= 2 boundary cells per window against g^lag ancestors, i.e. about 3 b^(-4 log2 g) per order instead of the measure 2 b^(-4). Level-averaged, b >= 5 cost 0.09 / 0.049 per level at g = 1.6 / 1.7, so the core needs growth >= 1.78 with near-uniform weights; the abstraction gives 1.67-1.73 and its weights are far from uniform (10% zero, threshold 0.2 collapses it, max-descendant ratio up to 1200). Probes scripts/cstar_models/abs23.js, kreg.js. Decisive probe 2026-10-07 (c-star lap 8) on the TRUE joint {2,3} tree (no abstraction): per-cell 10-step lookahead growth in [1.751, 1.842], and the weight-aware charge (killed core mass / ancestor core mass) of base 5 reaches 0.055 = 1.5x the regular value 4/1.8^lag already among 220 windows; the engine recursion M(k+1) = M(k) - sum_b rho_b M(k+1-lag_b) with these charges DIES at level 91 at c = 4, survives at c = 4.25, and at c = 4 survives only once base 5 is also exact (decay 0.975/level; x2 charges die). So even a perfect weight-regular {2,3} core does not reach c = 4 by ancestor counting. Probes scripts/cstar_models/joint23_spread.js, joint23_rho.js, joint23_rec.js. REOPEN IF: a regular core for S = {2,3,5,6,7} (SmallBaseTreeCore) with charges within 1.5x of regular. Lap 9 probe (core5.js): the exact {2,3,5,6,7} tree grows 1.815/level and b >= 10 counted survives at 4x charges, so the reopen condition reduces to weight regularity of that core alone (1% quantile of 12-step growth 1.59)",
   "UniformBadJoint.lean: jointCoreSubEigen_four (sorry), exists_good_of_subEigen; UniformBadRoute.lean: SmallBaseTreeCore; PENDING_WORK c-star lap 4", "2026-10-07"⟩,
  ⟨"adaptive split cores for the Newhouse thick core",
   "Build the thick core B inside every E_b(4), b >= 3 (thickness > 1/3, paired with E15 by the gap lemma) adaptively: local splits with good endpoints (SplitCore), the flipped pairing A = Fset 3 4 against B inside E15 and every E_b(4), b >= 5, or discarding clusters of near-touching windows instead of bounding them",
   .wall, .cited,
   "Adaptivity is illusory: a tau-thick compact B in the good set puts any two windows that are tau-close inside its hull into one gap (windows_merge_forced), so the gaps of every thick core contain the canonical tau-merge closure of the windows, and ThickCore holds iff that closure stays local. Locality needs a bound on merge cascades of windows of distinct bases at every depth; none is known (pair counts of centres A/b^n, A'/b'^m are exact lattice counts, 2 eps q q' + gcd, so clusters of every size are expected at small enough scales), and every pairing of Newhouse sets puts infinitely many bases on one side. REOPEN IF: a locality argument for the canonical closure that tolerates unbounded clusters, i.e. a proof of ThickCore itself",
   "UniformBadNewhouse.lean: merge_forced, windows_merge_forced, thickCore_of_splitCore, ThickCore, thickCore_four (sorry, 70%)", "2026-10-07"⟩,
  ⟨"Archimedean-only mechanisms for Erdős #406",
   "Prove that 2^n eventually has a ternary 2 from the real side alone: equidistribution of n log3 2, Baker discrepancy, leading-digit counts, shrinking targets for the rotation",
   .refuted, .cited,
   "Every such input also holds for floor(l 2^n) with any real l, and Lagarias (Thm 1.2) gives uncountably many l with infinitely many omitters. A proof must use that the low digits of 2^n follow 2^n mod 3^k",
   "ErdosTriples.lean: Literature.LagariasRealSibling", "2026-10-06"⟩,
  ⟨"Exceptional set via all exponent tuples",
   "Bound dim E(Z3), and so approach Erdős #406, by the supremum of dim C(1, 2^m1, ..., 2^mk) over every exponent tuple (ABL's nesting constants Gamma, Gamma*, alpha_n)",
   .refuted, .kernel,
   "Tuples with a gap of one power of 4 stay nonzero (4 = 1 + 3 gives the golden-mean shift): C(1, 4, 4^4) contains 1 and C(1, 4^8, 4^9) contains 282864854542, so the supremum stalls (ABL: log3 phi). An infinite orbit never has to face those tuples: pass to three exponents with large gaps",
   "ErdosTriples.lean: not_tripleTrivial_one_three, not_tripleTrivial_eight_one", "2026-10-06"⟩,
  ⟨"Erdős #406 via gap-two triples",
   "Reduce Erdős #406, and E(Z3) = {0}, to C(1, 4^a, 4^(a+b)) = {0} for all a, b >= 2, each instance a finite carry-automaton decision",
   .wall, .frozen,
   "The wiring is proved and every instance with a + b <= 160 is trivial (largest automaton 388 states), but nothing uniform covers the 3-adic imitators a = 1 + 3^D t, whose automata copy the golden-mean one for D levels. REOPEN IF: a uniform extinction bound for carry automata whose multipliers are 3-adically near 4",
   "ErdosTriples.lean: erdos406_of_gapTriplesEventually, tripleTrivial_of_sum_le_160, GapTwoTriples", "2026-10-06"⟩
]

/-- Rows whose verdict is machine-checked in this build. -/
def kernelRows : List Hall := register.filter (fun h => h.tier = Tier.kernel)

/-- Count of halls by verdict, for the report-back line. -/
def countOf (v : Verdict) : Nat := (register.filter (fun h => h.verdict = v)).length

end NormalNumbers.Maze
