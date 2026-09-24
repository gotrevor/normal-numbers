/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.CFScheduleARefuted
import NormalNumbers.G4EntropyBarrier
import NormalNumbers.G4EntropySubsample
import NormalNumbers.G4EntropyMixture
import NormalNumbers.G4EntropyPointwise
import NormalNumbers.G4EntropyDiagonal
import NormalNumbers.G4RowVariance
import NormalNumbers.G4RowMassOptimal
import NormalNumbers.G4WiringSparse
import NormalNumbers.StonehamSixFailure
import NormalNumbers.Walsh
import NormalNumbers.WalshBase

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
   .vacuous, .cited,
   "Wall 1949: normality survives rational multiplication, so picking a multiplier says nothing",
   "projects/normal-numbers.md", "2026-08-25"⟩,
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
  ⟨"uniform casting-out law (C1 draft)",
   "Assume a normal number's window digit sum is uniform mod b-1",
   .falseAsStated, .cited,
   "The true law is 1/(b-1) + b^{-L}((b-1)[r=0]-1)/(b-1), which is uniform only in the L to infinity limit",
   "branch wip/casting-out: CastingOut.not_castUniform_of_isNormal", "2026-09-23"⟩
]

/-- Rows whose verdict is machine-checked in this build. -/
def kernelRows : List Hall := register.filter (fun h => h.tier = Tier.kernel)

/-- Count of halls by verdict, for the report-back line. -/
def countOf (v : Verdict) : Nat := (register.filter (fun h => h.verdict = v)).length

end NormalNumbers.Maze
