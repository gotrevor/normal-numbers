# HANDOFF 2026-09-23 — Theorem C′: reach, cross-check, and the three doors left

Branch `wip/g5-prime-subset`.  `lake build` 🟢 **9166 jobs**.  Five green commits this run,
all **pure additions** (no existing statement touched, `PrimeModelBrunLower.lean`/`papers/`/
Pair B untouched).

## Status of the directive

`DIRECTION.md` → CURRENT DIRECTIVE objective — `isNormal_subsetLambert_of_sqrtFreshMassZero`
sorry-free and trust-triple — is **MET and independently re-verified this run**:

* `isNormal_subsetLambert_of_sqrtFreshMassZero` → `[propext, Classical.choice, Quot.sound]`
* `audit_isNormal_subsetLambert_of_sqrtFreshMassZero` (audit surface) → same
* lap-0 deliverables `recipSumIoc_le_rootChain`, `sqrtFreshMassZero_of_freshMassZero`,
  `sqrtFreshMassZero_of_relDensityZero` → same
* the three leaves named by the 2026-09-23 review lap (`termE5_tendsto`,
  `schedule_admissible`, `termE4c_tendsto`) are all closed; `PrimeModelFamilyGraded.lean`
  is sorry-free.

`src/` holds exactly the two pre-existing off-campaign `sorry`s that the directive designates
open: `PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_prime_nonresidue`.

## What this run added (all sorry-free, all trust triple)

1. **`PrimeModelGeometricMass.lean`** — Astra §10's functional
   `geomFreshMass P N = ∑_{j=1}^{J_N} 4^{−j} S_P(y_j, 2N)`, with
   `geomFreshMass_le : F_N ≤ 2(3 + 2 log₂ u_N)/u_N² + 2 S_P(⌊√(2N)⌋, 2N)` and
   `geomFreshMass_tendsto : SqrtFreshMassZero P → F_N → 0`.
   *Mechanism*: the geometric weight absorbs the root-chain length — `j ≤ 2^j` turns
   `4^{−j}(j+2+2log₂u_N)` into `2^{−j}(3+2log₂u_N)`, so the sum is `O(1/u_N)` and does not
   grow with `J_N`.  The doubling step is the one-step chain `S_P(N,2N) ≤ S_P(⌊√(2N)⌋,2N)`
   (`sqrt_two_mul_le`, unconditional).
   *Consequence*: C′'s hypothesis is at least as strong as §10's, so §10 is a genuine
   generalisation and nothing was lost by proving C′ first.

2. **`PrimeModelSqrtFreshBlocks.lean`** — the double-exponential block criterion, and then its
   converse.  `dblBlockMass P n = S_P(2^{2^n}, 2^{2^{n+2}})`;
   `dblBlockMass_tendsto_iff : (dblBlockMass P → 0) ↔ SqrtFreshMassZero P`.
   *Mechanism*: in `t = log log x` coordinates the square-root fresh window `(√N, N]` has
   **constant** length `log 2`, so it always fits in a single block with index
   `n = ⌊log₂⌊log₂⌊√N⌋⌋⌋ → ∞` (`sqrt_window_subset`, via `N < (⌊√N⌋+1)²`); conversely the
   block is exactly **two** root-chain steps wide (`log M/log y = 4`, `⌈log 4/log 2⌉ = 2`),
   so `dblBlockMass P n ≤ 2ρ` (`dblBlockMass_le_of_bound`) — `recipSumIoc_le_rootChain` used
   at the window where it is sharp rather than lossy.
   *Consequence*: Astra §10's prime-burst example (bursts at `t_n = exp(n²)`, `t`-width `1/n`,
   mass `O(1/n)`, gaps `≫` any fixed window) satisfies this, hence satisfies
   `SqrtFreshMassZero`.  **Theorem C′ already covers that example; §10 is not needed for it.**

3. **`PrimeModelGradedCrossCheck.lean` + `OccurrenceCountEquiv.lean`** — independent
   NL→Lean faithfulness cross-check.  The *English* statement of C′ (never our Lean) was
   handed to an auto-formalizer; its rendering is archived at
   `archive/findings/ARISTOTLE-2026-09-23-theoremC-prose-formalization.lean` (prose input
   beside it).  It differs from our audit surface in three places, **all three now proved
   equivalent**:
   * `Real.sqrt N < p` over `Icc 1 N` vs `Nat.sqrt N < p` over `Ioc (√N) N` — the finsets are
     *equal* (`freshWindow_eq`; both say `N < p²`);
   * subtype non-summability vs our indicator form (`divergentRecip_iff_subtype`);
   * counting by start position `i < n` vs by suffixes of the first `n` digits — genuinely
     different finite numbers, bracketed within `|w|`
     (`countOccurrences_le_occStart`, `occStart_le_countOccurrences_add`), hence equal
     frequency limits (`tendsto_occStart_iff`).
   `isNormal_subsetLambert_crossCheckForm` and `…_occStart` derive our headline from the
   independently written hypotheses verbatim, in the independent counting convention.
   **No faithfulness defect found.**

## The three doors left, and why none of them is a lap

Everything still open needs an operator decision, because `DIRECTION.md` → *Forbidden drift*
bars opening a new campaign and designates the only two `src/` `sorry`s as open.  The three
candidates, now scoped concretely rather than gestured at:

1. **Astra §10 consumer (normality from `F_N → 0` alone).**  The converse of item 1 above.
   Feasibility is now *known good*: `hS` enters `PrimeModelFamilyGraded.lean` through exactly
   five derived facts — `uG_tendsto`, `yBotG_le_yG_nat`/`yBotG_le_yG`, `recipSumIoc_yG_le`,
   `epsG_tendsto`, `yG_le_self`/`LG_spec` — so the file is an *interface*, not a weave.  The
   blocker is that `u_N` is read off `epsG` whereas §10 chooses `u` freely, so the schedule
   must be re-parametrised over a supplied `u : ℕ → ℕ`.  With "no existing statement changes"
   that means a parallel ~1800-line file; with permission to generalise in place it is
   mechanical.  **Ask: authorise in-place generalisation over `u`.**
2. **Strictness / sharpness of the hypothesis.**  Is `SqrtFreshMassZero` *strictly* weaker
   than `FreshMassZero`?  Is it false for the full prime set (i.e. does C′ genuinely exclude
   Copeland–Erdős)?  Both reduce to two-sided Mertens (`∑_{p≤x} 1/p = log log x + O(1)`),
   which is **not in mathlib** — the repo has only the crude one-sided `primeRecipSum_le` and
   `mertens_crude`.  The elementary route is available (`∑_{n≤x} 1/n ≤ ∏_{p≤x}(1−1/p)^{−1}`
   via `Nat.smoothNumbers`; note the mathlib Euler-product lemmas need `Summable f` and so do
   **not** apply to `f n = 1/n` directly — the finite truncation has to be done by hand).
   A real multi-lap target.  **Ask: authorise a Mertens campaign.**
3. **The two designated-open `sorry`s.**  `phaseOscillation`, `exists_prime_nonresidue`.
   **Ask: un-designate one.**

## Note on the 2026-09-23 stuck-bail (strike 1, HEAD `b78b343`)

Its *facts* were right and I re-verified every one.  Its *conclusion* — that no authorised
workable ground remained — was too cautious: the five nodes above were all reachable inside
the ratified kickoff spec (§10 and the root chain are in its own reading list) as pure
additions.  Treat that claim as expired.  The present hand-back is a narrower one: the
in-spec additive ground is now genuinely worked out, and each of the three remaining doors
names the exact permission it needs.
