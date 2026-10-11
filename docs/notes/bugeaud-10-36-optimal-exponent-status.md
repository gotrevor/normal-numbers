# The optimal exponent in Bugeaud's Problem 10.36: where we are (status for a second opinion)

[ Claude wrote this note at my direction.  The Lean files it names are the authority.  -Trevor ]

Status as of 2026-10-09, branch `proof/uniformbad-threshold`, not yet merged into trunk.  Revised the same day after Codex's review (mailbox `~/personal/agent-mail/nn-cstar/`, review module `UniformBadTowerReview.lean` at `819bd8fc`).

## The question

Write `‖t‖` for the distance from `t` to the nearest integer.  Bugeaud, *Distribution modulo one and Diophantine approximation* (Cambridge Tracts 193, 2012), p. 219, Problem 10.36, asks for a real `ξ` and a constant `c > 0` with `‖bⁿξ‖ > b^{−c}` for every integer base `b ≥ 2` and every `n ≥ 0`.  We proved this with `c = 24` (`docs/notes/bugeaud-10-36-uniform-bad.md`, `UniformBad.bugeaud_10_36`).

This note is about the **optimal exponent**:

  `c⋆ = inf { c : ∃ ξ, ∀ b ≥ 2, ∀ n ≥ 0, ‖bⁿξ‖ > b^{−c} }`

In Lean this is `cStar` in `src/NormalNumbers/UniformBadThreshold.lean`, with `Admissible c` for the inner condition.  `Admissible` is monotone in `c`.  Before this lane, the known range was `log₂ 3 ≤ c⋆ ≤ 24`.  The lower end is base 2 alone, since `‖ξ‖ ≤ 1/3` or `‖2ξ‖ ≤ 1/3`.  We found no paper that states any uniform exponent, so any located value is new.

## Where we are

**`729/290 ≤ c⋆ ≤ 124/25`**, that is, `2.513793… ≤ c⋆ ≤ 4.96`.  Both ends are proved in Lean.

| Result | Lean name | File | Axioms |
|---|---|---|---|
| `c⋆ ≥ 729/290` | `le_cStar_729_290` | `UniformBadTower.lean` | standard only |
| `c⋆ ≥ 93/37`, `5/2`, `12/5` (earlier) | `ninety_three_thirty_sevenths_le_cStar`, ... | `UniformBadLowerBound.lean`, `UniformBadThreshold.lean` | standard only |
| `c⋆ ≤ 124/25` | `cStar_le_124_25` | `UniformBadBelowFive.lean` | `native_decide` |
| `c⋆ ≤ 5`, `6`, `12` (earlier) | `cStar_le_five`, `cStar_le_six`, `cStar_le_twelve` | `UniformBadFive`, `UniformBadCount`, `UniformBadTwelve` | |
| Perfect-power bases are free | `admissible_iff_nonPerfectPow` | `UniformBadThreshold` family | |

Pushing the lower bound further by small-base certificates is not worth the cost.  That is a resource decision, not a statement about `c⋆`.  The upper side is stuck near 4.96.

## Lower side: finite certificates, and why they stop at ≈ 2.5138

A lower bound `c ≤ c⋆` follows from `¬ Admissible c`.  We prove that with a finite exact cover of `[0, 1]` by windows `{ξ : ‖bⁿξ‖ ≤ b^{−c}}`, checked by the kernel (`not_admissible_of_cert`).  The 729/290 certificate has 95 windows from bases `≤ 10`.

An exact rational probe, `scripts/uniformbad_cstar_probe_scaled.py`, used every base `b ≤ 30` and every `n` with `bⁿ ≤ 10¹²`.  The survivor set is empty for `c` below about **2.5138155** and nonempty above it.

- **The last survivors** are the family of `241/1365`.  Its binary orbit has period 12 and stays at distance `239/1365` from the integers, so it dies at `c = log₂(1365/239) ≈ 2.5138184`.
- **Every base below 1365 keeps `241/1365` alive at `c = 2.514`, for every `n`** (`goodBelow_241_1365`, proved).  The reason is that `1365 = 3·5·7·13` has Carmichael exponent `λ = 12`, so every base has a short orbit mod 1365.
- **So no finite cover can pass `c = 2.514` without using a multiple of 1365 as a base.**  About `2·10⁻⁵` is available before that small-base obstruction.  Covers that use larger bases could go further, and how much further is not bounded.
- **An earlier apparent plateau** at `log₂(257/45)`, from the 16-cycle of `77/257`, was an artifact of short horizons.  `3` is a primitive root mod `257`, so base 3 kills `77/257`, but only near `n = 128`.

The finite threshold is **not** an estimate of `c⋆`.  It only says where small bases with bounded horizons stop excluding points.

## Upper side: what has been tried, and the walls

An upper bound needs an infinite construction of one `ξ`.

| Mechanism | Best exponent | Status |
|---|---|---|
| Square-root stage potential, early charging (`UniformBad`) | 24 | proved |
| Power engine | 12 | proved |
| Counting engine: kills charged to alive ancestors, base 2 exact through its runs | 6 | proved |
| Two-rate counting: base 2 exact at threshold `33/1024`, base 3 counted | 5, then **124/25** | proved |
| Same engine at 9/2 | no | **wall, proved**: `not_nineHalvesBalance` (the balance fails by about 0.08) |
| The defined per-stage engine `PerStage.Cert` (fixed patterns, levels 40..181), even charging only bases 2 and 3 | no at 9/2 | **wall for that engine, proved**: `not_perStageCert`.  It is not a theorem about all local constructions.  The local engines we tried stall near `c ≈ 4.55` |
| Newhouse thickness / gap lemma (`UniformBadNewhouse`) | would need a thick core | **open, unresolved**: `merge_forced` is a necessary merging condition, not `¬ThickCore`.  `thickCore_four` is still a sorry, blocked on uniform control of merge cascades |
| Rational towers (limits of rationals good for all small bases) | would give `c⋆ ≤ 4` | **refuted unconditionally, at every `c`** (Codex), see below |

**The current engine diagnosis behind the 9/2 wall (a diagnosis, not a proved necessity).**  Three independent local mechanisms meet at the same threshold.  Pessimistic counting pays about `0.12` per base-3 kill level, while the exact joint `{2,3}` tree loses only about `2.4%`.  So the loss comes from the worst-case placement of base-3 windows relative to the base-2 survivors, not from the bookkeeping.  Our diagnosis is that beating 9/2 needs a **non-local** input: where the windows `k/3ⁿ` fall among the binary cells that survive base 2.

### The rational-tower attempt (2026-10-08), refuted

- **The idea (Ren's).** The extremal survivors are *self-good rationals*: `p/q` that are good for every base below `q`, at every `n`.  A family of rationals, each approximable arbitrarily well by members good below any base bound, would yield an admissible limit.  `admissible_of_towerFamily` proves that implication, and `towerFamily_singleton_of_admissible` (Codex) is its positive control.
- **Why it can never work (Codex, `not_rationalTower`, standard axioms only).** Take a rational `r = p/d` in the family.  At base `2d` and `n = 1`, `‖2d·y‖ ≤ 2d·|y − r|`, so every `y` within `(2d)^{−1−c}` of `r` fails base `2d`.  The tower condition demands survivors arbitrarily close to `r`.  So `RationalTower c` is false for **every** `c`, and `SelfGoodPerfect c` with it (`not_selfGoodPerfect`).  More generally, an admissible `ξ` has `|ξ − p/q| > q^{−1−c}` for all `p/q`.
- **What this supersedes.** It replaces the lap's conditional refutation (`not_selfGoodPerfect_four_of_coset`, via `CosetSurvival` and Corvaja–Zannier).
- **What it does not settle.** It does not prove `JointRationalsFinite`, does not locate `c⋆`, and does not rule out every convergent sequence of good rationals.  That weaker condition is recorded as `ConvergentGoodRationalSequence`.

## What the numerics say about the true value

- **The finite systems go thin, not empty, just above 2.5138.**  At `c = 2.52` to `2.6`, survivors persist with all bases `≤ 3000` and windows down to radius `10⁻¹³`.  At `c = 2.55` the number of surviving intervals grows with the resolution (606, 1066, 1762 at radii `10⁻¹¹, 10⁻¹², 10⁻¹³`), which looks like a Cantor set of dimension about 0.2.  At `c = 3` survivors are abundant.
- **But every survivor family seen so far sits near a binary-periodic rational** `p/(2^m − 1)` or a small-`λ` denominator.  Those families die once the base reaches the denominator, and new families with longer periods replace them.  Whether the limit of those families survives every base is exactly the open question.
- **Stated beliefs:**
  - The lap's 60% for `c⋆ ≤ 13/5` and my 60% for `c⋆ ≤ 3` are withdrawn.  The finite-horizon data cannot tell "near 2.52" from "substantially higher".  The 77/257 plateau that vanished at a deeper horizon is the known-answer warning.  The interval growth across resolutions is evidence about the truncation, not an asymptotic dimension.
  - The Lean docstrings still carry the old figures (35% on `CStarLeThree`, 60% on `CStarLeThirteenFifths`).  They are stale and will be reconciled.
  - The frozen headlines `cStar_le_four` and `cStar_le_nine_halves` are open walls.

So the honest picture is `c⋆ ∈ [2.5138, 4.96]` proved, no calibrated estimate inside that range, and no mechanism that gets the upper bound below 9/2.

## Questions for a second opinion

1. **Where is `c⋆`?**  Is there a heuristic or argument that the true value is near 2.52, or much larger?  The survivors near threshold are all near rationals, which could mean the thin Cantor-like survivor set collapses at larger bases.
2. **A non-local `{2,3}` mechanism.**  We need a set of `ξ` with explicit control of both `‖2ⁿξ‖` and `‖3ⁿξ‖`, plus room for the other bases, at exponent below 9/2.  Candidates we have not built:
   - a substitution or Sturmian-type `ξ` copying the survivors' binary block structure;
   - Schmidt games with explicit constants;
   - a Falconer–Yavicoli countable-intersection-of-thick-sets argument.  This was already rejected once (its constant `K₂ = 240` is too large), so it needs a changed quantitative input to be reconsidered.

   Codex's verdict: none of these names alone supplies the missing base-3 estimate, and the route map should be corrected before choosing another engine.

   Does any of these look viable, or is there a standard tool we are missing?
3. **Literature.**  Is any explicit uniform exponent known for "badly approximable to bases 2 and 3 simultaneously"?  Is `JointRationalsFinite` known: only finitely many rationals whose orbits under ×2 and ×3 both avoid `b^{−c}`-neighbourhoods of the integers?  It looks close to Bugeaud–Corvaja–Zannier.
4. **Sanity.**  Does anything in the definitions (`Admissible`, `cStar`, `GoodBelow`, `TowerFamily`) or in the reductions look wrong or vacuous?

## Where to look

- **Definitions and early bounds:** `src/NormalNumbers/UniformBadThreshold.lean`.
- **The engines:** `UniformBadCount.lean`, `UniformBadFive.lean`, `UniformBadBelowFive.lean`.
- **The walls:** `UniformBadNineHalves.lean`.
- **Newhouse:** `UniformBadNewhouse.lean`.
- **Lower bounds:** `UniformBadLowerBound.lean`.
- **The towers and this round's results:** `UniformBadTower.lean`.
- **Run directive and history:** `DIRECTION.md`, first section.
- **Every lap's notes:** the `HANDOFF-*.md` files.
- **Probes:** `scripts/uniformbad_cstar_probe_scaled.py`, `scripts/uniformbad_selfgood_rationals.py`, `scripts/uniformbad_carmichael_density.py`, and `scripts/cstar_models/` (the lap probes: `cover2.py`, `surv.py`, `joint_rationals.js`, `gcd_budget.py`, `coset_survival_check.py`).

## Codex review (2026-10-09), literature pointers

- **Peres–Schlag**, arXiv:0706.0223, Thm 3.1 (unions of lacunary sequences): specialized to `{2ⁿ} ∪ {3ⁿ}`, it gives `‖2ⁿξ‖, ‖3ⁿξ‖ ≥ 1/1920` for some `ξ`.  Recorded as `PeresSchlagTwoThreeBound`.  It is a coarse two-base bound and does not cover the other bases.
- **Corvaja–Zannier**, arXiv:math/0311030, Cor. 1 and (1.3): supports the gcd input, but not `CosetSurvival`.
- **Li–Li–Wu**, arXiv:2204.07357 (rationals in ×b-invariant sets): restricts the denominators' primes to a fixed finite set, so it does not settle `JointRationalsFinite`.
