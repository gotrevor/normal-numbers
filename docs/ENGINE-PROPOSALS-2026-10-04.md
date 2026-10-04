# Engine proposals, 2026-10-04

Direction doc.  Each proposal names the engine, what it opens, the barrier it gets around (or the guard it adds), its first Lean deliverable, and a success estimate for that deliverable.  Nothing here is a result; anything adopted gets a Lean statement before work starts.

## Current engines and anti-tools (for reference)

Engines: Fourier decay to a.e. normal to computable via derandomization (`ComputableNormalB`, `FamilyDerandomize*`, `SchedDerandomize`, `SchedFamily`); cylinder-cut decay through inflection points (`ExplicitOmegaK`, `ExplicitPQ`); Cassels second moment with forced zero runs (`CantorLiouville*`); nested-interval potential (`UniformBad.exists_avoid_of_stagePotential`); missing-digit measures plus mass distribution (`DigitCantor`); packing covers (`DeterministicBD`); sparse perturbation plus discrepancy (`LevinSparse`); multiplicative digit identities plus correlation inputs (`Erdos257*`, `JointLambertQuantitative`, `ElliottLedger`).

Anti-tools: Maze rows plus `#maze_audit`; guards such as `not_uniformBad_of_third_le`, `not_isNormal_six`, `not_approxGPfamClaim`; barriers `not_polyDecay_sparse_of_densityZero`, `not_logDecay_sparse_of_littleLog`; the `ElliottLedger` finding that log-averaged two-point Elliott does not reach the natural-average `CastingOut` route.

## E1. Constructive Schmidt games ⭐

**What.**  A Lean (α,β)-game and absolute-winning layer: winning sets, countable intersection, full Hausdorff dimension, and the observation that a *computable* winning strategy played against a computable opponent yields a computable point.  `UniformBad`'s nested-interval potential is already a one-off winning strategy; this makes it a reusable algebra.

**Opens.**  Dimension upgrades of existence results (is the set in Bugeaud 10.36 of full dimension, and how does it behave on Cantor sets via absolute winning); countable conjunctions in one step (BAD, non-dense orbit in every base, avoidance of a fixed target in every base); computable points in all of these.

**Guard.**  The set of base-b normal numbers is not winning (its complement is), so no game argument proves normality.  First Lean statement: that non-winning theorem as a guard, beside `winning_iInter` and `dimH_eq_one_of_winning`.

**Pairing.**  Normal and winning-type conditions together still need a decaying measure on the winning set (Kaufman, Queffélec-Ramaré, Sahlsten-Stevens style); E1 supplies the set, the existing derandomizers supply the point.

**First deliverable / estimate.**  `winning_iInter` + `dimH_eq_one_of_winning` + the 10.36 set reproved as winning: 60%.

## E2. Logarithmic-average digit statistics (wild numbers)

**What.**  A rung on the word-count ladder between `count ≥ N^{1-ε}` and normality: word frequencies under logarithmic weights `Σ_{n≤N} 1/n`.  Natural-average normality implies the logarithmic version; the converse fails in general, so this is a strictly weaker, genuinely new rung.

**Why now.**  `ElliottLedger` reduces `TwoPointElliottLog` to one cited input (Vinogradov-Korobov at near-maximal height), and nothing consumes it because the digit route wants the natural average.  A log-averaged `CastingOut` variant would consume it directly.

**Opens.**  Log-averaged two-word statistics for `Σ_{n} ω(n)/bⁿ` and, via the Lambert identity, for the #257 sums: the first positive-frequency statement about a constant defined without a construction.

**Crux.**  Whether the carry and casting-out steps survive logarithmic weighting.  Known-false sibling to test first: a sequence with correct logarithmic statistics and wrong natural statistics, to confirm the rung is distinct and the statement is not secretly natural-average.

**First deliverable / estimate.**  The log-averaged `CastingOut` statement frozen with its wiring to `TwoPointElliottLog`: 50%.  The full two-word theorem: 25%.

## E3. Finite-state gamblers and selection (non-Fourier normality)

**What.**  Normality as finite-state incompressibility (Schnorr-Stimm; Dai-Lathrop-Lutz-Mayordomo), Agafonov's selection theorem, and Kamae's characterization of normality-preserving selections (deterministic, positive density).

**Opens.**  Normality-preservation questions (which digit operations, selections, and relabelings preserve normality; Becher-Carton-Heiber and Vandehey questions; the earlier Pulari relabeling candidate), with a combinatorial proof route that needs no Fourier decay.  Kamae and Weiss also connect directly to `DeterministicBD`.

**First deliverable / estimate.**  Agafonov's theorem for base b in Lean, plus one normality-preservation answer from a sweep: 45%.

## E4. Linear forms in logarithms as scale separation

**What.**  Baker-Wüstholz / Matveev as a `Literature.*` Prop, used to control how the scales `p^m` and `q^n` interleave for multiplicatively independent `p, q`.

**Opens.**  Quantitative multi-base constructions: avoidance across finitely many bases with explicit rates, and the explicit side of ×2×3 questions.  It also lets us state the Stoneham family cleanly (`Σ_k 1/(3^k 2^{3^k})` is normal in base 2 and not in base 6, Bailey-Crandall and Bailey-Borwein) and ask the profile question for that family: for which bases is it normal.

**First deliverable / estimate.**  Matveev Prop (refereed) plus a multi-base avoidance theorem with a rate the current potential engine cannot give: 35%.

## E5. Entropy engine (Host, Hochman-Shmerkin)

**What.**  `Literature.*` Props for Host 1995 and Hochman-Shmerkin 2015: ×p-invariant ergodic measures of positive dimension give almost every point normal in base q when `log p / log q` is irrational.

**Opens.**  Normality profiles for typical points of measures with **no** Fourier decay, which our Fourier engines cannot touch.

**Crux.**  Our derandomizers need rates and these theorems give none.  The proposal is effective rate extraction from local entropy averages.  Absent that, the Props still give a.e. statements for profile questions.

**First deliverable / estimate.**  Refereed Props plus one new profile theorem at the a.e. level: 40%.  A computable version: 15%.

## A1. Barrier library (anti-tool)

**What.**  A `Barriers/` namespace of known-false siblings with their properties proved in Lean: Stoneham numbers (normal in base 2, not in base 6); a sequence that matches all order-≤k statistics and is not normal; a log-normal but not normal sequence (E2's sibling); the Cassels-type Cantor points that are normal iff `3 ∤ b`.  Each frozen crux names the sibling its mechanism must fail on, and a `#barrier_audit` check fails the build when a frozen crux names none, as `#maze_audit` does for Maze rows.

**Why.**  This is the difficulty check (named implications, unproved premise, mechanism, and a known-false sibling) turned from prose into a build check.

## T1. Prior-art instrument

**What.**  A `prior-art <arXiv-id or phrase>` CLI: `papers followups`, the asker's and named experts' newest arXiv papers, exact-phrase arXiv API queries, and `formal-conjectures` PR search, appending a dated search log to the sweep doc.

**Why.**  Sweeps missed prior art three times (Manai 2609.24665, Duverney-Tachiya 2019, partly Falconer-Yavicoli).  The audit step caught each, but late.

## Recommended order

1. T1 (cheap, removes a repeated failure).
2. E1 as the next lane, after the current sweep's pick.
3. E2 as the wild-number bet, since it is the only proposal aimed at a constant nobody constructed.
