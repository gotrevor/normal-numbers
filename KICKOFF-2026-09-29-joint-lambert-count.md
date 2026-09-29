# Kickoff — 2026-09-29 — joint Lambert quantitative COUNT

Authorized by Trevor ("do it!"), 2026-09-29.  Worktree
`/Users/gotrevor/src/normal-numbers-lambert`, branch `proof/joint-lambert-unconditional`,
baseline `e2828b32`.  At most six laps / six hours, Opus/low.  This objective supersedes
the completed small-pool campaign and every inherited Vandehey/AGP directive in this
worktree; another session owns Vandehey in the main checkout.

## Status discipline

DONE: the qualitative theorem (`jointWords_unconditional`), the gcd/non-coprime divisor
average (`sum_tau_progression_le_gcd`, `sum_tau_progression_le_noncoprime`,
`jointA_tau_le`) and the small prime pool (`eventually_small_prime_pool`,
`exists_prime_allocation_small_pool`).  The small-pool foundations are proved at
`23b3f2d2`, **not** at the commit label the small-pool handoff mistakenly cites.

NOT DONE: the all-`N` count below.  It is not done until its full dependency chain is
proved — file-local absence of `sorry` is not enough.

## Final target (ratified; meaning and quantifier order frozen)

For every finite set `S` of bases `≥ 2` and every fixed valid nonempty word in each base,
let `A(N)` count offsets `n < N` at which ALL those words start together in their
corresponding `E_b`.  Unconditionally, for some `C > 0` and `N₀`, for EVERY `N ≥ N₀`:

    A(N) ≥ N · exp(-C · (log log N)² · log log log N)

`C, N₀` depend on `S` and its words.  Neither uniformity in all bases nor an effective
computable threshold is required.  Then: for every fixed `ε > 0`, eventually
`A(N) ≥ N^(1-ε)`.

The parentheses are load-bearing: `(-C) * (log log N)^2 * (log log log N)`, not the square
of a product with `C`.

## Frozen Lean surface

* `src/NormalNumbers/JointLambertQuantitativeStatement.lean` —
  `noncomputable def jointWordCount` with classical decidability, on top of
  `NormalNumbers.JointLambertStatement` so `orbit` and `E_b` keep exactly their existing
  meaning.  Permanent boundary controls in-file: `S = ∅ ⇒ count = N`; `count at N = 0` is
  `0`; `count ≤ N`; monotone in `N`; witness and good-set-cardinality bridges.
* `src/NormalNumbers/JointLambertQuantitative.lean` — the two ratified headlines
  `jointWords_quantitative` and `jointWords_power_count`, with permanent audit examples
  for both exact types and for the `{2,4}` specialization (binary `11`, leading-zero
  base-4 word `0`).  Both declaration names must persist; literal syntax/elaboration
  fixes are fine, weakening/re-hypothesizing/deleting is not.

Conventions fixed at statement creation: `n` is an offset and the first requested digit is
`n+1`; words may run beyond position `N`; a syntactically repeated base is represented once
by the `Finset`; small `N` where iterated logs are nonpositive is handled by eventual `N₀`,
not a universal positivity claim; the `ε` theorem is for FIXED `ε > 0` (including `ε > 1`),
with no `ε(N)` substitution.

## Proof order (note §§3–5)

1. At caller-chosen large `X`: `k = ⌈4 log₂ log X⌉`, `L = k³`.  `P = P(X)` from
   `exists_pointwise_exponential_distribution` chosen BEFORE the allocation;
   `exists_prime_allocation_small_pool` avoiding `P` if prime (it also supports `P = 1`);
   CRT from `exists_joint_progression`.  Keep `jointB_le : B ≤ (2k³)^(1+c k²)` and
   `Q ≤ (2k³)^(a-1)`.  Prove `B ≤ X^(1/3)` and `C₀ B log X exp(-γ√log X) → 0` for fixed
   `c, a, r`.  Extract `≥ M/(4 log X)` prime candidates, `M = ⌊X/B⌋+1`; PNT gives
   `π(X) ≥ (9/10) X / log X`.  No reversion to the coarse `B ≤ 2^(k⁴)`; no substitution of
   "some `k ≥ K`" for a chosen-height theorem.  A dyadic `X = 2^t` variant is acceptable
   only with a proved all-`N` transfer preserving the same final rate.
2. `Y = 2QX`, `J = ⌊(log₂ X)²⌋`, `H = ⌈√Y⌉`.  Three-range tail; total cost small relative
   to the candidate count `M/log X`.
3. Markov at the FIXED threshold `2δ`; keep the FINSET CARDINALITY of `≥ M/(8 log X)` good
   prime indices.  Common binary majorant + `floor_digit_of_common_offset`;
   `m ↦ R + mA - 1` injective, `A > 0`.
4. `k_N = ⌈4 log₂ log N⌉`, `D_N = 2(2k_N³)^(a-1)`, `X = ⌊N/D_N⌋`.  Constants fixed BEFORE
   `N`; floors handled explicitly.
5. `jointWords_power_count` from `(log log N)² log log log N = o(log N)`.  No numerical
   frequency claim, no normality conclusion.

## Guardrails

Every pre-existing `JointLambert*.lean` stays byte-for-byte identical to `e2828b32`.  New
helper modules (`JointLambertCountPrimes`, `JointLambertCountTail`, …) plus the statement
and final modules; all in the root import.  No opaque `Prop` assumption may package the
missing work; any new interface gets a content locator and empty/singleton/boundary
controls under the repo guard rule.  Existing full-AGP gaps are irrelevant and untouched.

Stop successfully only when BOTH endpoints are proved with their full dependency chains and
the host build is green (`box done --green`).  Otherwise checkpoint at the cap with the
exact remaining mechanism or a documented refutation.
