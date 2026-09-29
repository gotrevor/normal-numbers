# Handoff — 2026-09-29 — joint Lambert quantitative foundations (small prime pool)

Branch `proof/joint-lambert-unconditional`, baseline `daedc1e`. Full `lake build` green.
All four deliverables of `KICKOFF-2026-09-29-joint-lambert-small-pool.md` are proved,
`#print axioms`-clean (`propext, Classical.choice, Quot.sound`), audited by
`scripts/check-joint-lambert-smallpool.sh`. Every pre-existing `JointLambert*.lean`
is byte-for-byte identical to `daedc1e` (verified per-file); only two new modules and
two root imports were added.

## What landed

`src/NormalNumbers/JointLambertGcdAverage.lean`
* `tau_mul_le : τ(mn) ≤ τ(m)τ(n)` — unconditional, through `Nat.divisors_mul`
  (divisors of a product are the pointwise product) and `Finset.card_mul_le`.
  Generalizing to `m = 0` or `n = 0` is free here, so the positive statement is
  not weakened, it is subsumed. `tau_prod_le` is the finite-product form.
* `sum_tau_progression_le_gcd` / `sum_tau_progression_le_noncoprime` — equation (1)
  of the note: `∑_{m<M} τ(u+mA) ≤ τ(gcd u A)·(2M(1+log H)+2H)`, resp. with `τ(A)`.
* `jointA_tau_le` — equation (2): `τ(A) ≤ (a+1)(c+1)^(k²)`.

`src/NormalNumbers/JointLambertSmallPool.lean`
* `eventually_small_prime_pool` — `∃ K, ∀ k ≥ K, ∀ r,
  1 + killPoolSize k r + 1 ≤ #{p prime : k³ < p < 2k³}`; `k` stays caller-chosen.
* `exists_prime_allocation_small_pool` — the allocation corollary; the spare `+1`
  pays for the single excluded `P(X)`.

## The mathematical gain

The old schedule drew the congruence primes from near `(log X)²`, which forced
`log B = O((log log X)³)` and hence the count `N exp(-C (log log N)³)`. Drawing them
from `(k³, 2k³)` with `k = ⌈4 log₂ log X⌉` gives `log B = O_c(k² log k)
= O((log log N)² log log log N)`, i.e. the sharper `N exp(-C (log log N)² log log log N)`.

The price is that the middle tail `k³ ≤ j < J` loses coprimality with `A`, so the
divisor average must be paid at `τ(A)` instead of `1`. `jointA_tau_le` is exactly
what makes that affordable: the middle-tail cost is
`(a+1)(c+1)^(k²) · 2^(-k³)`, whose logarithm is `O_a(1) + k² log(c+1) − k³ log 2 → −∞`.
The cube in the pool is what beats the square in the divisor count. This is the
structural reason the route works, and it is now machine-checked rather than
asserted.

Two traps were live and are now controlled in-file: the divisor average must NOT
assume `gcd(g, A/g) = 1` (the `u=6, A=12` control has `gcd(6,2)=2`, and the bound
`18 ≤ 20` is strict, not an equality), and `jointA_tau_le` must be stated as an
UPPER bound, since with repeated allocation primes the exact product formula fails
(the `q = p = 3` control gives `τ(A) = 5`, not `9`).

## Exact next boundary

Everything elementary is done. The next obligation is the *analytic consumer*, in
two named pieces:

1. **Prime supply at each chosen height `X`.** The installed
   `exists_pointwise_exponential_distribution` (`JointLambertAGPRange.lean`) must be
   instantiated at `B = jointB` with `log B = O_c(k² log k)`, `k = ⌈4 log₂ log X⌉`,
   to yield `π(X;B,u) ≥ X/(2 φ(B) log X)` for EVERY sufficiently large `X` — not for
   some `X` returned by an existence theorem. The needed decay is
   `log B + log log X − γ√(log X) → −∞`, which at this schedule is comfortable;
   `B ≤ X^{1/3}` eventually. No AGP is required: the bases are fixed.
2. **The three-range good-set COUNT.** Assemble near (`k ≤ j < k³`, coprime, existing
   averaging), middle (`k³ ≤ j < J`, `sum_tau_progression_le_noncoprime` +
   `jointA_tau_le`), far (`j ≥ J`, `τ(n) ≤ 2√n`), then Markov at the fixed threshold
   `2δ`, and keep the CARDINALITY of the surviving set rather than extracting one
   witness as the qualitative proof does. Then §5's all-`N` conversion.

Not in scope and deliberately untouched: AGP, full normality, Vandehey work.
