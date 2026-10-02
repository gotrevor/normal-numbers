# Kickoff — 2026-09-29 — joint Lambert small prime pool

Trevor authorizes this run ("Do the next thing!"), at most THREE laps, Opus/low.
Work ONLY in this worktree on `proof/joint-lambert-unconditional`, baseline `daedc1e`.
This objective supersedes inherited Vandehey and AGP directives for THIS worktree.

**Mathematical purpose.** Replace the congruence primes near `(log X)^2` by primes
near `k^3` with `k = ceil(4 log_2 log X)`, so the eventual synchronized occurrence
count improves from `N exp(-C (log log N)^3)` to `N exp(-C (log log N)^2 log log log N)`.
The new step pays `tau(A)` for a NON-COPRIME middle tail; since
`tau(A) <= (a+1)(c+1)^(k^2)`, the factor `2^(-k^3)` beats that cost.
This run proves the elementary foundations and prime-pool supply only, NOT the
full occurrence-count headline.

**Deliverables** (namespace `NormalNumbers.JointLambert`, new modules only):

1. `tau_mul_le` — `SwingC2.tau (m*n) <= tau m * tau n` for positive `m,n`.
2. `sum_tau_progression_le_gcd` / `sum_tau_progression_le_noncoprime` —
   `∑_{m<M} tau(u+mA) <= tau(gcd u A) * (2M(1+log H)+2H)` (resp. `tau A`),
   for `u>0, A>0, H>=1` and `u+mA <= H^2` for all `m<M`.
3. `jointA_tau_le` — `tau (jointA c a k r q p) <= (a+1)*(c+1)^(k^2)`.
4. `eventually_small_prime_pool` — for every sufficiently large `k` and EVERY `r`,
   `1 + killPoolSize k r + 1 <= #{p prime : k^3 < p < 2k^3}`.

Files: 1–3 in `src/NormalNumbers/JointLambertGcdAverage.lean`,
4 in `src/NormalNumbers/JointLambertSmallPool.lean`. Root import added.

**Constraints.** Freeze every pre-existing `JointLambert*.lean` byte-for-byte at
`daedc1e`. No new opaque hypothesis `Prop`s standing in for these obligations.
Permanent `example`-style Lean controls in the same modules (M=0; u=1,A=4,M=3;
u=6,A=12,M=3 with `gcd(6,2)=2`; a repeated-prime `jointA` case; pool exclusion
cases). Do not rerun the qualitative campaign, prove AGP, or chase normality.
