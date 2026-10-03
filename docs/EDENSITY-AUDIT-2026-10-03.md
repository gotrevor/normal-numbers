# Audit: density rungs for the binary words of the Erdős–Borwein constant (2026-10-03)

**Verdict: no rung is freezable.**  Recorded as Lean in `src/NormalNumbers/EDensityAudit.lean`
plus two `Maze` walls ("CRT freezing for density of the binary words of E", "free 2-adic kill
plus forced band for E").  Branch `audit/edensity`.

## Grades (confidence that an audit plus 2–4 treadmill laps land it)

| rung | statement (`EDensity.*`) | true | lands in 2–4 laps |
|---|---|---|---|
| R1 | `RungPolylog`: count `≥ N/(log N)^A` | ~95% | ~3% |
| R1 for `0^K` only | `ResidualSmallPolylog` (+ an unbuilt bridge to `eCount K 0`) | ~95% | ~8% |
| R2 | `RungRich`: count `≥ cN` | ~97% | ~1% |
| R3 | `RungFair κ` | ~90% (κ = 1) | <1% |

Proved edges: `rungRich_of_rungFair`, `rungPolylog_of_rungRich`,
`residualSmallPolylog_of_often`.  Baseline: `eCount_power` (= `jointWords_power_count`, `S = {2}`).

## Difficulty check

**Proved implications.**  Freezing: CRT witnesses `n = R + mA` with `n + r = Qp` give every word
at `≥ N exp(−C (log log N)² log log log N)` offsets.  New here:
`two_pow_oddExpCount_dvd_card_divisors` (`2^{ω_odd(m)} ∣ τ(m)`), so in
`frac(2ⁿE) = frac(Σ_{j≥1} τ(n+j)/2^j)` every position with `j ≤ ω_odd(n+j)` is an integer
(`fract_card_divisors_div_two_pow_eq_zero`).  For typical `n` that kills all `j ≤ (1−ε) log log n`
for free.  This is base-2 (and `2^k`) specific; nothing like it holds for odd bases or for `ω`.

**Why freezing stops at `N^{1−o(1)}`.**  The tail `Σ_{j≥k} τ(n+j)/2^j` has mean `(log N)·2^{−k}`,
so a deterministic construction must control `k ≥ log₂ log N` positions.  Killing position `j`
costs `j+1` CRT primes, so `log A ≍ k² log k`.  The writer needs an exact `τ`, which needs a
prime (`1/log N`).  All witnesses lie in one residue class mod `A`, so density `≤ 1/(A log N)`.

**Unproved premise.**  After the free kill, the digits at offset `n` are decided by a band
`j = log log n ± O(√(log log n))`: there `ω_odd(n+j) ≈ j`, and each position contributes an O(1)
fraction unless it is killed (`ω_odd ≥ j`) or small (`τ(n+j) ≪ 2^{j−K}`).  Heuristically the
expected number of "problem" positions is `O(K)`, so the band is clean with probability bounded
below.  That is `ResidualSmallOften` (for the word `0^K`).  A general word additionally needs
one writer position with exactly prescribed `τ`, i.e. an exact count of prime factors including
the large ones.  That is parity-sensitive: the joint local Erdős–Kac input already named at
`Erdos257Squarefree.SqfreeBinaryDisjunctive`.

**Mechanisms for the premise.**
- Force-kill the band: `≳ log log N · log log log N` primes, primorial `(log N)^{c(log log log N)²}`.
  Gives only `N/(log N)^{C(log log log N)²}`, still short of R1.  It also needs moderate-deviation
  Erdős–Kac for shifted primes `Qp + h` in progressions, which is BV-level and absent from
  mathlib/PNT+.
- Sieve (Kubilius model) in dimension `≍ log log N` over the integers: remainders are trivial,
  but large primes cost a margin `≍ log log log N` per band position.  That gives
  `(log log N)^{−C}` for `0^K` (so R1 for the zero words, ~25% on paper), and it is not monotone,
  so FKG is unavailable.  General words fall back on shifted primes (BV) plus the writer.
- No mechanism is known for R2 for general words.  This is HEADLINES H1 item 3 ("count it with C3").

**Sibling test.**  A method that reads only `τ mod 2` sees `Σ_k 2^{−k²}`, whose `1`s have
density 0: `card_odd_card_divisors_le` (`≤ √N + 1` odd divisor counts below `N`).  The band
heuristic passes this test, because it uses `v₂(τ) ≈ ω`, not the low bit.  The CRT construction
has no analogue there, since being a square is not a congruence condition.  No numerics:
`log log N ≈ 3.3` at `N = 10¹²`, so the band is invisible at computable scales (same caveat as C1).

## Prior art (checked 2026-10-03)

- Crandall, *The googol-th bit of the Erdős–Borwein constant*, Integers 12 (2012) #A23, §7: asks
  whether one can "even show that 1/2 of the bits of E are 1's".  In the first 2⁴³ bits it
  observes `4436987456570` ones against `4359105565638` zeros, a far larger gap than coin
  tossing predicts.  Erdős (1948) gives a `0`-run of length `c (log N)^{1/10}` in the first `N` bits.
- Campbell arXiv:2605.24160 (`11` recurs; `papers followups`: 0 citing papers).  The CaptainSude
  paper gives a cubic-log count.  Neither gives a density bound.
- Bailey–Crandall 2002 (*Random generators and normal numbers*) treats Stoneham-type `α_{b,c}`.
  `E` is not of BBP/Hypothesis-A form (`x_n = 2x_{n−1} mod 1` exactly), so it does not apply.
- Tao–Teräväinen 2512.01739 followups: Lau 2604.15042 (infinitely many `n` with
  `ω(n+k) ≪ log k` for all `k`, an existence result, not a density result) and Hughes 2609.28526
  (effective log two-point Chowla).  Neither supplies the band premise.
- No density or frequency lower bound for the digits of `E`, `Σ τ(n)/bⁿ` or `Σ ω(n)/bⁿ` was found.
  For `Σ ω(n)/bⁿ` this repo's C3 is the live conditional headline, and the 2-adic kill does not
  transfer to `ω`.
