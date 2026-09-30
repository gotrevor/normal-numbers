# Quantitative C′: discrepancy from bounded fresh mass

Ren, 2026-09-30, attended.  Paper-level derivation, **refereed once** (independent subagent, same day: no false step; ~85% `CPrimeQuant`, ~80% `CPrimeResidueRich`; its fixes are applied below).  Frozen statements:
`src/NormalNumbers/CPrimeQuantStatement.lean` (`CPrimeQuant`, `CPrimeResidueRich`), compile-checked.
Source proof: `papers/ROUND2-multicutoff-astra.md` §§2–11, Lean `PrimeModelFamilyGraded.lean`.

## Claim

Let `P` be a set of primes with `Σ_{p∈P} 1/p = ∞`.  Let the square-root fresh mass
`r_P(N) = Σ_{√N<p≤N, p∈P} 1/p` satisfy `limsup r_P(N) ≤ ρ`, with `ρ ≤ ρ₀`.  Then the orbit
`4ⁿ x_P mod 1` of `x_P = Σ_{p∈P} 1/(4ᵖ−1)` has asymptotic interval discrepancy
`≤ C ρ log³(1/ρ)`, for an absolute constant `C`.

**Corollary (residue classes).**  Primes `≡ a (mod q)` have `ρ = log 2/φ(q)`, by Mertens in
progressions.  So the discrepancy of `Σ_{p≡a (q)} 1/(4ᵖ−1)` is `O(log³φ(q)/φ(q))`, uniformly in `a`.
Every base-4 word of length `L` then has lower frequency at least `4^(−L) − C log³φ(q)/φ(q)`.  So
every word of length `L` has positive lower frequency once `q ≥ q₀(L)`.

These would be the first frequency statements about a prime-Lambert constant built from a natural
prime set.  At `ρ = log 2` (all primes, G₄) the bound is trivial, as it must be.

Confidence the argument is correct: about 80%, after the referee pass.  That the corollary is new: about 70%, by
a literature check of the C′ neighbourhood only.

## Why it works: with `u` fixed, only the transfer term carries `ρ`

C′ bounds the window mean `W_h(N)` (the prefix mean of `e(h·4ⁿ x_P)`, truncated to `J` digits).  The
bound is a sum of four terms (`windowMean_le_terms`: `termE1`, `termE4a/b/c`, `termE5`).  The
schedule is `(8.1)`: `J = min(⌊L3 N⌋, ⌊S_N/8⌋)`, cutoffs `y_j = ⌊N^(u⁻²·2⁻ʲ)⌋`, integer `u`.

Now **fix `u`** instead of letting `u_N → ∞`, and keep everything else.  Three terms used the divergence: E1 (transfer), E4a (`e^(−u²/32) → 0`) and E4b (`e^(−u) → 0`).  With `u` fixed, E4a and E4b become constants `O(e^(−u))`, carried in the bound below.  The transfer term is the only one that grows with `ρ`.

| term | paper | with fixed `u` and bounded `ρ` |
|---|---|---|
| cutoff range, `y_J ≥ exp(√log N)` | §8 | unchanged: needs only `u² ≤ L3 N`, true eventually |
| support budget | (8.2): `log R/log N ≤ (278+4u)/u²` | `R ≤ N^(1/8)` holds iff `u ≥ 66`, but it is only sufficient: the CRT remainder needs `2 log R/log N + (√2+1)/16 < 1`, i.e. `u ≥ 31`.  Below about `u = 35–40`, E4a's `e^(−u)`-sized constant swamps `ρ`.  **The Lean path is worse**: `termE4c_tendsto`'s constants need `u ≥ 3000` as written, or about `u ≥ 176` retuned within its own slack |
| joint error E4 | (5.3), (8.4) | `≤ 4e^(−u) + 2e²⁰·e^(−u²/32)/(e^(u²/128)−1) + o(1)`; the radical term is below `e^(−100)` at `u = 66` |
| model contraction E5 | (5.4), (8.6) | still `→ 0`: `S_P(2J, y_{j₀}) ≥ S_N − O_{u,ρ,j₀}(1) − log 2J`, while `J ≤ S_N/8` |
| infinite phase tail | §8 end, `tail_graded` | still `→ 0`: needs `S_P(N,2N) ≤ 1`, true since `ρ ≤ ρ₀ < 1` in the statement |
| **transfer E1** | (2.1) | **the term linear in `ρ`** (below) |

**Transfer.**  By (2.1), `|W − W_y| ≤ Σ_j a_j·[2 S_P(y_j, N) + J/N]`, with `a_j = |e(h/4ʲ) − 1|`.
The paper bounds `a_j ≤ 4π|h|4⁻ʲ`; we use the sharper `a_j ≤ min(2, 2π|h|4⁻ʲ)`.  The root chain
(11.3), with `log(2N)/log y_j ≤ 4u²2ʲ`, gives

    S_P(y_j, 2N) ≤ (ρ+ε)·(c_u + j),         c_u = 3 + 2 log₂ u.

Let `k = ⌈log₄|h|⌉`.  Splitting the sum at `j = k`:

    limsup_N |W_h(N)| ≤ 2ρ·[ 2(k c_u + k(k+1)/2) + 2π((c_u + k)/3 + 4/9) ]
                        + 4e^(−u) + e^(−100).

So `|W_h| = O(ρ(log²|h| + log u·log|h| + log u)) + 4e^(−u)`: polylogarithmic in `h`, where the
paper's cruder `a_j` bound gave a linear dependence.

## From Weyl sums to discrepancy

Erdős–Turán (Kuipers–Niederreiter Thm 2.5):

    D_N ≤ 6/(H+1) + (4/π) Σ_{h≤H} |W_h(N)|/h.

Take `H = ⌈1/ρ⌉` and `u = max(66, ⌈log(1/ρ)⌉)`.  Then `Σ_{h≤H} log²h/h ≈ log³H/3` and
`4e^(−u) log H ≤ 4ρ log(1/ρ)`.  The result is `limsup D_N ≤ C ρ log³(1/ρ)`.  A word `w` of length
`L` is a visit of the orbit to a 4-adic interval of length `4^(−L)`, so its frequency error is at
most `D`.

**Sizes: the displayed bound evaluated numerically, constants untuned.**

| `ρ` | `D` | what it gives | modulus |
|---|---|---|---|
| `10⁻³` | 2.55 | trivial | `φ(q) ≈ 690` |
| `10⁻⁴` | 0.42 | trivial for words | `φ(q) ≈ 6 900` |
| `10⁻⁵` | 0.064 | each base-4 digit's lower frequency `≥ 0.186` | `φ(q) ≈ 69 000` |
| `3·10⁻⁶` | 0.023 | every length-2 word has positive lower frequency | `φ(q) ≈ 231 000` |
| `10⁻⁶` | 0.009 | every length-3 word has lower frequency `≥ 0.0066` | `φ(q) ≈ 690 000` |

The cost is dominated by `c_u` through the `u` floor.  On paper `u` can drop to about 35–40.  With the Lean path's current constants (`u = 3000`, `c_u = 26.1`) every `D` rises about 1.6×: `ρ = 10⁻⁵` gives 0.101 and `ρ = 10⁻⁶` gives 0.014, so length-3 words survive at lower frequency `≥ 0.0016`.  Numeric check: the referee reproduced this table exactly.

## Referee findings and build gaps

**Verified**, all as OK:
- the sharper `a_j` bound enters (2.1) cleanly;
- the chain length `⌈log₂(4u²2ʲ)⌉ ≤ 3+j+2log₂u`, and the closed j-sum;
- contraction and tail under bounded `ρ`;
- the Erdős–Turán step;
- both frozen statements are faithful: `CPrimeQuant` is non-vacuous, and `ρ → 0` recovers C′.

**Lean-path work the campaign must do:**
1. **Refactor the schedule.**  `uG` builds in `εu² ≤ 1` (`epsG_mul_uG_sq_le`).  Restate
   `recipSumIoc_yG_le` as `ρ′(j+2+2log₂u)`.  Relax E5's `htail ≤ 1` to a bounded `K_h`; the
   majorant `e^(22+K_h)(2J)^12 e^(−6J)` still tends to `0`.
2. **Retune `termE4c`** (or sharpen `gradedLevel`) so a moderate constant `u` suffices.
3. **Sharpen `siteBudget`** (`4π|h|4^(−(j+1))`) to `min(2, 2π|h|4⁻ʲ)` upstream in
   `PrimeModelKMTGraded`.
4. **Quantitative Weyl wiring.**  `isNormal_subsetLambert_of_KMT_along` is qualitative.  The orbit
   Weyl sum differs from `windowMeanS` by at most `2π|h|·TailOK`, and this needs writing out.
5. **Erdős–Turán**, not in the build.  A single-interval Fejér sandwich is enough.
6. **Mertens in progressions, upper bound.**  `G4MertensAP` gives only the lower bound
   (`MertensRate`).  The corollary needs `r_P → log 2/φ(q)`, or Brun–Titchmarsh's
   `≤ (2+o(1)) log 2/φ(q)`.

## What it does not do

It gives no cancellation among the fresh primes.  The transfer term is a triangle inequality over
the unfrozen primes in `(y_j, N]`, and a positive-density `P` leaves a defect linear in its fresh
mass.  Reaching G₄ still needs cancellation *inside* that mass: the same wall as C1/C3.  The
quantitative theorem measures the wall's thickness; it does not thin it.

**The next research question this opens.**  Is the linear-in-`ρ` defect sharp for this
architecture, or do the fresh primes cancel?  An instrument: compare `|W_h − W_{y,h}|` with its
triangle bound numerically on residue-class sets.  A large gap would locate the cancellation G₄
needs in a controlled family, before attempting it at `ρ = log 2`.
