# Quantitative C′: discrepancy from bounded fresh mass

Ren, 2026-09-30, attended.  Paper-level derivation, **not yet refereed**.  Frozen statements:
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

Confidence the argument is correct as written: about 75%.  That the corollary is new: about 70%, by
a literature check of the C′ neighbourhood only.

## Why it works: only one term of the C′ proof ever needed `u_N → ∞`

C′ bounds the window mean `W_h(N)` (the prefix mean of `e(h·4ⁿ x_P)`, truncated to `J` digits).  The
bound is a sum of four terms (`windowMean_le_terms`: `termE1`, `termE4a/b/c`, `termE5`).  The
schedule is `(8.1)`: `J = min(⌊L3 N⌋, ⌊S_N/8⌋)`, cutoffs `y_j = ⌊N^(u⁻²·2⁻ʲ)⌋`, integer `u`.

Now **fix `u`** instead of letting `u_N → ∞`, and keep everything else.

| term | paper | with fixed `u` and bounded `ρ` |
|---|---|---|
| cutoff range, `y_J ≥ exp(√log N)` | §8 | unchanged: needs only `u² ≤ L3 N`, true eventually |
| support budget `R ≤ N^(1/8)` | (8.2): `log R/log N ≤ (278+4u)/u²` | holds iff `u ≥ 66` |
| joint error E4 | (5.3), (8.4) | `≤ 4e^(−u) + e²⁰·e^(−u²/32)/(e^(u²/128)−1) + o(1)`; the radical term is below `e^(−100)` at `u = 66` |
| model contraction E5 | (5.4), (8.6) | still `→ 0`: `S_P(2J, y_{j₀}) ≥ S_N − O_{u,ρ,j₀}(1) − log 2J`, while `J ≤ S_N/8` |
| infinite phase tail | §8 end, `tail_graded` | still `→ 0`: needs `S_P(N,2N) ≤ 1`, true since `ρ ≤ log 2 < 1` |
| **transfer E1** | (2.1) | **the only term that does not vanish** (below) |

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

The cost is dominated by `c_u` through the `u ≥ 66` floor from the support budget, so tuning (8.2)
lowers `q₀` directly.

## Review targets (before any campaign)

1. **Fixed `u` really suffices in every Lean-path lemma.**  `schedule_admissible` and
   `yBotG_le_yG` were proved for the adaptive `uG`.  Check that no admissibility clause silently
   uses `uG → ∞`.  The paper checks above say none does.
2. **The sharper `a_j` bound enters (2.1) cleanly.**  It is a pointwise bound on
   `|e(t) − 1|`, so this should be routine.
3. **Mertens in progressions, both directions.**  The corollary needs
   `Σ_{√N<p≤N, p≡a} 1/p → log 2/φ(q)`, or any upper bound `O(1/φ(q))`.  Check what
   `G4MertensAP` and the PNT-in-AP modules actually provide; Brun–Titchmarsh-type upper bounds
   suffice.
4. **Erdős–Turán is not in the build** (only mentioned in docstrings).  It is the one piece of
   known infrastructure the Lean route must add.  A Fejér-kernel sandwich for a single interval is
   enough.

## What it does not do

It gives no cancellation among the fresh primes.  The transfer term is a triangle inequality over
the unfrozen primes in `(y_j, N]`, and a positive-density `P` leaves a defect linear in its fresh
mass.  Reaching G₄ still needs cancellation *inside* that mass: the same wall as C1/C3.  The
quantitative theorem measures the wall's thickness; it does not thin it.

**The next research question this opens.**  Is the linear-in-`ρ` defect sharp for this
architecture, or do the fresh primes cancel?  An instrument: compare `|W_h − W_{y,h}|` with its
triangle bound numerically on residue-class sets.  A large gap would locate the cancellation G₄
needs in a controlled family, before attempting it at `ρ = log 2`.
