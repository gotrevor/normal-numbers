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

## The instrument: do the fresh primes cancel?  (measured 2026-09-30)

`experiments/cprime_fresh_cancellation.py` (tests: `test_cprime_fresh_cancellation.py`, 8 checks,
hand-derived).  Data: `probes/data-2026-09-30-cprime-fresh-cancellation.md` (T1/T2, h = 1, 3) and
`…-h135.md` (h = 1, 3, 5, N = 2^20..2^24).

**Setup.**
- Prime sets: residue classes `1 mod q` (q = 3 … 61) and `2 mod 31`, deterministically thinned
  primes (θ = 1/2 … 1/32), and all primes.
- `J = 5` sites; cutoffs `y_j = N^(2^−j)`.  The paper's `a = u⁻²` is numerically degenerate at
  reachable `N`, so these are not the proof's cutoffs.
- Exact split: `W − W_y = T1 + T2`.  T1 keeps the `n` whose fresh primes sit at one site.  T2 keeps
  the `n` with fresh primes at two or more sites, i.e. a prime pair `p | n+j`, `p′ | n+j′`.

**Findings.**
1. **No first-order cancellation.**  At small `ρ`:
   - `A = |W − W_y| ≈ M`, the pointwise L¹ mass: `A/M ≈ 0.85–0.95` at `h = 1`.
   - `A ≈ 2ρ` at `h = 1`, flat from `2^20` to `2^24`.
   - The triangle bound is sharp up to a constant at reachable scales.
2. **It tracks the frozen mean.**  Where `|W_y|` visibly moves (`1 mod 3`, thinned 1/2 and 1/4),
   `A/|W_y|` is stable across `N`: 0.955 → 0.974 → 0.984 for `1 mod 3` at `h = 1`.  This is the
   multiplicative, size-budget picture of the 2026-09-19 fable verdict: `T1 ≈ W_y·G_h(ρ)`.  Fresh
   primes rescale the frozen mean rather than adding independent error.  For sparse sets
   `|W_y| ≈ 1` at these `N`, so the relative form is **untested** there.
3. **The multi-site term is second order.**  `|T2|/ρ² ∈ [0.2, 4.6]` for every set, `ρ` from 0.69
   down to 0.012, stable from `2^22` to `2^24`.  Typical values are ≈ 1.5 at `h = 1` and ≈ 3.5 at
   `h = 3`.  Example: `1 mod 61`, `ρ = 0.012`, `T2 = 2.7·10⁻⁴`.

**What this suggests: the wall sits at second order in the fresh mass.**  Here is the difficulty
check.
- **Proved:** the `O(ρ log³)` bound above.
- **Unproved premise `RelativeFirstOrder`:** `T1 = W_y·G_h + o(1)`, with `G_h` bounded and
  `N`-independent.  Since `W_y → 0` under model contraction, T1 would drop out.  What remains is
  `|T2| ≤ C(Σ_j S_P(y_j, N))²` from an **upper-bound** sieve on prime pairs, which needs no parity
  input.  The discrepancy would improve to `O(ρ² polylog)`.
- **Candidate mechanism for the premise:**
  - Order the fresh primes by size, as in peeling identity (10)–(13).
  - For `p ≤ N^(1/2−ε)`, condition on `p | n+j` inside the frozen CRT sieve: one extra
    congruence, error `R²p/N`, summable.
  - For `p > √N`, the cofactor is `k < N/p`.  Swap the sums, and the other sites' frozen phases at
    `pk + c` need primes in progressions to moduli `≤ R² ≤ N^(1/4)` on average: a
    Bombieri–Vinogradov level, which the build lacks.
  - The pivot factor `Σ_{k≤N/p} z^(ω_frozen(k))` is the deterministic size budget.
- **Where it stops:** T2's *relative* form would need prime-pair correlations, which is
  parity-barrier territory.  So the argument stops at `ρ²` on purpose.
- **Sibling check:** at all primes (`ρ = log 2`, `C ≈ 1.5`) the `ρ²` bound is trivial, so the
  premise does not accidentally claim G₄.
- **Maze check:** the premise is not the refuted per-prime "regeneration as feedback" or the
  restatement-only signed peeling sum (7).  It asks for the size-budget factor `G_h` to be
  *deterministic*, and uses `ρ` as the expansion parameter.
- **Confidence:** about 70% that `T2 = O(ρ²)` persists in the proof's cutoff regime; about 40%
  that `RelativeFirstOrder` is provable by the mechanism above.

**The next research question.**  Answered in part by the measurement above.  The fresh primes do
not cancel at first order; they rescale.  The open question is now `RelativeFirstOrder`.  Its
first concrete test: track `T1/W_y` at a moderate fixed `a < 1`, on dense residue classes where
`W_y` decays visibly.

## `RelativeFirstOrder`, measured  (2026-10-01)

Data: `probes/data-2026-10-01-cprime-relative-first-order.md`.  The probe now reports
`G = T1/W_y`, the independent-sites value `Sbar` (the mean of `Σ_j (z_j^fresh_j − 1)`), and the
coupling `C = T1 − W_y·Sbar`.  The hand-derived test is the one-prime case `P = {101}`, where
`G = Sbar/(1 + c(z_1 − 1))` exactly.

**Verdict: the premise survives its direct test at reachable N.**  At fixed `a`, `G` holds within
about 3% across `N = 2^20 → 2^24` for every set with `ρ ≤ 0.35`.  The phase holds within about 1°.

- **T1 follows W_y down.**  The clearest case is `h = 2`, `a = 1`.  For `1 mod 3`, `|W_y|` falls
  0.262 → 0.234 → 0.212 (−19%), `|T1|` falls 0.370 → 0.331 → 0.301 (−19%), and
  `|G| = 1.413, 1.420, 1.423`.  `thin 0.25` is the same: `W_y` −9%, `G` 0.707 → 0.727.  Even all
  primes at `h = 2` behave this way: `W_y` −38%, `T1` −36%.
- **The fresh part is coupled to the frozen product, and the coupling holds steady in N.**  At
  `a = 1`, `|C|/|T1|` is 0.13 (`1 mod 5`), 0.25 (`1 mod 3`) and 0.29 (`thin 0.5`), with drift of
  0.01 or less.  It shrinks as `a` decreases: 0.03–0.06 at `a = 0.5` and h = 1.  So `G ≠ Sbar`.
  The size budget enters as a deterministic multiplicative factor, not as noise, which is the form
  the premise asks for.  `|G|/|Sbar|` sits at 1.12 (`1 mod 5`), 1.28 (`1 mod 3`) and 1.36
  (`thin 0.5`) at h = 1 and drifts less than 1% per step.  Most of the drift that remains in `G`
  is `Sbar`'s own drift, which is the slow Mertens-in-progressions convergence of the fresh mass.
- **One exception, outside the small-ρ regime: all primes (ρ = 0.69) at a = 1, h = 1 and 3.**
  `|G|` falls 3.73 → 3.53 → 3.34, and its phase rotates 138° → 145°, while `|W_y|` stays flat at
  0.137.  `|G|/|Sbar|` falls 7% per step.  My guess was a critical exponent: the site-local
  size-budget factor `(1−t)^(δ(z−1))` stops being integrable once `δ(1 − cos 2πh/4) ≥ 1`.  The
  `h = 2` control **refutes** that guess.  It predicts `1 mod 3` and `thin 0.5` (δ = 1/2) are
  critical at h = 2, yet both are stable to 1%.  The cause of the all-primes drift is unknown.
  Quantitative C′ concerns small `ρ`, so this does not touch the premise as used.

**Limits.**
- Only `a ≥ 0.25` is measured, not the proof's `u⁻²`.
- `log N` moves only 20 → 24, so "steady in N" means steady over a 20% change in `log N`.  A
  `1/log N` drift cannot be ruled out, and `Sbar` itself shows one.
- At `a = 0.25` the sparse classes have `W_y = 1` exactly (no frozen primes), so those rows are
  uninformative.

**Next:** derive `G_h` as a site-local Dickman-type integral, in the conditional form
`E[z^ω_y (z^f − 1)] / E[z^ω_y]` per site.  Then compare it with the measured `G` and its N-drift.
An analytic `G` that matches is the statement the CRT/Bombieri–Vinogradov mechanism has to deliver.
Confidence: about 75% that `RelativeFirstOrder` holds in the small-ρ regime (up from about 60%
implicit); about 40% that the mechanism proves it (unchanged).

## Analytic `G_h`  (2026-10-01)

Data: `probes/data-2026-10-01-cprime-analytic-G.md`.  Probe modes: `--report sites | limit | frozen`.
Tests: 19, hand-derived.

**The formula.**  Write `w_k = z_k − 1` and `κ_k = δ·w_k`, where `δ` is the density of `P` among
the primes (`δ = 1/φ(q)` for a residue class, so `ρ = δ log 2`).  Let `u_k = 2^k/a`.  Then

    G_h = Σ_k g_k,   g_k = 1/R_{κ_k}(u_k) − 1,

where `R_κ` solves the delay equation

    R = 1 on [0, 1],   R'(t) = −(κ/t)·((t−1)/t)^κ·R(t−1).

On `[1, 2]` it has the closed form `R = 1 − κ Σ_n b^(κ+n+1)/(κ+n+1)`, with `b = 1 − 1/t`.
`F_κ(u) = A u^κ R_κ(u)`, with `A = e^(−γκ)/Γ(1+κ)`, is the generalized Dickman distribution
function: the law of `log d / log y` under the weights `w^ω(d)/d` on `y`-smooth `d`.  Its
normalization `F(∞) = 1` is checked numerically for real and complex `κ`.

Properties:
- `G_h` depends on `P` only through `δ`.  It is bounded and independent of N.
- To first order in `δ` it is the linear fresh mass `Σ_k δ w_k log u_k`.
- When `κ` is a negative integer (`z = −1` with `δ = 1/2` or 1), the site factor is exactly `−1`.
- As `u → ∞`, `g_k → u^κ e^(−γκ)/Γ(1+κ) − 1`.  That simpler form misses the frozen mean's own size
  budget, and is off by about 35% for all primes at `y = √N`.

**Derivation, two steps.**
1. **Site reduction.**  If the fresh factor at site `k`, conditioned on the frozen configuration,
   depends only on site `k`, then `T1/W_y = Σ_k [Mf_k/My_k − 1]`.  Here `Mf` and `My` are the means
   of `z^ω_P` and `z^ω_{P,≤y}` over a single integer.
2. **Single-integer asymptotics.**
   - `Mf` uses the Selberg–Delange main term `(log N)^κ H/Γ(1+κ)`.
   - `My` is the CRT product `Π_{p≤y}(1 + w/p)` times `F_κ(u)`.
   - In the ratio the Mertens products cancel down to the fresh tail `Π_{y<p≤N}(1 + w/p) → u^κ`.
     That leaves `1/R_κ(u)`.

**Measured, N = 2^20 → 2^26.**  The four levels are:
- `G`, measured;
- `G_A`, the site reduction with exact single-integer means;
- `G_SD`, finite-N analytic: the Selberg–Delange main term, the exact Mertens-in-progressions tail and `F`;
- `G_∞`, the limit.

Results:
- **Site reduction holds for residue classes.**  `|G − G_A|/|G|` is 0.5–3% whenever every prime of
  `P` exceeds `J`.
  - With a prime `≤ J` in `P` (2 in the thinned sets; 2, 3 and 5 in all primes), the product of
    site means breaks.  `Π My_k/W_y` reaches 0.0 or 2.7, and `G_A` blows up where `My_1 = 0`
    (`z = −1` at `p = 2`).
  - Measured `G` still matches `G_SD` in those cases, because the shared small primes cancel in
    `T1/W_y`.
  - So the correct statement of step 1 is a frozen-weighted conditional mean, not a product of
    site means.
- **Finite-N analytic level.**  `|G_A − G_SD|` is 2–12% for `δ ≤ 1/2` and shrinks with N.  For
  `1 mod 5`, h = 1, a = 1: 7.9 → 7.0 → 6.2 → 5.6%.  For `1 mod 3`: 11.8 → 8.5%.
- **The limit shows up at reachable N for residue classes.**  `|G − G_∞|/|G_∞|` decreases
  monotonically at every h and both values of a:
  - `1 mod 5`: from 12–20% at `2^20` to 5–10% at `2^26`;
  - `1 mod 3`: from 6–17% to 5–14%;
  - `1 mod 31`: from 45–58% to 29–47%.  Its first frozen prime is 311, so the small-`y` sites are
    far from asymptotic.
  - all primes, a = 1, h = 1: 61 → 51 → 44 → 37%.  This is the drift of 2026-10-01 morning, now
    explained as convergence to `G_∞`.
  - The golden-ratio thinned sets wander and don't converge cleanly.  They are deterministic
    pseudo-random sets, and their density is only a heuristic.
  - A two-point `1/log N` extrapolation is too unstable to quote: it overshoots `G_∞` by 3–30%.
- **The Dickman factor `F_κ` is needed, and confirmed only for real `κ`.**
  - Without it, the all-primes gap between `G_A` and `G_SD` sits flat at 35% (0.358, 0.350,
    0.349).  With it, the gap shrinks (0.56 → 0.33 at 2^26).
  - Direct check at `κ = 1`: the exact frozen mean over its CRT product approaches `F_1(2) = 0.906`
    at the `1/log N` rate (gap 4.1 → 3.2%).
  - Complex or negative `κ` at `u = 2` is **not confirmed**.
    - `1 mod 3` at h = 1 (κ = −½+½i): a 4.2 → 3.9% gap, barely moving.
    - `1 mod 5` at h = 2 (κ = −½): 0.45 → 0.74%, **growing**.
    - All primes at h = 1: 52% off.
  - For `δ ≤ 1/4` the factor is below 1% at every site, so the small-ρ regime does not depend on it.
  - `dickman_F` returns `inf` at the poles (κ = −1, −2).  The finite limit there (`e^γ/u` on
    `(1, 2]` for κ = −1) does not match the measured 1.05–1.07 either.  The pole cases are
    unresolved.

**What this does to the mechanism.**
- Step 2 is classical mean-value theory: Selberg–Delange, plus smooth-number weighted means for
  `F_κ`.  It enters as Literature Props.
- The new content is all in step 1 for the fresh primes above `y_k`.  For `n + k = p·m`, the
  frozen configuration at the other sites must equidistribute along `n = pm − k`, summed over `p`.
  That is a weighted Bombieri–Vinogradov statement.  At the proof's cutoffs the frozen moduli stay
  below `N^(1/8)`, inside BV's level ½.
- The crux of `RelativeFirstOrder` is therefore one weighted-BV conditional factorization, with an
  explicit constant `G_h` to land on.

**Confidence.**
- About 80% that `RelativeFirstOrder` holds for small ρ (up from 75%).
- About 45% that the mechanism proves it (up from 40%, because the crux is now one named step).
- Unresolved: `F_κ` for complex `κ` with `Re κ < 0` at `u = 2`, and the pole cases.
