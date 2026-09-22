# OBSTRUCTION 2026-09-22 — Lane B invention round: G₄ window cancellation

Ren / Fable 5.1, attended, 2026-09-22 (token expiry 2026-09-23 05:00 EDT).  Brief: `papers/FABLE-NEXT-SESSION.md` §Lane B.
Inputs read: `G4PrefixDecayAudit.lean`, `G4WindowK.lean`, `LITERATURE-2026-09-20-prefixdecay-sweep.md`,
`DESIGN-2026-09-19-bcr-wiring.md`, `HANDOFF-2026-09-20-rough-independence.md`, `PROBE-2026-09-20-smooth-rough-decoupling.md`,
`HANDOFF-2026-09-21-summatory-split.md`, `papers/kmt-2023-prop43-k-dependence.md`, KB verdict 2026-09-19.
Probe: `probes/rotation_and_resonance.py` (probe 14; `--selftest` asserts hand-computed values), data
`probes/data-2026-09-22-rotation-and-resonance.txt`.  Adversarial review: §6.

**BLUF.**  No new cancellation mechanism was found, and I now believe none is available from the geometric
coefficients: they act only on the *tail* sites, which are provably deterministic (§2), and leave the leading two
sites as a fully general two-point Elliott instance at natural density on all scales (§3).  The one surviving
candidate (§2) is a reduction that halves the site schedule and corrects probe 13's reading; it is not
cancellation.  The h-resonance arithmetic of the brief is verified (§1).  Nothing here changes the status of
`EventualPrefixDecay`: still open, still 🔴, with the class of the obstruction now written down (§3–§4).  ⚠️ Tier:
§1, §2, §3b, §3c are proved (paper) and probe-checked; **§3a–§3d and §4 are a difficulty *diagnosis*, not a Maze-row
refutation** (referee, §6).  Calibration test for any future candidate: `h = 2`, `k = 2` (§6-ii) — a *calibration*, not a logical
gate (Astra 17:44Z: `EventualPrefixDecay` starts at `k₀`, `WindowDecayK` speaks only at scheduled `k`).

Notation.  `T_k(m) = Σ_{j=1}^{k} ω(m+j)/4^j` (= `truncTail k m`), `F_{h,k}(m) = e(h T_k(m)) = ∏_{j≤k} z_j^{ω(m+j)}`,
`z_j = e(h/4^j)`, `S(h,k,M) = Σ_{m<M} F_{h,k}(m)` (= `fullPrefixSum h k M`), `windowK M = ⌊log₂⌊log₂⌊log₂ M⌋⌋⌋ + 1`,
so `4^{windowK M} > (log₂log₂ M)²`.

## 1. Verified arithmetic (independent of the brief)

**1a. Exact shift identity.**  `4 T_k(m) − T_{k−1}(m+1) = ω(m+1)` for every `k ≥ 1`, `m` — from
`4 T_k(m) = ω(m+1) + Σ_{j=2}^{k} ω(m+j)/4^{j−1}` and reindexing `j ↦ j−1`.  Asserted numerically in the probe
selftest (`k = 5`, `m < 200`).  Consequences, all exact:

- **Frequency lifting.**  `F_{4h,k+1}(m) = F_{h,k}(m+1)`, hence `S(4h, k+1, M) = S(h, k, M+1) − F_{h,k}(0)`.
  So `EventualPrefixDecay (4h) ⟺ EventualPrefixDecay h` (window index shifted by one; `k₀` shifts by one).
  Every frequency reduces to one with `4 ∤ h`, whose leading site is `z_1 ∈ {i, −1, −i}`.
- **Trivial windows.**  For `h = 4^a h'` with `4 ∤ h'` and `k ≤ a`, every phase is `1` and `S(h,k,M) = M`.
  The audit's `prefixDecay_four_false` is the case `a = 1`; **`PrefixDecay h` is false for every `h ∈ 4ℤ∖{0}`**, and
  `EventualPrefixDecay h` needs `k₀ ≥ a + 1`.  (Selftest: `a ∈ {1,2}`, `h' = 3`.)

**1b. Product resonance** (the brief's diagnostic).  `∏_{j≤k} z_j = e(h(1 − 4^{−k})/3)`.  If `3 ∣ h` this is
`e(−h 4^{−k}/3) → 1`, with `|∏ z_j − 1|² = 4 sin²(π h/(3·4^k))` and
`𝔻(∏_j f_j, 1; M)² = ½ |∏ z_j − 1|² Σ_{p≤M} 1/p`.  At `k = windowK M` (Mertens `Σ 1/p ≈ log log M + 0.2615`):

| h | M | windowK | `\|∏ z_j − 1\|²` | `𝔻²` |
|---|---|---|---|---|
| 3 | 10⁸ | 3 | 0.00963 | 0.0153 |
| 3 | 10¹⁰⁰ | 4 | 0.000602 | 0.00172 |
| 12 | 10⁸ | 3 | 0.152 | 0.242 |
| 12 | 10¹⁰⁰ | 4 | 0.00963 | 0.0275 |
| 1 | 10¹⁰⁰ | 4 | 2.99 | 8.51 (→ ∞ like `(3/2) log log M`) |

So for `3 ∣ h` the pointwise product `∏_j f_j` is pretentious to `1` with distance `→ 0` along the schedule
(`16^k ≥ (log₂log₂ M)^4 ≫ log log M`), for `3 ∤ h` it is non-pretentious with `𝔻² ~ (1 − cos(2πh/3)) log log M`.
Confirms the brief: any argument keyed to the non-pretentiousness of the *product* (Tao–Teräväinen odd-order style)
fails at `h ∈ 3ℤ`, and cannot be made uniform.  This is a diagnostic, not an obstruction to the shifted correlation.

## 2. Candidate A — tail-site determinism (SURVIVES numerically; a reduction, not a cancellation)

**Lemma A (paper; Lean shape in 2c).**  Let `μ_M := (1/M) Σ_{m<M} ω(m+1)`.  For `K ≤ J`,

    S(h, J, M) = e( h μ_M Σ_{K<j≤J} 4^{−j} ) · S(h, K, M) + E,
    |E| ≤ 2π|h| Σ_{K<j≤J} 4^{−j} Σ_{m<M} |ω(m+j) − μ_M|  ≤  C |h| M √(log log M) / 4^K.

*Proof.*  `F_{h,J} = F_{h,K} · ∏_{K<j≤J} e(h ω(m+j)/4^j)`; write `ω(m+j) = μ_M + (ω(m+j) − μ_M)`; the constant part
factors out as the rotation; `|e(x) − e(y)| ≤ 2π|x − y|` and `|F_{h,K}| = 1` give the first bound.  The second is
Turán–Kubilius at shift `j`: `Σ_{m<M} (ω(m+j) − log log M)² ≪ M log log M` uniformly for `j ≤ M` (the standard proof
counts `#{m<M : p ∣ m+j}` and `#{m<M : pq ∣ m+j}` by CRT with `O(1)` errors, which is shift-invariant), then
Cauchy–Schwarz and `|μ_M − log log M| = O(1)`.  ∎

**What it buys.**  Only the modulus `|S|` is cut-invariant; the mean rotates by a deterministic unimodular factor.
The window can be cut at `4^K ≍ A|h|√(log log M)`, i.e. **`K ≈ ½ log₄ log log M + O_h(1)`**, at cost `M/A`.  The
repo's `windowK` cuts at `4^K > (log₂log₂ M)²`; `window_tail_tendsto_zero` uses the crude first moment
(`ω ≥ 0`, tail `≍ log log M / 4^K`).  Lemma A replaces the first moment by the centered second moment, so the
exponent drops by a factor 4.  Sites with `16^j ≫ h² log log M` carry **no randomness**: their phase is
`e(h μ_M/4^j)` up to `L¹`-error `≪ |h|√(log log M)/4^j`.  In pretentious language: `𝔻(f_j, 1; M)² ≈ 2π²h² log log M/16^j`,
so these sites are pretentious to `1` with vanishing distance, and Turán–Kubilius is exactly what turns
"small distance" into "pointwise constant in `L¹`".

**Probe 13 corrected.**  Probe 13 read `|W_K − W_J| ≍ 4^{−K}` as "fixed `K` fails".  Probe 14 (same `N`, `J`, `h`)
shows the gap is the rotation: at `N = 2²⁴`, `h = 1`, `K = 2`: `|W_K − W_J| = 0.097`, `|r_K W_K − W_J| = 0.0016`,
`||W_K| − |W_J|| = 0.0007`; at `K = 3`: `0.023 / 0.0009 / 0.0009`.  Same pattern at `h = 3, 5, 12` from `K = 3`
(`h = 12`: `0.035 / 0.008 / 0.0075`).  The centered `L¹` bound `cbd` of Lemma A is honest but crude (factor
10–25 above the rotated error).  Fixed `K` still fails asymptotically — the error is `√(log log N)/4^K`, not
`4^{−K}` — but the *reason* is the growth of `√log log N`, not a loss of modulus.

**Resonant checks.**  `h = 4`: `|W_1| = 1` (trivial window) and the `K = 2` row equals the `h = 1`, `K = 1` row
(frequency lifting, §1a) — `0.0375` vs `0.0375` at `N = 2²⁴`.  `h = 12`: `K = 1` trivial, `K = 2` carries the whole
`z_2 = −i` site, rotation useless there (as it must be: site 2 is non-pretentious); from `K = 3` the rotation works.
`h = 3`: fine from `K = 2`.  No failure at resonant frequencies; the lemma's only content at a resonant site is `0`.

**Does A change the difficulty class?  No.**  `K(M) → ∞` still, and the sites it keeps (`4^j ≲ |h|√(log log M)`)
are exactly the non-pretentious ones.  A is a cleaner interface (`EventualPrefixDecay` with a half-log schedule and
a rotation), i.e. "another conditional diagram", and by the brief that alone is not the deliverable.  It is
recorded because (i) it corrects a written reading of probe 13, (ii) it is the sharp statement of *which* sites are
random, which §3 needs, (iii) it is a bounded, classical, formalizable lemma if a later lap wants the half-log
schedule.

**2c. Lean shape (not built this round).**  Frozen input `TuranKubiliusShift : ∃ C, ∀ M j, j ≤ M →
Σ_{m<M} (omegaR (m+j+1) − loglog M)² ≤ C · M · loglog M` (or with the window mean); theorem
`norm_fullPrefixSum_sub_rot_le` with the explicit bound above; corollary: `EventualPrefixDecay h` may be weakened to
`k ≤ windowK' M := ⌈½ log₄ (h² log log M)⌉ + A(M)` with **any `A(M) → ∞`** (e.g. `⌈log₄ log log log M⌉`).
⚠️ A fixed `A` gives error `O(1/A)`, not `o(1)` — Astra's correction, 2026-09-22 17:44Z; the two-limit form
(`A → ∞` after `M → ∞`) is what the `∀ ε, ∀ᶠ M` quantifier structure of `EventualPrefixDecay` delivers for free.  Cost: TK second moment is the only real work (needs
`Σ_{p≤x} 1/p ≤ log log x + O(1)` and the two-prime CRT count; the repo has the one-prime first moment
`sum_omegaR_add_le`).  One to two Opus/low laps.  **Not fired**: a schedule change with no new node is a rung, not
a lap objective, per the brief.

## 3. Candidate B — the obstruction: the leading sites are a general binary problem

After §1a and §2, `EventualPrefixDecay h` (`4 ∤ h`) is, up to `o(1)`, the decay of a `K(M)`-site correlation whose
first two sites are `z_1^{ω}` with `z_1 ∈ {i, −1, −i}` and `z_2^{ω}` with `z_2 = e(h/16)`, `|z_2 − 1| ≥ 2 sin(π/16) = 0.39`.
Both are non-pretentious to every `χ(n) n^{it}` (`𝔻² ≍ (1 − Re z) log log M`).  The `k = 2` sub-case
`Σ_{m<M} z_1^{ω(m+1)} z_2^{ω(m+2)} = o(M)` **along all `M`** is therefore necessary in spirit (not formally: the
sweep's item 2 stands — the `K`-site and `2`-site statements are not comparable) for any route through the window law.

**3a. What every decomposition returns.**  Fix `y = M^ε`.  Exactly, `F_{h,k} = Φ_y · R_y` with `Φ_y(m) =
e(h Σ_j ω_{≤y}(m+j)/4^j)` (the smooth phase; `E Φ_y ≍ (log y)^{Re Σ_j (z_j − 1)} → 0`) and `R_y = ∏_j z_j^{v_j(m)}`,
`v_j(m) = ω_{>y}(m+j) ∈ {0, …, ⌊1/ε⌋}`.  `R_y` is a *character of the rough-count vector*; the geometric coefficients
enter **only** through which character (`z_j^{v_j}`).  Decompose by the fibre `(v_1, v_2)`:

- `(0, 0)`: `m+1, m+2` both `y`-smooth — consecutive smooth numbers, mass `≍ ρ(1/ε)² M`, harmless only because small.
- `(1, 0)`: `m+1 = p a`, `p > y`, `a` and `m+2 = pa+1` smooth.  Mass `≍ M`.  The bulk has `a ~ M^α`; for `α < ½`
  it is `Σ_{p ~ M^{1−α}} Ψ(M, y; p, 1)` — smooth numbers in progressions to moduli **beyond** `M^{1/2}`, on average
  (friable Bombieri–Vinogradov beyond level ½: Drappeau-type results reach `3/5` with well-factorable weights, not
  `1 − ε`).  The phase on the fibre is `z_1^{ω(a)} z_2^{ω(pa+1)}`.
- `(1, 1)`: `m+1 = p a`, `m+2 = q b`, i.e. **`p a + 1 = q b`**, `p, q > y` prime, `a, b` smooth, weighted by
  `z_1^{ω(a)} z_2^{ω(b)}`.  When `pq > M^{1−δ}` (positive proportion of the fibre — this is the "late-band
  regeneration" the KB measured), the count over `(p, q)` for fixed `(a, b)` is a binary prime-pair problem, and the
  sum over `(a, b)` is a Titchmarsh/BFI-type dispersion problem at level of distribution up to `1 − ε`.  The weight
  `z_1^{ω(a)} z_2^{ω(b)}` on the solutions of `p a + 1 = q b` is *the same two-point correlation of two non-pretentious
  multiplicative functions along a pair of linear forms* we started with — the substitution `m+1 = pa` changes the
  linear forms, not the class.

Every "sieve the large primes" route (KMT §4, fibre decomposition, one-large-prime Buchstab, hyperbola in
`z^ω = 1 ∗ μ²(z−1)^ω`) lands here.  The coefficient structure is inert at this point: it fixes `z_1, z_2` but the
argument would have to work for *arbitrary* unimodular `z_1 ≠ 1 ≠ z_2` on the fibre.

**3b. Why one-site information cannot suffice (rigorous, classical).**  `g_1(n) = n^{it}`, `g_2(n) = n^{−it}` have
`𝔻(g_j, 1; y, x)² = Σ_{y<p≤x} (1 − cos(t log p))/p = log(log x/log y) + O(1)`, the same profile as `i^{ω}`, yet
`Σ_{n≤x} g_1(n+1) g_2(n+2) = x + o(x)`.  Hence no bound of KMT-Prop-4.3 shape (a function of the truncated distances to
`1` plus sieve errors) can give `k = 2` for `G₄`; this is why "one-site Halász does not control the shifted product".
The sweep already records that KMT 4.3 gives nothing for `G₄` because `𝔻(f_1, 1; x^ε, x)² = log(1/ε)` is *large*; §3b
says the failure is structural, not a matter of constants.

**3c. The Chowla sector is Chowla.**  `(−1)^{ω} = λ ∗ g` with `g` supported on squarefull numbers,
`g(p) = 0`, `g(p^a) = −2` (`a ≥ 2`), `Σ_d |g(d)|/d < ∞`.  So for `h = 2` the `k = 2` sub-case is
`Σ_d g(d) Σ_{m'} λ(m') z_2^{ω(d m' + 1)}` with `z_2 = e(1/8)`: a two-point correlation of Liouville with a
non-pretentious multiplicative function along `(m', d m' + 1)`, natural density, all scales.  Tao 2015 gives this with
logarithmic averaging; Tao–Teräväinen 2512.01739 at natural density outside an exceptional set of scales; all scales is
open.  And **logarithmic or almost-all-scale results cannot be upgraded for normality**: the prefix mean
`(1/M) Σ_{m<M}` is dominated by its top dyadic block, so a single exceptional scale `N ∈ (M/2, M]` with
`|fullWindowMean N| ≥ c` forces `|S(h,k,M)| ≥ cM/2 − o(M)`; the Weyl criterion needs every `M`.

**3d. Where the specific structure genuinely helps, and where it stops.**  Helps: (i) tail sites are deterministic
(§2), so growing `k` reduces to `K ≈ ½ log₄ log log M`; (ii) with `y = M^ε` fixed, the rough phases of sites `j` with
`4^j ≫ 1/ε²` are Lipschitz-trivial (`≤ 2π|h|/(ε 4^j)` each), so the *rough* part of the problem has a **bounded**
number of sites `j ≤ log₄(1/ε²)` — growing-`k` becomes bounded-`k` with `y`-smooth weights on the remaining sites.
Stops: the bounded number is `≥ 2` for every `ε < 1/4`, and those sites are the fully non-pretentious ones.  There is
no `ε`-range in which the rough part is one-site.

## 4. Ideas tried and killed this round (negative inventory for the next session)

| idea | why it dies |
|---|---|
| Expand sites `j ≥ 2` as `z^ω = 1 ∗ μ²(z−1)^ω`, reduce to `z_1^ω` in progressions | the absolute sum `Σ_{d>x^{1−δ}} \|z−1\|^{ω(d)}/d ≍ δ(log x)^{\|z−1\|}` diverges while the complex sum converges; the large-modulus tail needs complex cancellation in `d`, and `z_1^ω` in progressions to moduli `> x^{1/2}` has none available.  Hyperbola cut at `Y = exp(√log x)` moves the divergence to the other side (progressions with `Y` terms). |
| KMT Prop 4.3 with sites `j ≥ 2` truncated to `x^ε`-smooth | truncation of site `j` costs `𝔻(f_j,1;x^ε,x) ≈ 2π\|h\|4^{−j}√log(1/ε)`; summed over `j ≥ 2` this is `≈ (π\|h\|/6)√log(1/ε)`, bounded but not small, and site 1 costs `√log(1/ε)` outright (§3b). |
| Drop the rough phases at sites `j ≥ 2` | `Σ_{j≥2} v_j/4^j` has mean `(log(1/ε))/12` and std `≈ 0.26√log(1/ε)`: phase spread `≈ 1.6√log(1/ε)` radians, not small. |
| Joint Erdős–Kac at shifts (Kubilius model + moments) | gives the joint law at scale `√log log`, i.e. sites with `4^j ≍ √log log M` — already the frozen/CLT boundary of §2; says nothing about `ω(m+1) mod 4`. |
| Product non-pretentiousness (TT odd-order style) | fails at `h ∈ 3ℤ` (§1b) and needs logarithmic averaging anyway. |
| Gowers-norm / linear-forms machinery | all forms `m + j` share a linear part: degenerate pattern (sweep, item 1). |
| Fundamental lemma with the complex weights `Φ_y` at bounded `u = 1/ε` | the nonnegative majorant has dimension `H = Σ_j \|z_j − 1\| ≈ 2.1\|h\|` and main term `(log y)^{+H}` against a true main term `(log y)^{−1.1}`: relative error `e^{−u}(log y)^{H+1.1}` forces `u ≫ log log y`, at which point `ω_{>y} ≍ log log M` and the Lipschitz saving of 3d(ii) is gone. |
| Bilinear over `(p, a)` in `m+1 = pa` | for `a ≥ M^{1/2+δ}` it is `z_2^ω` on shifted primes `ap+1` (Selberg–Delange on shifted primes, plausible) but the other sites' rough parts return `q ∣ ap+2`, i.e. the `(1,1)` fibre of §3a. |
| Self-similarity `ω_{>2}(2n) = ω_{>2}(n)` (halving is exact) | relates scale `M` to `M/2` for the *parity class*, not for the window at shifted sites; gives the 2-adic assembly already in `G4SummatorySplit.lean`, no scale-to-scale transfer of the crux. |

## 5. Next unresolved inference (exact)

The smallest open statement on the route: for `z_1 ∈ {i, −1}` and `z_2 = e(1/16)` (or `e(1/8)`),

    (1/N) Σ_{N ≤ m < 2N} z_1^{ω(m+1)} z_2^{ω(m+2)} → 0   as N → ∞ through ALL N.

Known: `o(1)` along a set of `N` of full upper logarithmic density (KMT 2304.05344, as recorded in the sweep; TT
2512.01739 with a power-of-`𝓛` saving outside an exceptional set of scales).  Unknown: every `N`.  A proof of this for these two specific
functions would be new mathematics and would not yet give `G₄` (`K(M) → ∞` remains), but it is the gate.  A proof
that it is *equivalent* to a named conjecture (two-point Elliott at natural density for a pair with `𝔻² ≍ log log`)
would be the honest closing of the route.

## 6. Adversarial review (fresh Opus, negative inventory first) — verdicts

Referee read the audit, `G4WindowK.lean`, the sweep, the summatory-split handoff, probe 13 data and the brief before
the candidates.  Condensed:

- **A: SURVIVES WITH CORRECTION, consequence cosmetic.**  Identity and bound correct; no circularity (triangle
  inequality + TK only).  Corrections accepted: (1) the centering constant is immaterial (`μ` enters only through a
  phase of size `|h|μ 4^{−K}`; the window mean is the self-calibrating choice); (2) TK uniformity in the shift is a
  non-issue (`windowK M ≤ 5` for every `M < 10^{10^{10}}`; a shift by `j` perturbs the TK sum by `O(j log M)`);
  (3) resonance is absorbed by `|h|`, so the threshold `4^K ≍ A|h|√log log M` is **not uniform in `h`** — harmless
  for Weyl (one `h` at a time), fatal if a future step needs a range of `h`.  Strongest objection: the repo already
  has `‖W_J − W_K‖ ≪ |h| (log log M) 4^{−K}` (`norm_fullWindowMean_sub_le` + `geom_tail_le` + `sum_window_omegaR_le`,
  the `L1bd` column of probe 13); A replaces `log log M` by `√log log M`, i.e. `K ≈ windowK/4`, same growth class,
  never the fixed-`k` Ingham–Estermann regime.  Two cautions to carry: the probe validates the *reduction*, not the
  *rate* (observed modulus gaps sit 2–3 orders below A's bound); and **A escapes the "pointwise truncation refuted"
  verdict of `HANDOFF-2026-09-21-summatory-split.md` only because `PrefixDecay`'s budget is `εM` — against the SD
  node's own budget `M (log M)^{Re κ}` A is still over by `log log M`.**
- **B: SURVIVES as a heuristic diagnosis, NOT as a verdict; no counterexample found.**  Closest natural-density
  all-scale results are one-non-pretentious-factor: Topacoğullari 1506.02608 (`τ_z(n) τ(n−h)`), Lau 2509.07556
  (`d_k(n) d(n+h)`) — the second factor is `τ`, pretentious.  Klurman 1603.08453, KMT 2304.05344, Elliott–Kish
  1405.7132: pretentious hypotheses or full-upper-log-density scale sets.  Overreach flagged: "every decomposition
  returns `pa+1 = qb`" quantifies over *methods* and is not provable; the fibre argument uses the smooth/rough
  factorisation the repo froze as `SmoothRoughDecoupling` (mildly circular as an obstruction); `(1,1)` is one fibre
  of a Poisson(`log 1/ε`) family.  **File as diagnosis, not as a Maze-row refutation** — done (see BLUF).
- **Best attack on `k = 2`, and where it fails:** hyperbola/dispersion with `z^ω = 1 ∗ μ²(z−1)^ω` at the *second*
  site needs `z_1^ω` in progressions on average over `d` with weights `|z_2 − 1|^{ω(d)}` — fine when `|z − 1| < 1`,
  but at the leading site `|i − 1| = √2 > 1` the demand becomes a dimension-`√2` BV beyond `x^{1/2}`, which
  Granville–Shao/Drappeau-type BV for 1-bounded multiplicative functions does not deliver.  Type II: none (same
  linear part).  Joint CLT: precision `o(1)`, not `(log)^{−c}`, and its error terms *are* the correlation.
- **Resonance arithmetic**: independently recomputed, agrees to all printed digits (`𝔻² = 0.01529, 0.001717, 0.24168,
  0.02745`).  Caveat added by the referee: Tao-type two-point theorems need only *one* non-pretentious factor, which
  site 1 supplies, so the product diagnostic is weak — **the blocker is the averaging mode, not pretentiousness.**
- **Trivial-frequency identities**: correct; `k₀(4^a h') = a + k₀(h')`; "`4 ∤ h` WLOG" now cited from §1a.
- **Missed**: (i) the slack — conjecturally `|S| ≪ M/log M` (from `exists_re_sdExponent_le_neg_one`) while the node
  asks only `εM`, so a method losing `(log M)^{0.99}` would do; neither candidate looks there.  (ii) Calibration
  gate: for `h ≡ 2 (mod 4)`, `z_1 = −1` exactly — **test every candidate on `h = 2`, `k = 2` first**,
  `Σ (−1)^{ω(n+1)} e(1/8)^{ω(n+2)} = o(M)` on all scales; if it cannot do that, it cannot do `PrefixDecay`.

## 7. Response to the review, and the closing verdict

**On the slack (6-i).**  The slack does not help, and the reason is the same as the obstruction.  The only
large-loss tool that works at natural density on *all* scales is one-site Halász (no shifts).  Every multi-site
argument (Matomäki–Radziwiłł–Tao, Tao's entropy decrement, TT 2512.01739) starts with the substitution `m+1 = pa`,
`p ∈ (P, Q]`, which is legal at natural density with a Turán–Kubilius loss `M/√H`, `H = Σ_{p∈(P,Q]} 1/p` (so `Q = P^{A}`
with `A = e^{1/ε²}`, fine).  After it, the sum is `Σ_p Σ_{a ≤ M/p} f_1(a) f_1(p) f_2(pa+1) …`, i.e. a family of sums at
the **different scales `M/p`**, and Cauchy–Schwarz in `a` controls only their *average over `p`*.  That is exactly why
these methods output "almost all scales" (or, with `1/m` weights that make `m ↦ pm` measure-preserving,
logarithmic averages).  A large loss buys nothing here: the defect is that a single bad sub-scale `M/p` is invisible
to the average, and normality needs every scale (§3c).  So the slack is real and unusable by any method that passes
through the `p`-substitution, which is every known multi-site method.  (Confidence 80% that no known method avoids
the substitution.)

**On A vs the SD budget (6-A).**  Recorded verbatim above.  A is filed as a rung for the `εM`-budget node only.

**On B's tier (6-B).**  Accepted: §3 is a *diagnosis* of the difficulty class, and its fibre exhibit assumes the
smooth/rough split.  It is not a Maze row and must not be written as one.  What *is* rigorous in §3: §3b (the
`n^{±it}` pair) and §3c (the `λ ∗ g` identity and the dyadic-block argument that exceptional scales break normality).

**Closing verdict for Lane B (this round).**  No new cancellation mechanism; the geometric coefficients act only on
sites that are provably deterministic (A) and on the character of the rough vector, never on the averaging mode.
The gate for any future candidate is `h = 2`, `k = 2` at natural density on every scale.  `EventualPrefixDecay`
stays 🔴.  No Opus lap fired: A is a rung (schedule/rotation) with a classical input, not a node; the brief says a
cleaner conditional wrapper alone is not the deliverable.  If a later session wants the half-log schedule, §2c is the
kickoff.
