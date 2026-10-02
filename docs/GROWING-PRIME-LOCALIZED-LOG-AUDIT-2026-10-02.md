# Growing-prime localized logarithm: paper audit (2026-10-02)

Audit of the claim in `~/personal/claude/knowledge/core/projects/normal-numbers-localized-log-growing-primes-2026-09-16.md` (the "overnight note"), with the repair asked for in `docs/REVIEW-2026-09-25-research-trajectory.md` item 7.  Mathematics only; no Lean was written or built in this pass (by instruction).  The Lean statements in section 6 are owed as declarations.

**Claim under audit.**  Let `Y : ℕ → ℕ` be nondecreasing, `Y(m) ≥ 3`, and `π(Y(n)) ≤ (1−ε) log₂ log n` for large `n`.  Put `ζ_Y = Σ_{m≥1, P⁺(m) ≤ Y(m)} 1/(m·2ᵐ)`.  Then `ζ_Y` is normal in base 2.

**Verdict: sound with repairs (75%).**  Two of the six skeleton steps are wrong as written, and both can be fixed.  Step 4 uses a `√N` segment cutoff, which by itself proves the claim only for `ε > 1/2`.  Step 5 sets `k = π(Y)+5`, which lies outside Vandehey's nontrivial range for every segment.  With the repairs below the claim holds for the stated range.  The method in fact reaches the wider range `π(Y(n)) ≤ log₂ log n − 2 log₂ log log n − log₂ log log log n − ω(1)` (70%).  Vandehey's Theorem 5.1 is uniform in `P` exactly as stated (85%).

Sources read this pass: Vandehey, *Differencing methods for Korobov-type exponential sums*, arXiv:1606.07911v1 (J. Anal. Math. 138 (2019)), all of sections 1-6 and 7.1, plus the start of 7.2.  Also `CaptainSude/xi-normality` @ HEAD (paper `paper/localized-logarithm-normality.tex` sections 2 and 5, the Lean tree, README, CREDITS).  Supporting checks are in `probes/growing_prime_localized_log_check.py`, which exits 0.  It recomputes Vandehey's exponent recursion against his printed constant `c` and Lemma 6.3 table, and it tests the arithmetic of steps 2-3 for a `Y` that jumps 3→5→7→11 at `n ≤ 4000`.

## 1. Vandehey Theorem 5.1: uniformity in `P` 📏

### 1.1 The statement, with every `P`-dependence named

For a finite set of primes `P = {p₁,…,p_s}` coprime to `b`, write `Q = ∏ pᵢ`, `M = M(P) = ∏ pᵢ^{β'ᵢ}` with `pᵢ^{β'ᵢ} ‖ b^{2·ord(b,Q)} − 1` (eq. 3), and `C_{P,x} = ∏ pᵢˣ/(pᵢˣ − 1)` (Lemma 4.2).  Theorem 5.1 says that for all `m ∈ ℕ_P`, `gcd(a,m) = 1`, `k ≥ 0` and `N ≥ 1`:

```
|Σ_{n=1}^N e(a bⁿ/m)| ≤ (A_k m^{α_k} N^{γ_k} + B_k m^{−α_k} N^{ν_k}) (1+log m)^{2^{−k}}
α_k = 1/(2^{k+2}−2),  γ_0 = 0, ν_0 = 1, A_0 = 1, B_0 = M,
γ_k = (1+γ+αν)/(2(1+α)),   ν_k = (1+ν)/2 + (1+γ−ν)α/(2(1+α))       [previous-index values]
A_k = (2^{s+2} Q (A_{k−1}+B_{k−1}) C_{P,α_{k−1}} + 2Q + 2 A_{k−1} M C_{P,1+α_{k−1}})^{1/2}
B_k = (2^{1+α_{k−1}} B_{k−1} M Q^{α_{k−1}} C_{P,1−α_{k−1}})^{1/2}
```

**Decision: Theorem 5.1 as stated is uniform in `P` (85%).**  It is a statement about every finite `P`, and the only `P`-dependent quantities are `s, Q, M, C_{P,·}`, which enter only through the explicit recursion for `A_k, B_k`.  No implied constant appears anywhere in Theorem 5.1.  The phrase "fixed, finite set of primes" in Lemmas 5.3-5.4 is wording only; both proofs are explicit inequalities valid for every `P`.  Checked line by line:

- **Base case** (`k = 0`) is Lemma 2.3: `|Σ| < (m^{1/2} + M m^{−1/2} N)(1+log m)`.  This comes from Korobov's complete-sum Lemma 2.2, which carries the explicit constant 1, together with eq. (5), `m/M ≤ ord(b,m)`.  It is uniform.
- **Induction step** is Proposition 4.1.  I re-derived `A'` and `B'` from the last display of its proof.  The coefficient of `m'N^ν` is `2^{s+1}BC_{P,δ}+1`, and `m' ≤ 2Q m^{α/(1+α)}N^{(1+γ−ν)/(1+α)}` (eq. 13).  So `A'² = 2^{s+2}QBC_{P,δ} + 2Q + 2AMC_{P,1+α} + 2^{s+2}AQC_{P,α}` and `B'² = 2^{1+δ}BMQ^δC_{P,1−δ}`, which matches the statement (90%).  Every auxiliary input is explicit: Lemma 4.2 (`C_{P,α}`), Lemma 4.3 (`φ_d(n,x) ≤ φ(n/d)x/n + 2^s`), Claims 4.4-4.6 (`m/m' | M`), and `τ/m̄ ≥ 1/M`.
- In Theorem 5.1 `δ_k = α_k` at every stage (`δ' = δ/(2(1+α))`, same as `α'`), which is why `(A+B)C_{P,α}` appears.  Proposition 4.1 also has `B' = max{…,1}`, which Theorem 5.1 drops.  This is harmless, since `B_k² ≥ 2B_{k−1} ≥ … ≥ 2M ≥ 1`.
- **The `O(·)` terms in eq. (20) are absolute and `P`-free (95%).**  `α_k, γ_k, ν_k` obey a recursion that does not involve `P` at all.  Lemma 5.2's proof gives `|ε'_k| ≤ 5` and `|ε'_k − c| ≤ (k+7)/2^{k−1}`, so the error is at most `(k+7)/4^k` for `ν_k−γ_k`.  Combined with eq. (15), `γ_k+ν_k = 2−2^{−k}`, this gives eq. (20) with implicit constant 1.  The probe recomputes the recursion exactly in rationals: eq. (15) holds for `k < 40`, `c` matches eq. (17) to about 10 digits, and every entry of the Lemma 6.3 tables matches the paper to the printed precision.
- **Lemma 5.4** (explicit, uniform): `A_k ≤ 6·2^{s(k+1)+7/2} Q^{3/2} M² C_{P,1/2} ∏(1−1/p)^{−1}` and `B_k ≤ 2^{3/2} M Q^{1/2} C_{P,1/2}`.  Remark 5.5 says the `2^{sk}` growth cannot be removed, because `A_k ≥ (A_{k−1}C_{P,α_{k−1}})^{1/2}` and `C_{P,α} ≈ ∏ 1/(α log p)`.
- **Lemma 6.3** (absolute): for `k ≥ 1` and `N = mˣ` with `x ∈ Ĩ_k = [1/(k+c+2), 1/(k+c+1)]`, `max(m^{α_k}N^{γ_k}, m^{−α_k}N^{ν_k}) ≤ N^{1−2^{−k−3}}`.  The intervals `Ĩ_k` for `k ≥ 1` tile `(0, 1/(c+2)] ≈ (0, 1.206]`.

**What is NOT uniform:** Theorem 1.1's `K₁, K₃` (eqs. 21, 23) and Corollaries 1.2/1.3 and Theorem 1.4, all of which use the crude bound `M ≤ b^{2Q}` (eq. 4) or hide constants depending on `P`.  Use Theorem 5.1 + Lemma 5.4 + Lemma 6.3 directly, never Theorem 1.1/1.4.

**One caveat on the literature input itself (not on uniformity).**  Vandehey says Korobov's Lemma 2.2 "is incorrectly stated in both locations cited", and repairs it to `d = 1` or `d < m/m₁`.  We only use `d = 1`.  It is a cited input, not re-proved here.

### 1.2 The honest `M(P)` for `b = 2`, `P` = odd primes `≤ Y`

Let `L_Y = ord(2, Q) = lcm_{p∈P} ord_p(2)`, and let `w_p = v_p(2^{ord_p 2} − 1)`, the "Wieferich excess".  It equals 1 except at Wieferich primes (1093, 3511 are the only known ones).  For odd `p`, lifting the exponent gives `β'_p = v_p(2^{2L_Y} − 1) = w_p + v_p(L_Y)`, because `ord_p 2 | p−1` is prime to `p`.  Also `v_p(L_Y) ≤ max_{q≤Y} v_p(q−1) ≤ log Y/log p`.  Hence

```
log M ≤ Σ_{p ≤ Y} w_p log p + π(Y) log Y.
```

- Generic (`w_p = 1` for all `p ≤ Y`, true for every `Y < 1093`): `log M ≤ θ(Y) + π(Y) log Y ≈ 2Y`.  This confirms the note's "≈ 2Y" (90%).
- Unconditional: `p^{w_p} ≤ 2^{ord_p 2} − 1 < 2^{p−1}`, so `log M ≤ (log 2) Σ_{p≤Y}(p−1) + π(Y) log Y = ((log 2)/2 + o(1)) Y²/log Y` (90%).

**Correction to the note's derivation.**  The note writes `β'_p ≤ 1 + v_p(2·lcm ord) ≤ 2 + Y/log p`.  The "1" should be `w_p`, which is unbounded unconditionally, and `Y/log p` should be `log Y/log p`.  The final bound `log M ≲ Y²/log Y` survives, with constant `(log 2)/2` in place of 1.  The crude eq. (4) would give `log M ≤ 2 log 2 · e^{θ(Y)}`.  At `Y ≍ log log n · log log log n` that is `(log n)^{ω(1)}`, which is fatal, so the honest `M` is required, as the note said.

Other `P`-quantities at `s = π(Y)−1` odd primes: `log Q = θ(Y) − log 2 ~ Y`; `log C_{P,1/2} = O(√Y/log Y)`; `log C_{P,1} = log log Y + O(1)`; `log C_{P,α_k} ≤ ks log 2 + log log Y + O(1)` (Lemma 5.3).  So, with `k ≤ s+1`,

```
log(A_k + B_k) ≤ s(k+1) log 2 + 2 log M + (3/2) θ(Y) + O(√Y) = O(s² log s) unconditionally,  s² log 2 + O(s log s) generically.
```

## 2. The segment cutoff and the admissible range of `π(Y)` 🎯

Setup on a dyadic block `[N, 2N)`: `s = π(Y(2N)) − 1` (odd primes), `P = P_s` = odd primes `≤ Y(2N)`.  Fix `h ≠ 0`.

**Segment count (95%).**  Put `Ψ_Y(x) = #{m ≤ x : P⁺(m) ≤ Y(m)}`.  Then `Ψ_Y(x) ≤ #{m ≤ x : P⁺(m) ≤ Y(x)} ≤ ∏_{p≤Y(x)} (1 + log_p x) ≤ (1+log₂ x)^{π(Y(x))}`.  Under `π(Y) ≤ log₂ log x` this is `exp((1/log 2 + o(1))(log log x)²) = x^{o(1)}`.  Let `B = ⌈log₂ 2N⌉+1` and let `E = [N,2N) ∩ ⋃_{retained m}[m, m+B)` be the exceptional set.  Every retained `m ∈ [N,2N)` opens an `E`-block, so the complement of `E` is a union of at most `Ψ_Y(2N)+1` runs with a constant truncation set.  `|E| ≤ B·Ψ_Y(2N)`.

**What a kept segment must satisfy.**  On a run starting at `n₀`, write `hR_{n₀} = A/m` in lowest terms.  Then `m` is odd with support in `P`, and `N/(3h) < m ≤ (2N)^s` (section 3, step 3).  For a run of length `L`, let `x = log L/log m`.  Choose `k = ⌈1/x − c − 2⌉`, so that `x ∈ Ĩ_k`.  If `x > 1/(c+2)` use Lemma 2.3.  Theorem 5.1 + Lemma 6.3 then give

```
|Σ_{t<L} e(A 2ᵗ/m)| ≤ L · (A_k+B_k)(1+log m)^{2^{−k}} · L^{−2^{−k−3}}.
```

If `L ≥ N^{1−θ}` then `1/x ≤ s·log(2N)/((1−θ) log N)`, so `k ≤ s/(1−θ) + O(s/log N) + 0.171`.  The saving is `log L/2^{k+3} ≥ (1−θ) log N / 2^{s/(1−θ) + 4 + o(1)}`.

**Why `√N` fails (95%), confirming the review.**  With `θ = 1/2`, `k ≈ 2s` and the saving is `≈ log N/(32·4^s)`.  Under `2^s ≤ (log N)^{1−ε}` that is `(log N)^{2ε−1}`, which tends to infinity only if `ε > 1/2`.  More generally, a cutoff `L₀ = N^{1−θ}` with fixed `θ` works if and only if `θ < ε`.  So the overnight skeleton proves the claim only for `π(Y) ≤ (1/2 − δ) log₂ log n`.

**Repair (90%).**  Take `L₀(N) = N·exp(−(log log N)³)`; the review's `N·exp(−(log log N)⁴)` also works.

- (a) Discarded mass `≤ (Ψ_Y(2N)+1)(L₀ + B) ≤ N·exp(1.45(log log N)² − (log log N)³ + O(log log N)) = o(N)`.
- (b) Kept segments have `θ = (log log N)³/log N`, so `sθ → 0` and `k ≤ s+1` for large `N`.  The saving is then `≥ (1−o(1)) log N/2^{s+4}`.

The full admissible window is `(1/log 2 + δ)(log log N)² ≤ log(N/L₀) = O(log N/log log N)`.  The lower end is (a) and the upper end keeps `2^k ≍ 2^s`.

**Admissible range.**  The block sum is `o(N)` when `log N/2^{s+4} − log(A_k+B_k) − log log N → ∞`, that is, when `2^{π(Y)} · (π(Y)² + log M(P_Y)) = o(log N)`.

- Unconditionally (`log M = O(s² log s)`): **`π(Y(n)) ≤ log₂ log n − 2 log₂ log log n − log₂ log log log n − ω(1)`** (70%).
- If `Σ_{p≤Y} w_p log p = O(Y)` (no large Wieferich excess, unproved): `π(Y(n)) ≤ log₂ log n − 2 log₂ log log n − ω(1)` (65%).
- The note's `π(Y) ≤ log₂ log n − 3 log₂ log log n − O(1)` is inside the unconditional range, hence admissible (75%).  The ratio of saving to cost is then `≳ 2^C (log log n)³ / ((log log n)² log log log n) → ∞`.
- The headline hypothesis `π(Y) ≤ (1−ε) log₂ log n` is far inside it.  The saving is `≥ (log N)^ε/32` against a cost of `O((log log N)² log log log N)` (80%).

Shape check: Vandehey's Theorem 1.4 threshold is `log₂ log m − 3 log₂ log log m`, at fixed `P` with a `(log log m)^{3/2}` saving.  Ours is the uniform-in-`P` analogue with the roles of `m` and `N` tied by `log m ≈ s log N`.

## 3. The six skeleton steps 🔍

| # | Step | Verdict | Confidence |
|---|---|---|---|
| 1 | Tail `0 ≤ 2ⁿζ_Y − R_n ≤ 1/(n+1)` | OK | 99% |
| 2 | 2-adic exceptional shifts `N^{o(1)}` | OK (cited asymptotic misapplied; replace) | 95% |
| 3 | 3-adic survival, `q` bounds, prime support | OK, including varying `Y(m)` | 95% |
| 4 | Segments; discard `< √N` | **GAP, fixable**: `√N` cutoff only gives `ε > 1/2`; use `L₀ = N exp(−(log log N)³)` | 90% |
| 5 | Vandehey 5.1 with `k = π(Y)+5` | **GAP, fixable**: that `k` is never in the nontrivial range; choose `k` per segment via Lemma 6.3 | 85% |
| 6 | Sum + dyadic + Weyl | OK after 4-5 | 90% |

**Step 1.**  `2ⁿζ_Y − R_n = Σ_{retained m>n} 2^{n−m}/m ≤ Σ_{j≥1} 2^{−j}/(n+1)`.  Then `|e(h2ⁿζ_Y) − e(hR_n)| ≤ 2π|h|/(n+1)`, which sums to `O(|h|)` over a block.  No dependence on `Y`.

**Step 2.**  For `n ∉ E` and retained `m ≤ n`, `n − m ≥ B > v₂(m)`, so `2^{n−m}/m` has odd denominator (xi-normality's Lemma `intervals`, verbatim).  `|E ∩ [N,2N)| ≤ B·Ψ_Y(2N) = N^{o(1)}`, using the elementary product bound from section 2.  The note cites `Ψ(x,(log x)^c) = x^{1−1/c+o(1)}`.  That is the `c > 1` regime and says nothing at `Y = o(log x)`, but the conclusion is right with the product bound.  Uniform in `Y`.  The probe confirms odd denominators at all 1329 nonexceptional `n ≤ 4000` for the test `Y`.

**Step 3 (the varying-`Y` question).**  The retained set at shift `n` is `S_n = {m ≤ n : P⁺(m) ≤ Y(m)}`, not "all `Y(n)`-smooth `m ≤ n`".  Three facts make survival independent of that difference:

- (i) Every 3-smooth `m` is retained, because `Y(m) ≥ 3` for every `m`.  So `3^k` and `2·3^k` (when `≤ n`) are in `S_n`, `k = ⌊log₃ n⌋`.
- (ii) Any retained `m ≤ n` with `v₃(m) ≥ k` is `3^k·c` with `c < 3`, so `c ∈ {1,2}`.  Every other retained index has `v₃ < k`.
- (iii) Off `E`, the top terms are `(2^{n−3^k} + 2^{n−2·3^k−1})/3^k`.  The exponent gap `3^k+1` is even, so the numerator is `≡ 2^{b+1} ≢ 0 (mod 3)`.  If only `3^k` is present, the numerator is a power of 2.

So `v₃(R_n) = −k` exactly, and `hR_n = A/q'` in lowest terms has `v₃(q') ≥ k − v₃(h)`, hence `q' > n/3^{v₃(h)+1}`.  **Prime support:** a retained `m ≤ n` has `P⁺(m) ≤ Y(m) ≤ Y(n)` by monotonicity.  So `supp(q') ⊆` odd primes `≤ Y(n) ⊆ P`, and `log q' ≤ Σ_{3≤p≤Y(n)} ⌊log_p n⌋ log p ≤ (π(Y(n))−1) log n`.  Without monotonicity, replace `Y(n)` by `max_{m≤n} Y(m)` in the hypothesis.  **Coprimality:** `gcd(A, q') = 1` by reduction to lowest terms, and `q'` is odd, so it is coprime to `b = 2`.  Both are exactly Theorem 5.1's hypotheses.  The probe confirms `v₃(q) = ⌊log₃ n⌋`, support `⊆ {p ≤ Y(n)}`, and the `log q` bound at every nonexceptional `n ≤ 4000` for a `Y` with three jumps.

**Step 4.**  The run structure is correct.  `R_{n+1} = 2R_n + 1_{S}(n+1)/(n+1)`, so on a run with no retained index `R_{n₀+t} = 2ᵗR_{n₀}`, and `q'` is constant along the run.  The `√N` cutoff is the defect (section 2).

**Step 5.**  The skeleton fixes `k = π(Y)+5 ≈ s+6`.  Vandehey's nontrivial interval is `I_k ≈ [1/(k+c+3), 1/(k+c−1)] = [1/(s+7.8), 1/(s+3.8)]`.  But a long segment at maximal modulus has `x ≈ 1/s`, which exceeds the right endpoint, and smaller moduli push `x` higher.  At such `x`, `m^{−α_k}N^{ν_k} > N`, so the bound is trivial on **every** segment.  The note's own section 3 reasoning ("`k+c+3 > π(Y)`") is the left-endpoint condition only.  Repair: choose `k` per segment from `x` (section 2), which gives `1 ≤ k ≤ s+1`.  Also cite Theorem 5.1 + Lemma 5.4 + Lemma 6.3, never Theorem 1.1/1.4 (`P`-dependent `K`'s).  After the repair the note's bound `≤ L·exp(−c log N/2^{π(Y)})` holds with `c = 1/32 − o(1)`, given the cost estimate of section 1.2.

**Step 6.**  `Σ_{N≤n<2N} e(h2ⁿζ_Y)` has three contributions.  The exceptional and short-run shifts contribute `O(N exp(−(log log N)³ + 1.45(log log N)²))`.  The long runs contribute `O(N exp(−(log N)^ε/32 + O((log log N)² log log log N)))`, and the tail contributes `O(|h|)`.  Altogether `o(N)`.  Dyadic summation gives the full Weyl criterion for every `h ≠ 0`.  Wall's theorem then gives base-2 normality.  Repo glue exists: `WeylCriterion.equidistributed_of_weyl` and `Wall.isNormal_iff_equidistributed_orbit`.

**Adversarial notes that did NOT break anything.**
- The modulus lower bound `q' > N/(3h)` keeps `x ≤ log N/(log N − log 3h) < 1/(c+2)` for large `N`, so `k ≥ 1` or Lemma 2.3 always applies.
- The `Q`-dependence through `m' ≤ 2Q…` in Proposition 4.1 is already inside `A_k`.
- `Y` bounded is allowed by the hypothesis.  It reduces to the finite-`P` theorem with `2, 3 ∈ P`.
- "Unbounded prime support" needs `Y → ∞` in addition.  It is consistent with the hypothesis, e.g. `Y(n) = max(3, p_{⌊½ log₂ log n⌋})`.

## 4. Literature and novelty check (about 30 min) 📚

Instruments and their reach:
- `papers followups 1606.07911` returned 2 citing papers, both factorization-by-diffusion (Cadavid-Hoyos-Jorgenson 2021, 2026), irrelevant.
- Semantic Scholar returned the same 2, and OpenAlex returned 0.  These are thin instruments: Google Scholar was not reachable, so this is a floor, not exhaustion.
- Web searches: smooth or restricted index log series normality, Korobov sums uniform in the prime support, Bailey-Crandall restricted-index log 2.

Findings:
- **Korobov 1990 / Stoneham 1973 / Bailey-Crandall 2002 Theorem 4.8.**  These are single divisibility chains (`Σ_{n = c^{d^j}} 1/(n bⁿ)`, `Σ 1/(c^{n_k} b^{m_k})`) with one fixed prime set.  Vandehey Theorem 7.4 is the same chain shape at fixed `P`.  None has a multi-chain (all smooth indices) or a growing prime set (85% that none of these covers `ζ_Y`).
- **xi-normality** (unknown author, AI-assisted, September 2026) is the closest precedent.  Its finite-`P` theorem ("Theorem `finite`") covers `P` coprime to `b`, or `b = 2` with `3 ∈ P`, at fixed `P`.  The paper's last paragraph explicitly leaves uniformity in `P` open.  Its Lean development proves ONLY `P = {2,3}` (`XiNormality.double_series_binaryNormal`, `Solution.solution : Challenge.Statement`), via exact unit-group orthogonality mod `3^k` with no Vandehey input.  The README says the finite-prime extension, the discrepancy theorem and the optimized lemma are outside the formalization.  Toolchain `v4.34.0-rc2`; this repo is on `v4.33.1`.
- Banks-Shparlinski (arXiv:1605.07553) give absolute constants for character sums with smooth modulus.  This is the wrong sum (multiplicative characters, not `e(a bⁿ/m)`), but it is a possible second engine for a sharper range.
- Shparlinski's open-problems list mentions Korobov sums with smooth moduli and does not ask about uniformity in the prime set (60%; skimmed via search snippet only).

**Novelty estimate: 55% that normality of a growing-smoothness-index log series is new.**  This is unchanged from the note.  The search found no counterexample, but the instruments cannot see the 1972/1992 Korobov books, which were not read.

## 5. Envelope remarks (unchanged from the note, re-checked)

- Section 5 of the note (bounded coefficients `c(m)` with `p ∤ c(p^k)`) is consistent with step 3 (85%).  For the growing-`Y` version in base 2 the condition is needed only at the top 3-adic indices.  The numerator is `≡ 2^{n−2·3^k−1}(c(3^k) + c(2·3^k)) (mod 3)`, so the requirement is `3 ∤ c(3^k)` when `2·3^k > n` and `3 ∤ c(3^k) + c(2·3^k)` otherwise.  Re-check this per coefficient family: for `c = (−1)^{m+1}` in base 2 it fails, since `1 − 1 = 0`.
- The method cannot reach `log 2`: at `Y = n` every index is retained and `L = 1` (95%).

## 6. Lean campaign proposal 🧾

### 6.1 Frozen headline (pseudocode, to be written as Lean declarations)

```lean
namespace NormalNumbers.GrowingLocalizedLog

/-- `m` is retained iff every prime factor of `m` is at most `Y m`. -/
def Retained (Y : ℕ → ℕ) (m : ℕ) : Prop := 1 ≤ m ∧ ∀ p, p.Prime → p ∣ m → p ≤ Y m

noncomputable def zetaY (Y : ℕ → ℕ) : ℝ :=
  ∑' m : ℕ, if Retained Y m then 1 / ((m : ℝ) * 2 ^ m) else 0

theorem zetaY_isNormal (Y : ℕ → ℕ) (hmono : Monotone Y) (h3 : ∀ m, 3 ≤ Y m)
    (ε : ℝ) (hε : 0 < ε)
    (hY : ∀ᶠ n : ℕ in Filter.atTop,
      ((Y n).primeCounting : ℝ) ≤ (1 - ε) * Real.logb 2 (Real.log n)) :
    IsNormal 2 (zetaY Y)

/-- Witness that the theorem has unbounded prime support (cheap corollary). -/
theorem exists_unbounded_zetaY : ∃ Y, Monotone Y ∧ (∀ m, 3 ≤ Y m) ∧ Tendsto Y atTop atTop ∧
    (∀ᶠ n in atTop, ((Y n).primeCounting : ℝ) ≤ (1/2) * Real.logb 2 (Real.log n))
```

Stretch statement (a later node, not the first target): the sharp range `2^{π(Y n)} · (π(Y n)² + log M(P_{Y n})) = o(log n)`, stated with the literal `M`.

### 6.2 Literature inputs as faithful-or-weaker hypothesis Props

| Name | Content | Faithful? |
|---|---|---|
| `Literature.korobov_complete_sum` | `b,m > 1` coprime, `gcd(a,m) = 1`, `1 ≤ N ≤ ord(b,m)` ⟹ `‖Σ_{n=1}^N e(abⁿ/m)‖ < √m (1+log m)` (Korobov 1972 Lemma 2 / book Lemma 32, `d = 1` case as corrected by Vandehey Lemma 2.2) | faithful (weaker: `d = 1` only) |
| `Literature.vandehey_thm51` | For every finite prime set `P` coprime to `b`, `m ∈ ℕ_P`, `gcd(a,m)=1`, `k`, `N`: the Theorem 5.1 bound, with `α_k, γ_k, ν_k, A_k, B_k` as Lean `def`s by the displayed recursion (`M(P)` via `padicValNat` of `b^{2·ord(b,Q)} − 1`) | faithful |
| `Literature.vandehey_optimal_range` (the one consumed) | For `k ≥ 1`, `m^{1/(k+1)} ≤ N ≤ m^{1/k}`: `‖Σ‖ ≤ 2·Abd(P,k+1)·Bbd(P)·N^{1−2^{−k−4}}(1+log m)`, where `Abd, Bbd` are the Lemma 5.4 closed forms | weaker: `[1/(k+1), 1/k] ⊂ Ĩ_k ∪ Ĩ_{k+1}` because `Ĩ_{k+1} ∪ Ĩ_k = [1/(k+c+3), 1/(k+c+1)]` with `k+c+3 > k+1` and `k+c+1 < k`; on the `Ĩ_k` part the exponent `1−2^{−k−3}` and the constant `A_k ≤ Abd(P,k+1)` are dominated; follows from 5.1 + 5.4 + 6.3, with the constant `c` eliminated |

`vandehey_optimal_range ← vandehey_thm51` is a side quest: pure real-number bookkeeping, Lemma 6.3's 11 tabulated values, and `c ∈ (−1.1710, −1.1709)`.  `Literature.korobov_complete_sum` + (5) is Lemma 2.3, which is provable in Lean.  Eq. (5) `m/M ≤ ord(b,m)` is LTE (`Nat.emultiplicity_pow_sub_pow` is in mathlib), so it is a new-math-free lemma, not a Prop.  The xi-normality finite-`P` theorem is **not** worth a Prop: it is fixed-`P`, and the headline with `Y` constant already covers every initial-segment set `{2,3,…,p}`.  Its Lean `Arithmetic.lean` (2-adic cancellation, top 3-adic terms) is the template for N3-N4.  Per the no-vendoring rule, either reprove (about 400 lines, mostly specialised to `{2,3}`) or fork + require at a SHA after the 4.34 bump.

### 6.3 New-math lemmas in dependency order

| # | Lemma | Content | Confidence |
|---|---|---|---|
| N1 | `retained_count_le` | `#{m ≤ x : Retained Y m} ≤ (1 + log₂ x)^{π(Y x)}` (monotone `Y`) | 95% |
| N2 | `tail_bound` | `0 ≤ 2ⁿ ζ_Y − R_n ≤ 1/(n+1)` | 99% |
| N3 | `twoAdic_cancel` | `n ∉ E_N` ⟹ denominator of `R_n` odd | 95% |
| N4 | `threeAdic_exact` | `n ∉ E_N` ⟹ `v₃(R_n) = −⌊log₃ n⌋` (needs only `3 ≤ Y`) | 95% |
| N5 | `den_bounds` | `hR_n = A/q'` reduced: `q'` odd, `supp q' ⊆ {3 ≤ p ≤ Y n}`, `n/3^{v₃ h+1} < q' ≤ n^{π(Y n)−1}` | 95% |
| N6 | `run_structure` | non-`E` runs have constant truncation set, `R_{n₀+t} = 2ᵗR_{n₀}`, `#runs ≤ Ψ_Y(2N)+1` | 95% |
| N7 | `log_M_le` | `log M(P_Y) ≤ (log 2) Σ_{p≤Y}(p−1) + π(Y) log Y` (LTE) | 90% |
| N8 | `korobov_uniform_saving` (**crux**) | from `vandehey_optimal_range` + Lemma 2.3 + N7: `s = π(Y)−1`, `2^s ≤ (log N)^{1−ε}`, `m ∈ ℕ_{P_Y}`, `N/(3h) ≤ m ≤ (2N)^s`, `L ≥ N e^{−(log log N)³}` ⟹ `‖Σ_{t<L} e(A2ᵗ/m)‖ ≤ L·η(N)` with explicit `η → 0` | 80% |
| N9 | `block_weyl_little_o` | `Σ_{N≤n<2N} e(h 2ⁿ ζ_Y) = o(N)` from N1-N8 | 85% |
| N10 | `zetaY_isNormal` | dyadic summation + `equidistributed_of_weyl` + `isNormal_iff_equidistributed_orbit` | 95% |

### 6.4 First treadmill target

**Recommendation: go straight for the headline, conditional on `Literature.vandehey_optimal_range` + `Literature.korobov_complete_sum`.**  Lap 1 freezes 6.1 and 6.2 and states N1-N10 with `sorry`.  It then proves N8 first: it is the only node where the claim could still die, and it is pure real-analysis bookkeeping once the Prop is fixed.  Then N1-N6 (arithmetic, low risk), then N9-N10.

Why not a weaker first milestone:
- **Finite `P`** is the xi-normality paper's known theorem.  It needs the same Vandehey Prop for `|P_odd| ≥ 2`, and its only new content would be formalization, which is not the goal.  The `{2,3}` case is already Lean-proved there.
- **"`|P| ≤ 2` via Pólya-Vinogradov / Korobov Lemma 2.2"** is not a coherent milestone.  Lemma 2.3 suffices only when the modulus has **one** odd prime, so `q ≤ n` and `L ≈ n^{1−o(1)} ≫ √q log q`.  With two odd primes (`{3,5}`, or `{2,3,5}` in base 2) `q` can reach `n²`, so `√q ≥ L` and completion is trivial.  This corrects the note's section 2 remark "Pólya-Vinogradov suffices for `r ≤ 2`", which holds only for `r` counted as odd primes `≤ 1` (85%).  Any growing `Y` has unboundedly many odd primes, so this milestone shares nothing with the target's crux.

Risk register:
- (i) The `Abd` closed form has `2^{s(k+1)}`.  N8 must carry `k ≤ s+1` explicitly, since the saving depends on it.
- (ii) `Real.logb 2 (Real.log n)` is negative or zero for small `n`.  The hypothesis is eventual, so this is fine.
- (iii) `IsNormal` reads `Int.fract`, and `zetaY ∈ (0,1)`.

## 7. Prior-art check, 2026-10-02 (second pass) 📚

Scope: the Lean result `zetaY_isNormal` (`src/NormalNumbers/GrowingLocalizedLog.lean`, branch `wip/g5-prime-subset`), i.e. base-2 normality of `ζ_Y` for every monotone `Y ≥ 3` with `π(Y(n)) ≤ (1−ε) log₂ log n` eventually, conditional on Vandehey Theorem 5.1.  This pass replaces the snippet-level parts of section 4 with sources actually opened.

### 7.1 Sources opened, and what each proves

| Source | Accessed via | What it proves (quoted or precise paraphrase) | Implies or anticipates `ζ_Y`? |
|---|---|---|---|
| N. M. Korobov, *On the distribution of digits in periodic fractions*, Mat. Sb. 89(131) (1972) | zbMATH review 3392547 (full text NOT opened) | Four theorems on `R_n = N_P(δ₁…δₙ, a/m) − Pq^{−n}`, the deviation of digit-block counts in the first `P` digits of `a/m`.  Thm 1 (`P = τ`, full period): bound in terms of the prime divisors of `m`, `R_n = O(1)` as `m` grows with fixed prime divisors.  Thm 3 (`P < τ`): if every exponent `αᵥ ≥ 2`, `R_n = O_ε(m^{1/2+ε})`.  Thm 4: `m = p^α`, Vinogradov-type short-sum bound. | No.  It is about digits of a single rational, not a series construction.  Thm 3 is uniform in the prime set but is nontrivial only for `P ≥ m^{1/2+ε}`; for `ζ_Y` the modulus is up to `n^{π(Y)−1}` against run length `≤ n`, so it is useless once two odd primes occur (same obstruction as section 6.4). |
| N. M. Korobov, *Exponential sums and their applications* (Kluwer 1992; Russian 1989) | zbMATH reviews 52979, 41710; theorem statements as restated by Vandehey 2019 §§2, 7.1 and Bailey-Crandall 2002 §4 (book NOT opened: Google Books API quota exhausted, Springer page behind a bot challenge, no archive.org copy) | Chapter III is "distribution of fractional parts, normal numbers and quadrature formulas".  Restated theorems: Lemma 32 (complete-sum bound `< √m(1+log m)`, `N ≤ ord(b,m)`); Thm 32 (= Vandehey Thm 7.1: odd `m` with all `αᵥ ≥ 2`, `N ≤ τ`: `N_{a,m,s}(N) = N/bᵏ + O(m^{1/2+ε})`, constant depending only on `ε`); Thm 33, p. 171 (`m = p^α`, `p` fixed odd prime, saving `exp(−γ(log N)³/(log p^α)²)`, `γ = 1/(2·10⁶)`). | No, as far as the restated content shows.  The only `P`-uniform estimate (Thm 32) is the `√m` range.  The book's own normal-number constructions in Chapter III were not seen; this is the main remaining gap. |
| A. N. Korobov, *Continued fractions of some normal numbers*, Mat. Zametki 47 (1990) 28-33 (Bailey-Crandall attribute it to N. M. Korobov; zbMATH lists A. N. Korobov) | zbMATH review 4128931 | If `λᵥ, μᵥ` increase and `μᵥ ≥ p^{λᵥ}`, `p ≥ 2` coprime to `q`, then `Σᵥ p^{−λᵥ} q^{−μᵥ}` is normal to base `q`; with `λ_{ν+1} ≥ 2λᵥ`, `μᵥ = p^{λᵥ}` the numbers are algebraically independent with explicit continued fractions. | No.  One fixed integer `p`, one chain, gaps `μᵥ − μ_{ν−1}` at least the modulus. |
| R. G. Stoneham, Acta Arith. 22 (1973) 277-286 | restated in Bailey-Crandall 2002 §1 | `α_{b,c} = Σ_k 1/(cᵏ b^{cᵏ})` is `b`-normal when `c` is an odd prime and `b` is a primitive root mod `c²`. | No.  One prime, one chain. |
| D. H. Bailey, R. E. Crandall, *Random generators and normal numbers*, Exp. Math. 11 (2002) | full PDF, davidhbailey.com `bcnormal.pdf` | Thm 4.8: for coprime `b, c > 1`, `(νₖ)` nondecreasing and `μₖ/c^{γnₖ} ≥ μ_{k−1}/c^{γn_{k−1}}` for some `γ > 1/2`, the number `Σₖ 1/(b^{mₖ} c^{nₖ})` is `b`-normal.  Reproves Korobov's `β_{b,c,d}` (indices `c^{dᵏ}`).  The intro names the general shape `Σ_{n∈S} 1/(n bⁿ)` and asks for sparse index sets. | No.  One fixed `c`, one chain `c^{nₖ}`, and the `γ > 1/2` gap condition is the `√` range again. |
| D. H. Bailey, R. E. Crandall, *On the random character of fundamental constant expansions*, Exp. Math. 10 (2001) | full PDF (preprint in scratchpad) | Hypothesis A: for `rₙ = p(n)/q(n)` rational-polynomial with `deg p < deg q`, the orbit `xₙ = (bx_{n−1} + rₙ) mod 1` has a finite attractor or is equidistributed.  Thm 1.1: on Hypothesis A, `π, log 2, ζ(3)` are 2-normal.  §4 discusses perturbations outside the class (`n/2^{n²−n}`, Champernowne, Euler's `γ`). | No, not even conditionally.  `ζ_Y` has `rₙ = 1_{Retained}(n)/n`, which is not rational-polynomial, so Hypothesis A does not cover it.  The `rₙ = 1/n` case is `log 2`, which our method cannot reach (section 5). |
| H. Kano, *General constructions of normal numbers of Korobov type*, Osaka J. Math. 30 (1993) | zbMATH review 591446 | Satz 1: coprime `a, b > 1`, `a^{λₙ} = O(μₙ)`, `a^{λₙ−λ_{n−1}} ∤ Aₙ`, `Aₙ = O(a^{λₙ})` ⟹ `Σ Aₙ a^{−λₙ} b^{−μₙ}` is normal to base `b` but not to base `ab`.  Subsumes Stoneham 1970, Korobov 1990, Wagner, Kano-Shiokawa 1993. | No.  Fixed `a`, chain, gaps at least the modulus. |
| J. Vandehey, arXiv:1606.07911 (J. Anal. Math. 2019) §7 | full PDF | Thm 7.4: fixed finite `P`, `cₖ ∣ c_{k+1}` supported on `P`, `exp((1+ε) log cₖ/log log cₖ) = o(μₖ)` ⟹ `Σ 1/(cₖ b^{mₖ})` normal.  Thm 2.5 (Bourgain 2005, Thm 8.28) restated, see 7.2. | No (already recorded in the KB note §7).  Fixed `P`, single chain. |
| `CaptainSude/xi-normality`, *Binary normality of a localized logarithm* (no byline; VibeMathed attributes it to "ChatGPT-6 Astra (OpenAI)", 9 September 2026) | repo clone, `paper/*.tex` §5, `docs/CREDITS.md`, vibemathed.com problem page | `F_P(1/2) = Σ_{m∈ℕ_P} 1/(m 2ᵐ)` is 2-normal for `P = {2,3}` (Lean) and for every finite `P` coprime to 2 or with `2, 3 ∈ P` (paper only, via Vandehey).  Closing remark: "A normality argument for these limits would require estimates uniform in the prime set; the constants ... depend on that set."  VibeMathed: no earlier published conjecture located. | The closest precedent, fixed `P` only, and it names our uniformity question as open.  0 forks, 0 stars, last push 2026-09-09. |
| I. E. Shparlinski, *Open problems on exponential and character sums* (UNSW PDF) | full PDF | Problem 2 asks for explicit forms, "with all constants explicitly evaluated", of Bourgain's and Bourgain-Chang's short-sum bounds for `Σ e_m(a gˣ)`.  Problem 4 asks for bounds for very short `N` for almost all `m`.  Nothing on uniformity in a growing prime support, and nothing on normal numbers. | No.  It confirms that explicit Bourgain constants were open when written. |
| T. Tao, blog post 2013-06-22, *Bounding short exponential sums on smooth moduli via Weyl differencing* | search hit only, NOT opened | Title-level: Weyl differencing with smooth moduli for `e(f(n)/q)`, the Polymath8 `q`-van der Corput setting. | Methodological cousin of Vandehey's differencing, different phase (polynomial or rational, not `bⁿ`).  Not an anticipation (60%, unread). |

### 7.2 Two routes to a weaker statement that the literature already supports 🧭

These do not anticipate the theorem, but they move where its novelty lives.

**(a) Soft diagonalization from the fixed-`P` theorem (80% that it works).**  For each fixed `P_k = {primes ≤ p_k}`, Vandehey's Theorem 1.1 gives a block bound `|Σ_{A≤n<B} e(h2ⁿζ)| ≤ ε_k(B)·B` with `ε_k → 0` depending only on `P_k` and `h`, for any index set whose truncation denominators lie in `ℕ_{P_k}`.  This is because the bound depends only on `P` and the modulus.  Pick `Y = p_k` on `[T_k, T_{k+1})` with `T_k ≥ k·T_{k−1}` beyond the point where `ε_k(B) ≤ 1/k` for all `|h| ≤ k`.  Then `|S(N)|/N → 0`, so the resulting `ζ_Y` is normal.  So **"some unbounded `Y` gives a normal `ζ_Y`" follows by diagonalization from the finite-prime theorem in the xi-normality paper** (or directly from Vandehey Theorem 1.1 plus the section 3 denominator facts).  It holds at an ineffective, unspecified growth rate, and no source writes it down.  Consequence for section 6.1: `exists_unbounded_zetaY` is a soft corollary.  The new content is the **explicit, uniform rate** `π(Y) ≤ (1−ε) log₂ log n` for every monotone `Y`, which needs the `P`-explicit constants (section 1) that the diagonal argument avoids.

**(b) Bourgain's uniform theorem (60% that it gives an explicit but far smaller rate).**  Vandehey's restatement of Bourgain Thm 8.28: for `γ ∈ (0,1)` there is `ε(γ) > 0` such that for sufficiently large `m` (depending only on `γ`), if `ord(b,m′) > m′^γ` for all `m′ ∣ m` with `m′ > m^ε`, then `max_a |Σ_{n≤N} e(abⁿ/m)| < N^{1−ε}` for `m^γ < N ≤ ord(b,m)`.  This is uniform in `m`, with no prime-set dependence.  The order hypothesis holds for `m ∈ ℕ_P` once `m′^{1−γ} > M(P)` (eq. 5).  Vandehey's own heuristic extraction of the constants ("approximately given by", towers in `1/γ`) says the bound is nontrivial only when `N ≥ m^{C/√(log log log m)}`.  With `m ≤ n^{π(Y)}` and `N ≈ n`, that would give `ζ_Y` normal for `π(Y(n)) ≲ c·(log log log n)^{1/2}`.  But Bourgain's constants are stated inexplicitly, and Shparlinski's Problem 2 lists making them explicit as open.  So this is not a derivation anyone can cite, and its range is triply-logarithmically smaller than ours.

### 7.3 Searches that returned nothing relevant (instruments and their reach)

- `papers followups 1606.07911` and Semantic Scholar `/citations`: the same 2 factorization-by-diffusion papers (Cadavid-Hoyos-Jorgenson 2021, 2026).  OpenAlex lists 0 citations for the J. Anal. Math. version.  Springer's "cited by" page was not reachable (auth redirect), and neither was Google Scholar.  This is a floor.
- OpenAlex forward citations of Bailey-Crandall 2002 (90 works, full list scanned by title): Stoneham-number follow-ups (Bailey-Borwein 2012 nonnormality, Coons 2014, Bailey-Misiurewicz hot-spot papers), BBP/π experiments, PRNGs.  None concerns smooth or growing-prime index sets.  OpenAlex coverage of 1990s journals is incomplete.
- zbMATH Open API: `au:Korobov ti:normal`, `ti:"Korobov type" ti:normal`, `ti:Stoneham`, `au:Levin ti:normal`.  Levin's papers are discrepancy-optimal constructions (Acta Arith. 1999: discrepancy `O(log² N/N)`), lattice configurations and Markov-normal numbers, all with a fixed base modulus and none with smooth-index series.
- arXiv API full-field searches (Stoneham/Korobov/smooth + normal), and web searches for "smooth"/"friable"/"increasing set of primes" + "normal number", "localized logarithm" + normal, and Dibag + normality: only the xi-normality item and its VibeMathed page.
- GitHub: `gh search repos "localized logarithm"` returns only `CaptainSude/xi-normality`, which has 0 forks.
- NOT accessed: Korobov 1972 full text (mathnet.ru navigation failed), the Korobov 1992 book, Bugeaud, *Distribution modulo one and Diophantine approximation* (2012) chapters 4-5, Stoneham 1970/1974/1976 originals, MathSciNet reviews.  Each is a question, not a negative.

### 7.4 Verdict and updated confidence

- **Explicit-rate theorem** (every monotone `Y ≥ 3` with `π(Y(n)) ≤ (1−ε) log₂ log n`): **not found in any source opened; 70% novel** (up from 55%).  The upgrade rests on the full reads of Bailey-Crandall 2001/2002, Vandehey §7 and the xi-normality paper.  The xi-normality paper explicitly leaves `P`-uniformity open.  The Korobov-line restatements (zbMATH, Vandehey, Bailey-Crandall, Kano) are all fixed-modulus single chains.  The residual 30% is mostly the unread Korobov 1992 Chapter III and Bugeaud chapters 4-5, plus the possibility that someone has extracted explicit Bourgain constants for smooth moduli.
- **Qualitative "`Y` may tend to infinity"**: not stated anywhere I found, but **derivable by soft diagonalization** from the finite-prime theorem (7.2(a), 80%).  Do not headline it as the new content.  Headline the explicit rate and the `P`-uniform Vandehey bookkeeping.
- **Closest prior result**: the xi-normality finite-prime theorem (all finite `P` with `2, 3 ∈ P`, base 2, via Vandehey Theorem 5.1 at fixed `P`).  Among classical work, Vandehey Theorem 7.4 and Bailey-Crandall Theorem 4.8.
