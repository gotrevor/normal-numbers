# Referee report: the constant-tracked proof of `KMT_quant₂` (Parts I–III of `kmt-2023-prop43-k-dependence.md`)

Written 2026-09-20.  Brief: `papers/REFEREE-REQUEST-2026-09-20-kmt-quant2-constants.md`.
Sources consulted: `papers/kmt-2023-multiplicative-correlations.txt` (arXiv:2304.05344, §4, lines 660–1290
of the local text); Thorner–Zaman arXiv:1803.02823 §6, fetched and `pdftotext -layout`'d this session
(their Lemma 6.2 is at line 1015 of the extraction, (6.1)–(6.2) at lines 950–960, Theorem 6.1 at line 970).
**Not consulted: Friedlander–Iwaniec, *Opera de Cribro* (not local), Iwaniec–Kowalski Lemma 6.3.**
Numerics for `T₁`, `T₂` and the `R(k,u₀)` scan were recomputed from scratch, not taken from KB §4e.

Bottom line: the headline results `C₁(k) = exp(O(k²))`, `C₂(k) = exp(O(k²))` survive.
One sub-claim **fails** (II.5's `exp(O(k/log k))` completion factor), three need **corrections**
(II.3's constant, II.4's `s` and remainder, Part III's `Ω(κ)` hypothesis), and the `Ω(κ)` item is
**not closed** against its single source.

---

## 1. II.0 — the three inherited uniformities — **holds**

*Location:* note §II.0; KMT lines 679–695 (Prop 4.3 statement), 719–726 (Step 1 threshold remark).

- **Uniform in the `f_j` (hence in 𝒫).**  Holds.  Prop 4.3 reads "Let `k ≥ 1` and `a₁,…,a_k, h₁,…,h_k ∈ ℕ`
  be **fixed** … Then for any `x ≥ 3`, `ε ∈ (1/log log x, 1/2)` and **any** multiplicative functions
  `f₁,…,f_k : ℕ → 𝔻` we have (4.3) ≪ …".  The `f_j` are quantified *inside* the `≪`, so the constant
  is uniform in them; 𝒫 enters only through `f_j`, so one `C(k)` serves every prime set.  ✔
  (The constant does depend on `a_j, h_j`, which are `k`-dependent in the instance; the note is right to
  push that dependence through Step 2 into `A`, item 2.)
- **`exp(−max_j 𝔻(f_j,1;y,x)²) ≤ exp(−S_𝒫(x^ε))`.**  Holds.  `j*` = least `j ≤ k` with `4^j ∤ h` gives
  `4^{j*−1} | h`, so `h/4^{j*} = m/4` with `4 ∤ m`, so `1 − cos(2πm/4) ∈ {1,2}` ≥ 1, so
  `𝔻(f_{j*},1;x^ε)² = (1−cos)·S_𝒫(x^ε) ≥ S_𝒫(x^ε)`.  Likewise `1 − cos ≤ 2` gives the `√(2 S_𝒫(x^ε,x))`
  weakening.  ✔
- **Threshold absorption.**  Holds.  For `x ≤ x₀`, `ε > 1/log log x` gives
  `1/(8k²ε) < log log x/(8k²) ≤ log log x₀/(8k²)`, so `exp(log log x₀/(8k²))·exp(−1/(8k²ε)) > 1 ≥ |W|`.  ✔
  (Pedantic: `|W| ≤ ⌈x⌉/x ≤ 1 + 1/x`, not `≤ 1`; use `2 exp(log log x₀/(8k²))`.)

*Free observation, in the note's favour:* the hypothesis `ε ∈ (1/log log x, 1/2)` is **empty** unless
`log log x > 2`, i.e. `x > e^{e²} = 1618`.  Every "`x ≥ x₀` absolute" with `x₀ ≤ 1618` is vacuous.

## 2. II.1 — Step 1 / Step 2 tuple sums `T₁`, `T₂` — **holds**

*Location:* note §II.1; KMT (4.6) line 843, (4.7) lines 860–875, (4.8)–(4.10) lines 885–905.

- **`T₁` Euler product is exact, not an estimate.**  For one prime `p`, `e_j = p^{α_j}`, `[e] = p^{max α}`,
  and `#{α ∈ ℕ^k : max α = m} = (m+1)^k − m^k`, so
  `Σ_{e_j|A^∞} 1/[e₁,…,e_k] = ∏_{p|A} Σ_{m≥0} p^{−m}((m+1)^k − m^k)`.  ✔
- **Numerics reproduced independently** (`A = ∏_{p≤k}p`): `log T₁/k²` = 0.526 (k=4), 0.601 (8), 0.574 (16),
  0.629 (32), 0.631 (64) — the note's "≈ 0.6k² for k = 4..64" is accurate **on that range**.  ⚠ It is not a
  constant: 0.627 (96), 0.651 (128), 0.669 (256), rising toward 1 (the asymptotic is
  `π(k)·k log k ~ k²`).  The note's analytic `O(k²)` is the right claim; the 0.6 is range-bound.
- **`T₂`.**  The identity `Σ_{e_j|A^∞}(e₁⋯e_k)^{−1/(10k)} = (∏_{p|A}(1−p^{−1/(10k)})^{−1})^k` and the split
  `e₁^{−1/k} ≤ z^{−9/(10k)} e₁^{−1/(10k)}` both check against (4.7).  `1 − p^{−1/(10k)} ≥ log p/(20k)` for
  `p ≤ k` is right (`1−e^{−t} ≥ t/2` for `t ≤ 1`, `t = log p/(10k) ≤ log k/(10k)`), giving
  `log T₂ ≤ k π(k) log(20k) = O(k²)`.  Recomputed: `log T₂/k²` = 1.92 (k=4), 1.74 (16), 1.72 (32),
  1.54 (64), 1.44 (128).  ✔
- **Absorption of the `z^{−9/(10k)}` leg.**  `z = (log x)^{1/(3k)}` ⟹ `z^{−9/(10k)} = (log x)^{−3/(10k²)}
  = exp(−(3/(10k²))log log x) < exp(−3/(10k²ε))` since `1/ε < log log x`, and `3/10 > 1/4 > 1/8`.  ✔
  This leg sits **outside** Prop 4.4, so it is in the outer `ε` — no `ε'` correction needed (contrast item 4).
- **`A = ∏_{p≤k}p` is legitimate.**  Step 2 uses `A` only through (i) `f̃_j(p^ℓ)=0` for `p|A`, (ii) `a_j | A^∞`,
  (iii) `M = [e] | A^∞`, (iv) the implication in (4.12), whose proof needs only
  `rad(a₁⋯a_k ∏(a_i h_j − a_j h_i)) | A`.  With `a_j = 1`, `h_j = j`, `Δ = ∏_{i<j}(j−i)` has only primes
  `≤ k−1`, so `∏_{p≤k}p` covers it.  ✔  (Only the radical is needed; `Δ | A` is not.)
- Error bookkeeping `O(M/x)` per tuple × `≤ z^k = (log x)^{1/3}` tuples is `≤ (log x)^{1/3}/x`, better than
  the note's `(log x)^{2/3}/x`.  ✔  With `Q = 1` the `O(x^{−1/2})` of (4.9)–(4.10) does not arise.

## 3. II.2 — (4.16)–(4.18) Cauchy–Schwarz + Mertens — **holds**

*Location:* note §II.2; KMT (4.14)–(4.18), lines 1000–1050.

- The "for some `j`" of (4.16) **is a sum over `j`** — see item "Glitch A" below; factor `k`.  ✔
- Everything else is absolute: (4.17)'s `x(log x)^{3/2}/y` (union bound on `p² | a_j n + h_j` plus
  `Ω(n) ≪ log n`), the `x/(log x)^{1/2}` from `a_j, h_j ≤ (log x)^{1/2}`, Mertens' `x log log x/log x`,
  and `Σ_{y<p≤X} 1/p = log(1/ε') + O(1/log y)`.  ✔
- Cauchy–Schwarz constant: `|1−f(p)|² ≤ 2(1−Re f(p))` for `|f| ≤ 1`, so the bound is
  `√2·𝔻(f_j,1;y,X)·(log(1/ε')+O(1))^{1/2}`, and `log(1/ε) ≥ log 2` absorbs the `O(1)`.  Absolute `A₀`.  ✔
- The `x ≥ e^{30}` threshold checks: at `log x = 30`, `x^ε ≥ e^{30/3.4} ≈ 6.6·10³`,
  `(log x)^{3/2} = 164`, `exp(−1/(2ε)) ≥ (log x)^{−1/2} = 0.18`, and `164 ≤ 1.2·10³`.  ✔

## 4. II.3 — (4.20) smooth-number truncation — **holds with two corrections**

*Location:* note §II.3 and Part I "The (4.20) re-run"; KMT (4.20) and the display after it, lines 1070–1100.

**Correction (a) — the exponent is transcribed with a spurious `+5/2`.**  KMT's display is
`x (1/(4kε) − 5)^{−1/(8kε)+5/2}`.  Since `u₀ = 1/(4kε) − 5`, `−u₀/2 = −1/(8kε) + 5/2` **exactly**, so the
paper's exponent *is* `−u₀/2`.  The note writes `u₀^{−u₀/2+5/2}`, i.e. it adds the `+5/2` a second time,
inflating the bound by `u₀^{5/2}`.  Direction is safe (the note over-estimates), but the numeric scan
inherits it: with `−u₀/2` the same scan gives `max log R = 6.21`, not 8.78.

**Correction (b) — the target exponent is in the wrong `ε` (a factor 2).**  This leg lives *inside*
Prop 4.4, whose parameter is `ε' ∈ [ε, 2ε]` (KMT line 905: "Letting `ε' ∈ [ε,2ε]` satisfy `X^{ε'} = x^ε`").
So `1/ε' ∈ [1/(2ε), 1/ε]`, and landing on `exp(−1/(8k²ε'))` delivers only `exp(−1/(16k²ε))` — **not** the
claimed `exp(−1/(8k²ε))`.  The slack exists (II.0 notes the `t=0` case carries `exp(−1/(4k²ε))` and the
statement only asks `exp(−1/(8k²ε))`), but II.0 buys it and II.3 spends it again.  The leg must be run
against `exp(−1/(4k²ε'))`, i.e. `R(k,u₀) = u₀^{−u₀/2}·4(u₀+5)·exp((u₀+5)/k)`.  Recomputed:

| exponent used | target | admissible `u₀ ≥ 5` | scanned `u₀ ≥ 1` |
|---|---|---|---|
| note's `−u₀/2+5/2` | `exp(−1/(8k²ε))` | 8.69 | **8.780** (k=1, u₀≈4.15) — reproduces the note exactly |
| paper's `−u₀/2` | `exp(−1/(8k²ε))` | 4.67 | 6.21 |
| note's `−u₀/2+5/2` | `exp(−1/(4k²ε))` | 13.93 | 13.93 |
| paper's `−u₀/2` | `exp(−1/(4k²ε))` | **9.67** | 9.83 |

So the honest constant is `C_tr(k) ≤ e^{10} k` (or `e^{14} k` if one keeps the note's inflated exponent),
not `e⁹ k`.  **The verdict `O(k)` is unaffected.**  Two further remarks:
- The admissible scan range is `u₀ ≥ 5`, not `u₀ ≥ 1`: `ε ≤ 1/(40k)` and `1/ε = 4k(u₀+5)` force `u₀ ≥ 5`.
- `log R` is strictly decreasing in `k` (only `exp((u₀+5)/ck)` depends on `k`), so the max is at `k = 1`
  and the `k ≤ 64` cap in the scan is not load-bearing.  The `u₀ → ∞` monotonicity claim is right.

**Checks that do hold.**  The Dickman range `z ∈ [y^{10}, y^{(log y)^{1/10}}]` and its consequence
`x^{1/(4k)} ≥ y^{10} ⟺ ε ≤ 1/(40k)` are correct.  `ρ(u) ≪ u^{−u/2}` for `u ≥ 1` is KMT's [21,(1.7)].
The Selberg step is right: `#{e ≤ Y : (e,P(y))=1} ≪ Y/log y` uniformly for `Y ≥ y`, and partial summation
gives `Σ 1/e ≪ log Y/log y = 1/ε` with an absolute constant.  `−log q/log y` is indeed swallowed by the
`−4` (`q ≤ (log x)^{1/2}`, `log y = ε log x ≥ log x/log log x`).  The large-`z` branch's absolute threshold
checks numerically: at `log x = 10^{25}`, `(log x/log log x)^{1/10} − 5 = 206 ≥ 3 log log x = 173`, and the
Hildebrand range `u ≤ exp((log y)^{3/5−δ})` is satisfied since `u ≤ log log x ≪ (log y)^{3/5}`.  ✔
Part I's "literal reading" is also right: `d/du₀[2ku₀ − (u₀/2)log u₀] = 0` at `log u₀ = 4k−1`, value
`u₀/2 = e^{4k−1}/2`.  ✔

## 5. II.4 + Part III — the fundamental lemma — **holds with corrections; sub-item (a) is not closed**

### (a) The restatement — **holds with a correction, and against a single source only**

Thorner–Zaman Lemma 6.2 is verbatim as the note quotes it (extraction line 1015):
`Σ_b θ'_b h̃'(b) ≥ 1 − e^{9κ−s}K^{10}` for a lower-bound β-sieve with `β = 9κ+1`, `s ≥ β`, and the matching
`≤ 1 + e^{9κ−s}K^{10}` for the upper-bound sieve.  So `β = 9κ+1`, `e^{9κ}`, `K^{10}` and the two-sidedness
are confirmed.  ✔

**But the note's `Ω(κ)` hypothesis is not TZ's.**  The note (III.1) states it as
`∏_{w≤p<z}(1−g(p))^{−1} ≤ K(log z/log w)^κ`.  TZ's (6.2) (extraction lines 950–960) reads
```
∏_{w≤p<z} ( 1 − g'(p)/(1 − g'(p) − g''(p)) )^{−1}  ≤  K (log z/log w)^κ     (and the same with g' ↔ g'').
```
Specialised to a single sieve (`g'' = 0`) that is `∏(1 − g/(1−g))^{−1} = ∏((1−g)/(1−2g))`, not `∏(1−g)^{−1}`.
**Smallest counter-observation:** with the KMT density `g(p) = k/p`, take `p` = the least prime `> k`.  Then
`g(p) = k/p > 1/2`, so `1 − g/(1−g) = 1 − k/(p−k) ≤ 1 − k < 0` for `k ≥ 2` — TZ's (6.2) is not merely large,
it is **undefined/negative**, so no `K` exists and Lemma 6.2 does not apply as literally stated.
The note's form is the Friedlander–Iwaniec (5.38) / Iwaniec–Kowalski (6.13) form, and TZ's own proof says
"the assumption [5, (5.38)] corresponds to our (6.2)" with `V(z) = ∏_{p<z}(1−g̃'(p))`, `g̃' = g'/(1−g'')`,
whose `w≤p<z` product is `∏(1−g'(p))^{−1}` when `g''=0`.  So either TZ's printed (6.2) is a misprint for
`∏(1 − g'/(1−g''))^{−1}` (the note's form) or the note's restatement is not licensed by its source.
**Deciding this requires opening *Opera de Cribro* Lemma 6.8 / (5.38), which neither the note's author nor
this referee did.**  The note's own III.4 flags the single-origin risk; this item stays open.

Second correction: TZ's **Theorem 6.1** — the two-sided statement they actually apply — assumes
`s > 9κ + 1 + 10 log K`, not `s ≥ 9κ+1`.  With `K = exp(O(k))` that is `s ≫ k`, so II.4's
"`s ≥ 9k+1`, i.e. `ε ≤ 3/(4(9k+1))`" should read `ε ≤ c/k` for a smaller absolute `c`.  Harmless: II.0's
trivial-range device covers `ε > c/k` at cost `e^{1/(8ck)} = O(1)`.

### (b) The `Ω(κ)` computation in III.2 — **holds** (one constant slip)

Splitting `log ∏(1−k/p)^{−1} = k Σ 1/p + Σ[−log(1−k/p) − k/p]` is right; the `k < p < 2k` piece
(`≤ π(2k)log(k+1) ≤ 2.52k`, using `log(k+1)/log(2k) < 1`) and the `p ≥ 2k` piece
(`−log(1−t)−t ≤ t²` for `t ≤ 1/2`; `k²Σ_{p≥2k}p^{−2} ≤ k/log 2k`) both check.  ✔
**Slip:** "`e^{c₀k/log w} ≤ e^{c₀k}`" needs `log w ≥ 1`; the condition is quantified over `2 ≤ w`, and at
`w = 2` the factor is `e^{1.45 c₀ k}`.  Also Rosser–Schoenfeld gives the Mertens error as `O(1/log²w)`,
not `O(1/log w)` — the note's weaker form is safe.  Neither touches `K = exp(O(k))`.  ✔
The note's own referee question ("is the same `K` good for both `k/p` and `1/p`?") resolves correctly:
`1/p ≤ k/p` makes the mixed product termwise smaller.  ✔

### (c) KMT's use of the lemma — **holds with two corrections**

- **Two-sided: yes.**  (4.22) is an equality with a `(1 + O(exp(−1/(2ε))))` factor (KMT lines 1140–1150),
  so both `λ^+` and `λ^−` are required.  ✔
- **`s` is misidentified.**  The note sets `s = log(X/(d₁⋯d_k))/log y ≥ 3/(4ε)`.  `s` is
  `log(level of distribution)/log z`, not `log(sifted range)/log z`.  The level here is capped near
  `x^{1/2}` by the remainder (see next bullet), giving `s = 1/(2ε)` — which is exactly KMT's literal
  `exp(−1/(2ε))` in (4.22), and is the right reading.  Consequence: `ε ≤ 1/(2(9k+1))`-type thresholds
  rather than `3/(4(9k+1))`.  Shape unchanged.
- **The remainder is not `O(x^{1/2})`.**  The sieve error is `Σ_{m<D}|r_m|` with
  `|A_m| = (ρ(m)/m)N + O(ρ(m))`, `ρ(m) ≤ k^{ω(m)}`; hence `Σ_{m<D} k^{ω(m)} ≍ D(log D)^{k−1}/(k−1)!`.
  With `D ≈ x^{1/2}` this is `x^{1/2}(log x)^{k−1}` per `d`-tuple, so `x^{3/4}(log x)^{k−1}` in total,
  not the note's `x^{1/4}·x^{1/2} = x^{3/4}`.  Still absorbed: `x^{−1/4}(log x)^{k−1} ≤ (log x)^{−1/(8k²)}`
  needs `log x₀(k) = O(k log k)`, i.e. `log log x₀(k) = O(log k)`, consistent with II.0.  ✔ but unstated.
- **Unverified hypothesis at `p | A`.**  (4.23) is proved only for `p ∤ A`, yet the fundamental lemma in
  (4.22) is applied with the product over **all** `p ≤ y`.  For `p | A` the density `ρ(p;d)` can equal 1,
  violating the lemma's `0 ≤ g(p) < 1`.  **Smallest counter-observation:** `k = 2`, `a_j = 1`, `h_j = j`,
  `p = 2 ∤ d`: the forms `w+b+1`, `w+b+2` cover both classes mod 2, so `ρ(2) = 1`.  Degenerate — the sifted
  count and `∏(1−ρ(p))` are both 0, so the conclusion is true — but the hypothesis is not verified, and
  III.2's wave-off ("the product over `p<k` is empty because those primes are not sifted") is wrong:
  KMT sift by `P(y)`, which includes every `p ≤ k`.

## 6. II.5 — (4.25) completion + Lemma 4.5 main term — **fails on one exponent; conclusion survives**

*Location:* note §II.5; KMT (4.25) and the two displays after it, lines 1240–1275; Lemma 4.5, lines 921–960.

**Fails:** the completion factor.  The note writes
`(∏_{p≤y}(1 + 1/p + O(k/p²)))^{k−1} ≤ (A₂ log y)^{k−1}·exp(O(k/log k))`.
The Euler factor of `Σ_{d|P(y)} (1/d)∏_{p|d,p>k}(1−k/p)^{−1}` at a prime `p > k` is exactly
`1 + (1/p)(1−k/p)^{−1} = 1 + 1/(p−k)`, and the expansion `1/p + O(k/p²)` is valid **only for `p ≥ 2k`** —
the very trap the note itself identifies one section earlier, in II.4.
**Smallest counter-observation:** take `k` with `k+1` prime (e.g. `k = 4, 6, 10, 12, 16, …`).  That single
prime contributes `1 + 1/(p−k) = 2` to the bracket, hence `2^{k−1}` to the completion error — already
larger than `exp(O(k/log k))` for every large `k`.  Summing honestly,
`Σ_{k<p<2k} 1/(p−k) = O(log k)`, so the bracket is `A₂ log y · k^{O(1)}` and its `(k−1)`st power costs
`exp(O(k log k))`.  So II.5's arrow "**→ sieve term: `exp(O(k))`**" should read `exp(O(k log k))`.
`exp(O(k log k)) = o(k²)` in the exponent, so `C₂(k) = exp(O(k²))` is unaffected.

**Related inconsistency (internal to the note):** Part I's table row "Lemma 4.5 / (4.25) dimension-`k`
Mertens … `exp(O(k/log k))`" contradicts II.5's own `log E₄₅(k) = O(k log k)`.  One of the two is stale.

**`E₄₅(k) = exp(O(k log k))` itself — holds as an upper bound, invalid derivation.**
- `a_p = (k−1)/(1−k/p)` is right: `(1−1/p)(1−k/p)^{−1} = 1 + a_p/p`.  ✔
- The step `|1+w| ≤ exp(Re w + |w|²/2)` needs `|w_p| < 1`, which fails for `p ≲ 2k` (there `a_p` is
  unbounded: at `p = k+1`, `a_p/p = k−1`).  The Taylor bookkeeping `O((k² + k a_p)/p²)` is therefore not
  licensed on that range, even though it happens to produce the right order.
- It is repairable **exactly**, and with room to spare: the local factor is
  `(1−k/p)|1 + Σ_j f_j(p)(1+a_p/p)/p| ≤ (1−k/p)(1 + k(p−1)/(p(p−k))) = (p²−k)/p² ≤ 1`,
  while `exp(−Σ_j(1−Re f_j(p))/p) ≥ e^{−2k/p} ≥ e^{−2}` for `p > k`.  So the range `(k,2k]` costs
  `exp(O(k/log k))`, not `exp(O(k log k))`.  Lemma 4.5's `a_p = O(1)` hypothesis is `O_k(1)` only, as the
  note assumes.
- `Σ_j 𝔻² ≥ max_j 𝔻²` (all terms ≥ 0), so the passage from the sum to the max is fine.  ✔

**Exponent bookkeeping `(log y)^{−k}·(A₂ log y)^{k−1} = A₂^{k−1}/log y` — holds** (note writes `A₂^k`;
harmless).  ✔

**`(1−k/p)^{−1}` well-defined once `A ∋ k` — holds.**  `(d_j, A) = 1` and `k | A` force `p | d_j ⟹ p > k`.  ✔

**Hildebrand–Tenenbaum threshold — holds.**  `((log x)/(4k))^{1/20} ≥ log log x` is solved by
`log x₀ ≍ 4k·(20 log log log x₀)^{20}`, so `log log x₀(k) = log(4k) + O(log log …) = O(log k)`.  ✔
⚠ The note drops the dyadic-block count (`≈ log x/log 2` values of `D = 2^ℓ`) from the smooth-tail sum;
re-inserting it changes only the same threshold's constant.
⚠ "The first summand is `≤ exp(−1/(2ε))` as in II.3" is asserted, not re-run; it is the same `u log u`
shape and does clear the weaker target `exp(−1/(4k²ε'))` (it needs only `log u ≥ 2/k`).

## 7. II.6 — assembly — **holds with the corrections of items 4, 5, 6**

*Location:* note §II.6.

- **Structure is right.**  `T₁` genuinely multiplies everything coming out of Prop 4.4: in (4.6) the weight
  is `1/[e] = 1/M` and `S(x;e) = (1/(x/M))Σ_{m≤x/M}(…) + O(M/x)`, so each small tuple contributes
  `(1/[e])·(Prop 4.4 bound)`.  `T₂` is a **separate additive** contribution from (4.7), correctly *not*
  multiplied by `T₁`.  ✔
- **Each leg lands where the table says.**  `T₂`/(4.7) → third term ✔ (item 2); `A₀k` from (4.16) → first
  and third ✔ (item 3); `e⁹k` from (4.20) → third ✔ (item 4, constant corrected); `C_FL·E₄₅` from (4.22)
  → third ✔ (item 5); completion → third ✔ (item 6, exponent corrected); Lemma 4.5 main term ×`(log k)²`
  → second ✔.  The `(log k)²` for `𝔻(g_j) → 𝔻(f_j)` is right and conservative: the true deficit is
  `Σ_{p≤k}1/p = log log k + O(1)`, i.e. a factor `e^{O(1)}log k`, not `(log k)²`.
- **One global slip, unbooked anywhere:** the `ε' ∈ [ε,2ε]` factor of item 4(b).  Every leg proved inside
  Prop 4.4 is stated in `ε'` and must be converted at a factor-2 loss.  The slack exists (II.0 buys it
  from the `t=0` improvement `exp(−1/(4k²ε))`) but II.3 spends it a second time.  One line of bookkeeping;
  no change to `exp(O(k²))`.
- **Net:** `C₁(k) = T₁·max(A₀k, E₄₅(log k)²) = exp(O(k²))` ✔ and
  `C₂(k) = T₁·(A₀k + e^{10}k + e²C_FL E₄₅ + exp(O(k log k))) + 2T₂ = exp(O(k²))` ✔, conditional on item
  5(a) (the `Ω(κ)` restatement) being settled against *Opera de Cribro*.  The Lean-side hypotheses
  `log C₁(k) = o(4^k)` and `log log C₂(k) = o(4^k)` hold with enormous margin either way — even the
  discarded `exp(exp(e^{4k}/(2e)))` reading of Part I would satisfy `h₂`.

---

## Glitch A — (4.16) "for some `j`" is a sum over `j` — **confirmed**

*Location:* KMT (4.16) and the line immediately after it (extraction lines 1030–1035).
(4.14) is `|z₁⋯z_m − w₁⋯w_m| ≤ Σ_{j=1}^m |z_j − w_j|` — a sum.  Applying it with `m = k` and then (4.15)
gives `Σ_{j≤k} Σ_{n≤x} Σ_{p^ℓ‖a_j n+h_j, p>y}|1 − f_j(p^ℓ)|`.  The paper's "for some `j ≤ k`" attached
below the display is at best `k·max_j`.  Either reading costs the factor `k`; the note's II.2 is right.
(With `k` fixed this is invisible in KMT's `≪`, so it is a presentational glitch, not an error.)

## Glitch B — (4.25) divides by `1 − k/p` at `p = k` — **confirmed**

*Location:* KMT (4.25), main-term display, `∏_{j=1}^k ∏_{p|d_j} (1−1/p)(1−k/p)^{−1}` (extraction line 1252).
The `d_j` are constrained only by `d_j | P(y)`, `(d_i,d_j)=1`, `(d_j, A) = 1` with `A = Q∆`.  In the
instance `Q = 1` and `∆ = ∏_{i<j}(j−i)`, whose prime factors are all `≤ k−1`.  So when `k` is prime,
`k ∤ A`, `p = k` is an admissible divisor of some `d_j`, and the factor is `(1−1)^{−1} = ∞`.
(The very next display in the paper silently repairs it by writing `∏_{p|d, p>k}`, which is the tell.)
The note's `A = ∏_{p≤k}p` removes it.  ✔

---

## Additional glitches found, not in the note's list

- **Prop 4.4's first term is squared wherever it is used, unsquared where it is stated.**
  Prop 4.3 (line 686) and Prop 4.4 (line 710) both carry `max_j 𝔻(f_j, …; x^ε, x)`, unsquared.  Both
  *applications* — the Step 1 display (line 745) and the Prop 4.4 invocation at the end of §4.1 (line 915) —
  carry `𝔻(…)²`.  The proof settles it: (4.18) produces `x·(log(1/ε))^{1/2}·𝔻(f_j,1;x^ε,x)`, unsquared, so
  the *statements* are correct and the two in-proof superscripts are typos.  The note uses the unsquared
  form throughout.  ✔ (Worth confirming against the published PDF rather than the `pdftotext` extraction.)
- **The end of §4.1 names the wrong distance.**  Prop 4.4 is applied to the `g_j` and delivers
  `𝔻(g_j, 1; ·)`, but the display (line 915) writes `𝔻(f_j, χ_j; x^ε, X)`.  These differ at every `p | A`,
  a factor `exp(Σ_{p|A}1/p) ≍ log k` in the second term.  With `k` fixed it is an unremarked `O_k(1)`;
  the note does book it (II.1's `(log k)²`), but KMT do not.
