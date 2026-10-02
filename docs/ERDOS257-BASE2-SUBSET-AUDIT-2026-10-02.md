# Erdős #257 at base 2 for a proper prime subset: paper audit and route (2026-10-02)

*Audit by Ren (Claude), sweep rank 2 of `docs/OPEN-PROBLEMS-SWEEP-2026-10-02.md`.  Mathematics only, no Lean edits.  Every claim carries a confidence.*

**Target.**  For `S` a set of primes (a reduced residue class `a mod q`, or any `S` with `MertensAP.MertensRate S c C`), is

    c_S(2) = Σ_{p∈S} 1/(2ᵖ − 1) = Σ_n ω_S(n)/2ⁿ

irrational, and better, binary disjunctive?

## Verdict

1. **No new correlation estimate is needed** (80%).  Tao-Teräväinen Theorem 3.1 is a theorem about *arbitrary* real 1-bounded multiplicative `g₁` satisfying an equidistribution hypothesis; the functions their §5 feeds it (avoidance of one bin of very large primes) stay inside that hypothesis class when the bin is cut down to `S`-primes, by the same inclusion-exclusion count.  Their irrationality proof of `Σ ω(n)/2ⁿ` transfers to `ω_S` with one changed step, the variance lower bound (5.21), which a Mertens rate supplies with room to spare.
2. **The repo's own route can reach base-2 *disjunctivity***, which is stronger and also new for `S` = all primes (75% the mathematics closes, conditional on one Literature Prop, TT Thm 3.1(i)).  The b ≥ 3 frame already accepts `bb = 2` (`hbb : 2 ≤ bb` throughout `G4SubsetJunk`, `G4SubsetWitness`); only the *pointwise* very-large-prime term in `hbig` must be replaced by an `L²`/covariance bound, plus a base-2 parameter schedule.
3. **Prior art: none found** for any proper divergent prime subset at base 2 (85%, instruments listed in §3).  TT explicitly flag it as "likely" and unpursued.
4. **Reachable in days** (Lean, conditional on the TT Prop): 50%.  In two weeks of treadmill: 70%.

## 1. Why the base-≥3 argument fails at b = 2 (95%)

The failing inequality is the `hbig` field of `G4.ScheduleWitnessS` (`src/NormalNumbers/G4SubsetWitness.lean`):

    √(4·(1 + log log₂Y − log log₂R)·rowL2 bb K + 2Y²·rowL1 bb K²/|sample|)
      + (log Mx / log Y) · rowL1 bb K   ≤   δbig·(ε·η).

The second summand is the very-large-prime block (`p > Y`) bounded **pointwise** (`G4.abs_blockSum_omegaVL_le`, `G4MediumPrimes.lean`): each argument `≤ Mx` has at most `log Mx / log Y = O(1)` prime factors above `Y`, times the row `ℓ¹` mass

    rowL1 b K = (2/b)^K / (b − 1)        (`G4RowMass.lean`).

At `b = 2` this is exactly 1 (`G4.rowL1_two`), so the left side is `≥ 1` while the right side is `< 1`.  In the paper draft this is `prime-lambert-disjunctivity-fixed-base.md` eq. (5): the pointwise error at resolution `η = 2^{-K/4}` is `(2^{5/4}/b)^K`, which tends to 0 iff `b > 2^{5/4} ≈ 2.38`.

It is not an artefact of the array (95%): `G4.two_pow_le_sum_abs` / `G4.one_le_rowMass_two` (`G4RowMassOptimal.lean`, Maze row `hall_base_two_design`) show every nonzero integer array with vanishing line sums in `K` directions has `ℓ¹ ≥ 2^K`, so killing `K` layers at base 2 always costs exactly the `2^{-K}` it gains.  Every other term is fine at `b = 2` (90%): `rowL2 2 K = 2^{-K}/3` decays, `freqSeed 2 K = 2^{-4}·2^{-K}` still beats the Jackson budget (draft eq. (3), `L·2^{-K} = L^{1-o(1)}`), and `farBound 2` decays in the window depth.

**TT hit the same wall at the same place** (90%).  In TT §5 the alternating coefficients `(−1)^{|ε|}/2^{h+K}` have `ℓ¹` mass `2^{-h}` per near shift, the same exact cancellation, and their (5.40), the very-large-prime part of `κ₃`, is the one step that needs Theorem 3.1.  Their remark that "the case `b > 2` is somewhat easier due to the faster convergence of certain coefficients" is this phenomenon.  The only repair is signed cancellation for `p > Y`, i.e. a two-point covariance bound.

## 2. Does TT's proof transfer to ω_S?

Source: `papers/tao-teravainen-2025-quantitative-correlations.txt` (arXiv 2512.01739v2), §1.3 (lines 185-226), Theorem 3.1 (lines 1566-1600), §5 (lines 3004-3790).

### 2a. The estimate TT need, exactly (95% faithful transcription)

**TT Theorem 3.1, case (i), equidistributed.**  Let `X ≥ 2`, `g₁, g₂ : ℕ → ℂ` 1-bounded multiplicative, `1 ≤ L ≤ log X`, and real `δ_N` for `X^{0.4} ≤ N ≤ X`.  Suppose `g₁` is real-valued, and for all `X^{0.4} ≤ N ≤ X` and all `a, q ∈ ℕ`

    Σ_{N<n≤2N, n≡a (q)} g₁(n) = (N/q)·δ_N + O(N L^{-1}),                        (3.1)

and `g₁(p) = 1` whenever `exp(log^{1/11} X) ≤ p ≤ exp(log^{1/10} X)` (3.2).  Then for a sufficiently small absolute `c > 0` there is `E ⊂ [√X, X]` with `(1/log X)∫_E dt/t ≪ L^{-c}` such that for all `W ∈ [L^c]` and integers `b, h₁, h₂ = O(L^c)`, `h₁ ≠ h₂`,

    (W/N) Σ_{N<n≤2N, n≡b (W)} (g₁(n+h₁) − δ_N)·g₂(n+h₂) ≪ L^{-c}     for all N ∈ [√X, X] \ E.   (3.4)

TT §5.14 apply it with `g₁ = g_ℓ`, `g₂ ∈ {g_{ℓ'}, 1}`, where `g_ℓ` is completely multiplicative with `g_ℓ(p) = 1_{p ∉ J_ℓ}` and `J_1, …, J_L` partition `(R₊, 2x]`, `R₊ = x^{1/100}`, into intervals of equal `log₂`-length.  This yields the covariance bound (5.42):

    E (Σ_{p∈(R₊,2x]} (1_{p | n+r} − 1/p)) · (Σ_{p'∈(R₊,2x]} (1_{p' | n+r'} − 1/p')) = o(1),   r ≠ r'.

### 2b. Is it covered for ω_S?  Yes (85%)

For `ω_S`, replace `J_ℓ` by `J_ℓ ∩ S` and set `g_ℓ^S(p) = 1_{p ∉ J_ℓ ∩ S}`.

* `g_ℓ^S` is real, 1-bounded, completely multiplicative (100%).
* (3.2) holds since `J_ℓ ∩ S ⊂ (x^{1/100}, 2x]` lies above `exp(log^{1/10} X)` (100%).
* (3.1): TT's own verification (§5.14, last display block) is inclusion-exclusion over `≤ 101` primes of the bin, all coprime to `r` after reducing `(a, r) = 1`, with error `r·#{bin products ≤ 2N}/N`, and that count is bounded by the number of `x^{1/100}`-rough integers `≤ 2N`, `≪ N/log N`.  Restricting the bin to `S` only shrinks the set of products, and `δ_N = Σ μ(d)/d` over bin products is again independent of `a, q` (90%).
* So Theorem 3.1 applies verbatim and gives (5.42) with all sums restricted to `p ∈ S` (85%).  The existing repo Prop `CastingOut.TwoPointNaturalCorrelation` (`C3MrtTTThm31.lean`) is case (ii) only, which does **not** apply: `g_ℓ^S` is pretentious (close to 1).  Case (i) needs its own Prop (§4).

### 2c. The rest of TT §5 with ω_S (80% overall)

* **Dilation (5.2).**  `ω_S(pn) = ω_S(n) + 1_{p∈S}(1 − 1_{p|n})`, so `q·Σ_h ω_S(n+ph)/2^h ≡ −q·1_{p∈S}·δ_p(n) (mod 1)`.  The multipliers `p_ε` need not lie in `S`; TT's Hilbert-cube primes in `[P/2, P]` work unchanged (95%).
* **`X_p`** is defined only for `p ∈ S` (`X_p = 0` otherwise, deterministic, put in `S₀`) (100%).
* **`κ₁, κ₂, κ₄, κ₅`, and `κ₃` on large primes `R < p ≤ R₊`** are upper bounds over primes, so restricting to `S` only helps (95%).
* **Variance (5.21)**, the one changed step: `Σ_{p∈S∩S₁} Var X_p ≍ 2^{-K}·Σ_{p∈S, p≤R, p∤W, p≠p_ε} 1/p`.  With `MertensRate S c C`, the sum is `≥ c·log₂R − C − O(log₃ W)`, and `log₂ R ≍ log₂ x`, `2^K ≍ (log₃ x)²`, so the variance tends to infinity (90%).  For residue classes the rate is `G4.MertensAP.mertensRate_residueClass`, already proved.
* **Very large primes (5.40)**: §2b (85%).

The joint conclusion, irrationality of `Σ_{p∈S} 1/(2ᵖ−1)` for every Mertens-rate `S`, follows by TT's argument (80%).

**Side conjecture, every infinite set of primes** (45%).  Erdős 1968 [Er68d] covers pairwise coprime `A` with `Σ_{a∈A} 1/a < ∞` (erdosproblems.com/257), hence every *convergent* prime set.  For divergent `S`, the two constraints in §2c are `mass_S(≤ R) ≫ 2^K ≫ mass_S(R, R₊]`.  Writing `F(u)` for the `S`-mass up to `exp(eᵘ)`, `F(u) ≤ u + O(1)` forbids `F(u + log u) ≥ (1+ε)F(u)` for all large `u`, so a good sequence of `x` exists (70%).  But very sparse `S` may have its mass on primes dividing `W`, and `K` must be retuned against Lemma 5.2 and `κ₅`; I have not checked this (45% the whole thing closes).  If it does, #257 holds for **every** infinite `A ⊆ primes`.

## 3. Prior art (85% that nothing states the target)

* `papers followups 2512.01739` (2026-10-02): two citing papers.
  * **Hughes arXiv:2609.28526** (v1, 2026-09-22), "Effective logarithmic two-point Chowla bounds in every window": Liouville/Möbius only, **logarithmic** averages, `exp₄`-type thresholds; §(4) says outright "We make no claim for general multiplicative functions."  Not an input here, since we need natural averages for pretentious real `g` (95%).
  * **Lau arXiv:2604.15042** (v2): `ω(n+k) ≪ log k` (Erdős #248 line); no irrationality content (95%).
* erdosproblems.com/257 (edited 15 April 2026) and its forum thread (7 comments, read 2026-10-02): known cases `ℕ`, primes, prime powers, pairwise coprime summable, period-2 (Tachiya), summable without coprimality (Plectis/Astra note).  No prime-subset statement (95%).
* `formal-conjectures` PRs matching 257 (`gh pr list --state all`): wcook04's #6528/#6529 (open; weighted, mixed-support, reciprocal-summable variants), #6506 and #4269 (merged; `tsum_top`).  None is a prime subset (90%).
* Pratt arXiv:2409.15185: all primes, conditional on prime tuples (100%).
* **CaptainSude/erdos-borwein-disjunctivity @ `bd98789`** (single commit "Add files via upload", 2026-09-07 package): binary disjunctivity of the Erdős-Borwein constant `E = Σ 1/(2ⁿ−1) = Σ τ(n)/2ⁿ` only (`A = ℕ`), conditional on AGP + a PNT interval supply.  Its mechanism forces divisor counts by exact prime valuations (Campbell's construction); it does not touch `ω`, `ω_S`, or prime subsets (95%).
* TT §1.3 themselves: "It seems likely that the arguments in this paper can also treat other sets `A` that are sufficiently similar to the primes, but we do not pursue this question here."  So the irrationality statement is **expected-but-unwritten** (80%), and its novelty as mathematics is modest.  Base-2 **disjunctivity**, even for `S` = all primes, is not claimed anywhere found (85%); that is the larger prize, and the repo's draft `prime-lambert-disjunctivity-draft.md` is its only written candidate.

## 4. Route for this repo

Use the existing G4 frame at `bb = 2`, not a port of TT §5: the grid (pairwise coprime composite multipliers `d_α`, exact transport) already replaces TT's Hilbert-cube lemma, and the frame proves disjunctivity, which implies irrationality (`IsDisjunctive.irrational`).  An irrationality-only port would still need the same very-large-prime input, so it saves nothing (80%).

### Literature inputs (hypothesis Props, faithful-or-weaker)

**L1. `Literature.TTEquidistributedCorrelation`** (TT 2512.01739 Thm 3.1(i)); faithful-or-weaker (90%):

    ∃ c Cst > 0, ∀ g₁ g₂ : ℕ → ℂ, IsCoprimeMultiplicativeNat g₁ → IsCoprimeMultiplicativeNat g₂ →
      (∀ n, ‖g₁ n‖ ≤ 1) → (∀ n, ‖g₂ n‖ ≤ 1) → (∀ n, (g₁ n).im = 0) →
      ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ log X → ∀ δ : ℝ → ℝ,
      (∀ N : ℝ, X^0.4 ≤ N → N ≤ X → ∀ a q : ℕ, 1 ≤ q →
          ‖Σ_{n ∈ Ioc ⌊N⌋₊ ⌊2N⌋₊, n ≡ a [MOD q]} g₁ n − (N/q)·δ N‖ ≤ N / L) →
      (∀ p, p.Prime → exp(log X ^ (1/11)) ≤ p → p ≤ exp(log X ^ (1/10)) → g₁ p = 1) →
      ∃ E ⊆ Icc (√X) X, MeasurableSet E ∧ ∫_E t⁻¹ ≤ Cst·L^{-c}·log X ∧
        ∀ N : ℕ, √X ≤ N → N ≤ X → (N:ℝ) ∉ E →
        ∀ W b h₁ h₂ : ℕ, 1 ≤ W → W ≤ L^c → h₁ ≤ L^c → h₂ ≤ L^c → h₁ ≠ h₂ →
          ‖(W/N)·Σ_{n ∈ Ioc N (2N), n % W = b % W} (g₁(n+h₁) − δ N)·g₂(n+h₂)‖ ≤ Cst·L^{-c}.

Weakenings relative to TT, each making the Prop weaker: the `O(N L^{-1})` in (3.1) is pinned to constant 1 (a stronger hypothesis), the hypothesis is kept over **real** `N` as in TT, shifts are restricted to `0 ≤ h ≤ L^c`, and the conclusion holds only at natural `N`.  Mirror the shape of `CastingOut.TwoPointNaturalCorrelation`.

Nothing else is literature.  The rough-number count, Chebyshev's `π(x) ≪ x/log x` (from `primorial_le_4_pow`), Mertens (`G4Mertens`) and Mertens in APs (`G4MertensAP`) are proved or elementary.

### New-math lemmas, in dependency order

| # | Lemma | Content | Conf. |
|---|---|---|---|
| N1 | `blockSum_sq_le_of_cov` | Abstract: weights `c_i` with `Σc_i = 0`, any `n`-dependent centre `μ(n)`: `avg (Σ c_i W_i)² ≤ (Σc_i²)·V + (Σ|c_i|)²·κ` when centred second moments are `≤ V` and centred cross moments, `i ≠ i'`, are `≤ κ` in absolute value.  The `n`-dependent centre is free because `Σc = 0` | 95% |
| N2 | `gridFrameW_subset_propD_of_cov` | `PropD` with the pointwise `(log Mx/log Y)·rowL1` replaced by `√(rowL2·V + rowL1²·κ)`, hypothesis `VeryLargeCov` below.  First-moment `bigAvgS` via Cauchy-Schwarz, exactly as the medium block | 90% |
| N3 | `exists_bins` | Partition `S ∩ (Y, Mx]` into `B` consecutive bins of harmonic mass `≤ 1/B + 1/Y` | 90% |
| N4 | `omegaVL_eq_bins` | On `m ≤ Mx`, `Y ≥ Mx^{1/A}`: `ω_{S,>Y}(m) = Σ_ℓ (1 − g_ℓ^S(m)) + err`, `0 ≤ err ≤ A·1[two primes of one bin divide m]`; sample mean of `err` `≤ A·P₀·Σ_ℓ mass_ℓ²` + CRT error | 85% |
| N5 | `ttHyp_bins` | (3.1) for `g_ℓ^S` with `δ_N = Σ_{d ≤ 2N} μ(d)/d` over bin products, error `≪_A N/log N` via the rough-number count; (3.2) trivially | 75% |
| N6 | `veryLargeCov_of_TT` | From L1: choose `X` so that `X/2^j ∉ E_{ℓ,ℓ'}` for all bin pairs and all `j ≤ J₀`; average TT's dyadic block bounds over `apSample X = [0, X)`, the blocks below `X/2^{J₀}` costing `≤ 2^{-J₀}·O(1)`.  This avoids re-basing `apSample` (87 files) onto a dyadic window | 75% |
| N7 | `ScheduleWitnessS₂` + base-2 schedule | `bb = 2` analogue of `SchedB` / `G4SubsetSchedule` with the new `hbig₂`: needs `P₀`, shifts `≤ (log X)^c` and `B²·(log X)^{-c} ≤ (δ·ε·η)²`.  Both are free because `log X ≳ 2^{2^e}` with `e` free up to the moment cap `2^{8K²}/(10⁵ T K)`; constants depend on TT's unknown `c` | 65% |
| N8 | headline | `isDisjunctive_subsetLambert_two (htt : TTEquidistributedCorrelation) (h : MertensRate S c C) : IsDisjunctive 2 (subsetLambert S 2)`; corollaries for residue classes, `S` = all primes (base-2 disjunctivity of `Σ ω(n)/2ⁿ`, which TT do not give), and the #257 shape `Irrational (∑' p : S, 1/(2^p − 1))` | 90% given N1-N7 |

**The key estimate N6 delivers, as the frame Prop** (to state first, 90% it is the right interface):

    def VeryLargeCov (S) (G : GridParams) (X Y : ℕ) (V κ : ℝ) : Prop :=
      ∃ μ : ℕ → ℝ, (∀ i, avg_{n ∈ apSample X G.P₀ G.b₀} (ω_{S,>Y}(n + ρ_i) − μ n)² ≤ V) ∧
        ∀ i i', i ≠ i' → |avg_{n} (ω_{S,>Y}(n+ρ_i) − μ n)·(ω_{S,>Y}(n+ρ_{i'}) − μ n)| ≤ κ

At `bb = 2` the budget needs `√(2^{-K}V/3 + κ) ≤ δbig·ε·η` with `η ≈ 2^{-K/4}`, i.e. `κ ≪ 2^{-K/2}`.  TT give `κ ≪ B²·(log X)^{-c} + 1/B`.

### Effort and confidence

The b ≥ 3 schedule went from parameters to headline in one day (2026-09-14 commits), so N7 is plausibly 1-3 laps once N2 fixes the interface.  N1-N2 one lap; N3-N5 two to three; N6 one to two.  Overall: theorem reachable conditional on L1, **50% in days, 70% in two weeks**; the mathematics closes, 75%.

**First treadmill target:** N1 + N2.  State `VeryLargeCov`, prove `blockSum_sq_le_of_cov` and `gridFrameW_subset_propD_of_cov`, and state L1 beside `CastingOut.TwoPointNaturalCorrelation`.  Done-when: `PropD` at `bb = 2` follows from `VeryLargeCov` with `κ`, `V` free, building green.  This pins the exact interface before any schedule arithmetic, and it is base-generic, so it also gives a second proof route at `b ≥ 3`.
