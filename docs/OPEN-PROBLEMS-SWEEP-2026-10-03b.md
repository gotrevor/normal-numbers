# Open-problem sweep, 2026-10-03b 🔎

Third harvest, deliberately pointed **away** from the seam the last two sweeps mined (Manai's
`Ω_k` and `P`/`Q` questions, Bergelson–Downarowicz, Erdős #257 variants, Campbell's `E`).  The
directions searched were these:
- Fourier decay of other fractal measures (continued-fraction Cantor sets, Bernoulli
  convolutions, self-conformal measures);
- computable points in multi-base digit-condition sets;
- effective discrepancy;
- Lambert-type and arithmetic-function series;
- Erdős irrationality problems.

The new seam this pass found is **Bugeaud's *Distribution modulo one and Diophantine
approximation* (2012), Chapter 10**, a list of 61 problems that this repo had never swept.  The
2026-10-03 sweep flagged it as "a seam for a later sweep".  Per `lean-is-the-record`, the top three
candidates carry draft Lean statements (§§1–3), to be frozen in a worktree.

**Negative inventory read first:**
- the 2026-10-02 and 2026-10-03 sweeps;
- `DIRECTION.md`, `HEADLINES.md` (ranked bets and the "Don't fund" list), and the `STATUS.md`
  achievements to 2026-10-03;
- every `Maze.lean` row title (to "squarefree #257 single-survivor encoding at base 2"), in
  particular "measure-theoretic non-disjunctive witness", "Furstenberg-intersection route" and
  "Martin abnormal number as witness".  Those rows close Bugeaud 10.23 (an irrational rich in
  neither base `r` nor base `s`), so that problem is not re-proposed here.

**Engines checked against the candidates:**
- `ComputableNormalB.exists_computable_absNormal`: any random real on fair coins with polynomial
  Fourier decay and a primitive-recursive dyadic approximation has a computable absolutely
  normal sample.
- `DecayAeNormal`: the second moment `≤ N + K` plus the `j²` subsequence.  This step needs
  **polynomial** decay.
- `BakerBanajiUniformQuarterCantor`: uniform over `C²` maps `F` on `[1/2, 1]` with `|F''|`
  bounded below.
- the `cfDigit` / `cfK` / `cfVal` CF layer (`CFDefs.lean`).

**Instrument limits.**
- Bugeaud's book was read in full from the copy at `staff.dc.uba.ar/becher/aa/Bugeaud2012.pdf`.
  Its problem statements are dated 2012, so each one needed its own freshness check.
- `papers followups` (Semantic Scholar) failed on 2108.06804 (HTTP 404).
- arXiv API phrase search is weak, as before: `abs:"absolutely normal"` returns mostly physics.
- Journal-only papers were reached only through web search.  So "no answer found" means none
  found by these instruments; it does not mean none exists.

## Ranked table

| # | Source | Statement (short) | Mechanism | Unproved premise | Conf. (audit + 2–3 laps) | Weight |
|---|---|---|---|---|---|---|
| 1 | Montgomery, *Ten Lectures* (1994) problem; Queffélec, arXiv math/0608249 §4: "Note that no explicit normal numbers in BAD have been constructed yet." | A **computable absolutely normal number all of whose partial quotients lie in {1,2}** | Fair coins `ω` ↦ `x = [0; 1+ω₀, 1+ω₁, …]`.  Cited polynomial Fourier decay of this Bernoulli measure (Jordan–Sahlsten 1312.3619, finite alphabet with dim > 1/2; or Sahlsten–Stevens 2009.01703, AJM 2024, with no dimension threshold) feeds `exists_computable_absNormal`.  CF convergents give exact rational cylinder endpoints. | none mathematical; the cited decay Prop, plus a CF-cylinder approximation lemma | **75%** | medium: answers a stated survey gap and Montgomery's question in computable form, on a new object class for this repo (CF Cantor sets) |
| 2 | Bugeaud 2012, Problem 10.37 (with the sentence before it: "we do not know whether there are real numbers with all these three properties") | **The middle-third Cantor set contains a Liouville number that is normal to base 2** (and a computable one) | A Cassels-type measure on `K`: fair `{0,2}` ternary digits off a run set `R = ⋃[n_k, w_k n_k]` with `w_k → ∞` slowly.  The runs give the Liouville property.  The Riesz-product second moment is controlled by the free digits at ternary positions `≤ log₃ N`, where `2ʲ mod 3ᴹ` is equidistributed (2 is a primitive root mod `3ᴹ`).  Then DEL along a geometric subsequence. | a quantitative Cassels lemma with a free-digit fraction `f(M)`: `𝔼_μ ‖Σ_{j<N} e(h2ʲx)‖² ≤ N + C N² θ^{\|T∩[1,log₃N]\|}`; plus the `DecayAeNormal` refactor from polynomial decay to a second-moment rate | **20%** (paper 70%) | high: an existence question in Bugeaud's book, open as far as found |
| 3 | Aistleitner–Becher–Scheerer–Slaman 1707.02628 §1 ("any further improvement … would require some truly novel ideas"; Bugeaud's 2017 question); Becher–Lew Deveali 2607.06773 | **A number normal in base 2 and in every odd base with `D_N(2ⁿx) = O((log N)³/N)`**, beating both the almost-everywhere order and the `N^{-1/2}` all-bases barrier in base 2 | `x = α + y`: `α` is Levin's base-2 number (`D_N ≪ (log N)²/N`, cited) and `y` is `μ_S`-random in BLD's sparse Cantor set `C(S)`.  BLD bound only `\|μ̂\| = Π\|cos(πh/2ᵏ)\|`, which does not see the translation, so `α + y` is normal in every odd base a.s.  `{2ⁿy}` is below `1/N` except at `O(\|S∩[1,N]\|·log N) = O((log N)³)` indices, so base-2 discrepancy is perturbed by `O((log N)³/N)`. | cited: Levin 1999 (Acta Arith. 88) and BLD Lemma 5/7 in `\|cos\|`-product form; DEL as a cited Prop or proved (the rate is `(log N)^{-1.005}`, too slow for the `j²` trick) | **30%** | medium: a first trade-off point between Levin's one-base rate and normality in independent bases.  The absolutely-normal upgrade (even bases such as 6 and 10) is open, see §3.4 |
| 4 | Bugeaud 2012, Problems 10.17 and 10.18 (suggested by Rivoal) | Explicit `ξ` normal (resp. absolutely normal) to base `b` with `1/ξ` not normal (resp. not absolutely normal) | `ξ = 1/cantorReal e`.  `F(t) = 1/t` on `[1/2, 1]` has `F'' = 2/t³ ∈ [2,16]`, so `BakerBanajiUniformQuarterCantor` plus the generic engine give a computable `e` with `ξ` absolutely normal, while `1/ξ = cantorReal e` is not normal (`not_isNormal_cantorReal`) | none new | **85%** (about half a lap) | low–medium.  ⚠️ **Same seam** as `ExplicitPQ`: harvest it as a corollary inside the next note, not as a campaign |
| 5 | Pramanik–Zhang 2408.03473 §1, Remark 2 after Thm 1.1 | Optimal Fourier decay of a Rajchman measure on the **absolutely non-normal** numbers.  They reach `1/log⁽³⁾\|ξ\|`; `(log log\|ξ\|)^{-1-κ}` is impossible (PVZZ).  Is `(log log)^{-1+κ}` reachable? | none in the repo; Lyons-type skewed measures | the whole construction | 8% | medium (harmonic analysis) |

## Checked and dropped this pass

- **`Σ μ(n)/2ⁿ` irrational**: elementary, not a target.  If `x = p/q`, write the tails as
  `Tₙ = fₙ − ηₙ` with `fₙ = {2ⁿx}` eventually periodic and `ηₙ ∈ {0,1}`.  Then
  `μ(N) = d_N + η_N − 2η_{N−1}`, where `d` are the (periodic) binary digits of `x`.  At a zero of
  `μ`, this forces `η_{N−1} = η_N = d_N`.  CRT gives zero-runs of `μ` of any length in every
  residue class mod the period, so `d` is constant.  Then `μ(N) = 1` forces `μ ≡ −1` afterwards,
  a contradiction.  `Σ λ(n)/2ⁿ` is trivially irrational (`λ = 2δ − 1`, a unique expansion).  The
  Lambert transforms of `μ`, `λ` and `φ` collapse: to `1/b`, a lacunary series, and a rational.
- **`Σ σ_{2k−1}(n)/bⁿ`**: transcendental by Nesterenko (the values of `E₂`, `E₄`, `E₆`).
  `Σ σ₂(n)/bⁿ` has polynomially growing coefficients, beyond any carry argument here.
- **`θ₃(1/b)² − 1 = Σ r₂(n) b^{-n}` disjunctive?**  Unlikely as posed.  Since `r₂(n) = 0` for
  `n ≡ 3 (mod 4)`, a digit at such a position comes only from rare carries.
- **Bugeaud 10.49, 10.51, 10.54, 10.56**: answered (Becher–Yuhjtman / Scheerer 2017;
  Jackson–Mance–Vandehey 2111.11522; Simmons–Weiss; Vandehey 2017, which this repo reproved).
  **10.53**: Temur 2609.16362.  **10.18's "both normal" cousin** (Mendès France): Becher–Madritsch
  2108.06804.
- **"No AN number with discrepancy below almost-everywhere order in some base"** (Scheerer's
  thesis, 2017): superseded by Aistleitner–Becher–Scheerer–Slaman 1707.02628 (`O(N^{-1/2})` in all
  bases).  Candidate 3 targets the next rung.
- **Bugeaud 10.36** (`‖bⁿξ‖ > b^{-c}` uniformly in `b`): a Schmidt-game problem with no engine
  here.  A heuristic look showed that the bad intervals of different bases can overlap at one
  scale, so the absolute-winning intersection does not apply directly.
- **10.14 and 10.16** (Korobov-optimal discrepancy), **10.21–10.29** (Furstenberg type), **10.48**
  (Mahler/Pillai `0.248163264…`): headline-hard.
- **10.50** (a CF-normal number with low-complexity `b`-ary digits): needs CF-normality almost
  everywhere for a dimension-0 non-self-similar measure, and no engine does that.
- **Bernoulli convolutions / self-conformal measures**: the almost-everywhere normality results
  are done (Algom–Rodriguez Hertz–Wang 2012.06529, Algom's survey 2504.18192, already swept at 5%).
  Computable points add nothing, since the supports are intervals.
- **Mance–Tomaszewski 2608.15866, Algom–Ben Ovadia–Rodriguez Hertz–Shannon 2607.22001,
  Baker–Koivusalo–Troscheit–Zhang 2507.21605, Lee 2412.16621**: no stated open problem with
  engine bearing.

## 1. A computable absolutely normal number with partial quotients in {1,2} (75%)

### 1.1 Source and freshness

- **Montgomery** (*Ten Lectures on the Interface between Analytic Number Theory and Harmonic
  Analysis*, 1994), as quoted by Queffélec: "Does there exist normal numbers with bounded partial
  quotients?"
- **Existence.**  Kaufman 1980 (`F(N)`, `N ≥ 3`) gave a measure with polynomial decay, and
  R. C. Baker observed that DEL then gives normal numbers in BAD.  Queffélec–Ramaré 2003 did
  `N = 2`.  Jordan–Sahlsten 1312.3619 extend this to every Gibbs measure of dimension > 1/2 on a
  finite alphabet, and note that "all Bernoulli measures on badly approximable numbers are Gibbs
  measures".  Sahlsten–Stevens 2009.01703 (AJM 146 (2024)) remove the dimension threshold for
  totally non-linear maps such as the Gauss map.  Hochman–Shmerkin prove almost-sure absolute
  normality for the Hausdorff measure on every `C_Λ`, by a method that gives no rate.
- **Explicit form.**  Queffélec, *Old and new results on normality*, IMS Lecture Notes 48 (2006),
  arXiv math/0608249, §4, after Theorem 4.4: **"Note that no explicit normal numbers in BAD have
  been constructed yet."**

**Prior-art search done:**
1. `papers followups 1312.3619` (Jordan–Sahlsten, 86 citers), filtered for comput / explicit /
   construct / algorithm / normal / badly.  The hits were Fraser 2503.17277, Algom–Baker–Shmerkin
   2111.10082, Baker 2107.02699, Chow–Zafeiropoulos 2103.03605, ARW 2012.06529 and Hambrook
   1604.00411.  None constructs a point.
2. `papers followups` on Becher–Yuhjtman 1704.03622 (10 citers), Scheerer 1701.07979 (7) and Bluhm
   2000 (31): nothing.
3. The TeX of Fraser 2503.17277, Sahlsten–Stevens 2009.01703 and Jordan–Sahlsten 1312.3619,
   grepped for explicit / computable / Montgomery / badly approximable / open: existence only.
   JS §10 asks only whether BAD is a Salem set.
4. The Becher–Carton survey chapter (*Normal numbers and computer science*, 2018), whose
   fractals-and-Diophantine section covers Cassels, Schmidt, BBS, Kaufman, Bugeaud and Bluhm.  It
   lists the computable absolutely normal Liouville number (BHS 2015) and nothing for BAD.
5. Scheerer's thesis (TU Graz), §1.5 "Normal numbers in fractals": existence results only.
6. Four web searches ("computable absolutely normal bounded partial quotients", "explicit
   construction … partial quotients in {1,2} Kaufman", "algorithm absolutely normal badly
   approximable", "Kaufman normal partial quotients computable"): no construction found.

The closest published analogues are computable absolutely normal numbers that are CF-normal
(Becher–Yuhjtman 2017, Scheerer 2017), Liouville (Becher–Heiber–Slaman 2015) or Pisot-normal
(Madritsch–Scheerer–Tichy 2016).  **Freshness about 65%.**  This is the computable form of a 1980
existence theorem, and a Becher-school author could have it in a journal-only note.

### 1.2 Mechanism

For `ω ∈ {0,1}^ℕ` put `G ω = [0; 1+ω₀, 1+ω₁, …]`.  Under `coins`, `G` has the law of the
Bernoulli(1/2) measure on `F({1,2})`.  Its dimension is `log 2 / λ ≈ 0.515` (a Monte Carlo
Lyapunov estimate, `λ ≈ 1.346`), above 1/2 but with little margin.  So cite Sahlsten–Stevens,
which needs no threshold, and keep JS as the cross-check.

1. **Decay (cited).**  `∃ C δ > 0, ∀ ξ ≠ 0, ‖∫ e(ξ G ω) dcoins‖ ≤ C|ξ|^{-δ}`.
2. **Approximation.**  `A(p)` is the lower endpoint of the restricted cylinder of the prefix
   `p`, computed exactly from `cfK`.  For `x ∈ F({1,2})` the depth-`D` cylinder has length
   `≤ 1/q_D² ≤ F_{D+1}^{-2}`, where `F` is Fibonacci.  This is `≤ 2^{-D}` for `D ≥ 2`, and the
   `D ≤ 1` cases are checked by hand inside `[1/3, 1]`.  The base-`b` floors `⌊A p·b^m⌋` are
   primitive recursive (rational arithmetic).
3. **Assembly.**  `ComputableNormalB.exists_computable_absNormal` gives `e` computable with
   `G e` absolutely normal.
4. **Content.**  `cfDigit (G ω) n = 1 + ω n` for all `n`.  This is a CF-uniqueness lemma for an
   infinite CF with digits ≥ 1, which `CFWordBridge` / the `cfCyl` layer should nearly have.

### 1.3 Difficulty check

- **Proved implications:** everything except the cited decay; the engine already exists.
- **Unproved premise:** the decay Prop for this specific Bernoulli measure.  Its faithfulness
  needs a referee pass: SS's hypotheses are a strongly separated Cantor set, a non-atomic Gibbs
  measure and total non-linearity.  The Gauss branches restricted to `{1,2}` are strongly
  separated: first digit 1 puts `x` in about `[0.58, 0.75]`, first digit 2 in about `[0.37, 0.43]`.
- **Known-false siblings.**  The mechanism must not run on these, and it does not:
  - the middle-third Cantor measure in base 3: `μ̂(3ⁿ) ↛ 0`, so the decay premise fails;
  - the one-letter alphabet `{1}`: an atom at `1/φ`, no decay;
  - CF-normality of `G e`: false (all digits ≤ 2), and the mechanism makes no claim about it.
- **Weight caveat:** computable, not "explicit" in Queffélec's sense.  The derandomizer is
  primitive recursive and astronomically slow, so say so in any note.

### 1.4 Draft Lean statement (to freeze)

```lean
import NormalNumbers.ComputableNormalB
import NormalNumbers.CFDefs
import NormalNumbers.ExplicitOmegaK

namespace NormalNumbers.BadNormal

open MeasureTheory NormalNumbers.DecayAeNormal NormalNumbers.ExplicitOmegaK

/-- The CF value `[0; 1+ω₀, 1+ω₁, …]` of a coin sequence (limit of convergents). -/
noncomputable def cfCoin (ω : ℕ → Bool) : ℝ :=
  Filter.limUnder Filter.atTop fun n : ℕ =>
    ((cfVal ((List.range n).map fun i => if ω i then 2 else 1) : ℚ) : ℝ)

namespace Literature

/-- Sahlsten–Stevens, AJM 146 (2024), Thm 1.1 (Gauss map, totally non-linear, strongly separated
finite-alphabet Cantor set, non-atomic Gibbs measure): polynomial Fourier decay.  Instance: the
Bernoulli(1/2) measure on CF digits `{1,2}`.  Cross-check: Jordan–Sahlsten 1312.3619 (dim > 1/2,
here ≈ 0.515). -/
def SahlstenStevensBernoulli12 : Prop :=
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * cfCoin ω) ∂coins‖ ≤ C * |ξ| ^ (-δ)

end Literature

/-- Content locator: the CF digits of `cfCoin ω` are exactly `1 + ω n`.  Provable now, 85%. -/
theorem cfDigit_cfCoin (ω : ℕ → Bool) (n : ℕ) :
    cfDigit (cfCoin ω) n = if ω n then 2 else 1 := by sorry

/-- The dyadic approximation the engine needs.  Provable now, 80%. -/
theorem cfCoin_approx : ∃ A : List Bool → ℝ, (∀ p, 0 ≤ A p) ∧
    (∀ ω D, A (Derandomize.pre ω D) ≤ cfCoin ω ∧
      cfCoin ω ≤ A (Derandomize.pre ω D) + (1 / 2 : ℝ) ^ D) ∧
    Primrec fun x : ℕ × ℕ × List Bool => ⌊A x.2.2 * (x.1 : ℝ) ^ x.2.1⌋₊ := by sorry

/-- **Headline.**  A computable absolutely normal number whose partial quotients all lie in
`{1, 2}`: an explicit-in-the-computable-sense answer to Montgomery's question (Queffélec 2006:
"no explicit normal numbers in BAD have been constructed yet"). -/
theorem exists_computable_absNormal_bad (h : Literature.SahlstenStevensBernoulli12) :
    ∃ e : ℕ → Bool, Computable e ∧ IsAbsNormal (cfCoin e) ∧
      ∀ n, cfDigit (cfCoin e) n ∈ ({1, 2} : Finset ℕ) := by sorry

/-- Guard rule, degenerate case: the constant sequence gives the golden-ratio conjugate, a
quadratic irrational; the headline's witness is not eventually periodic (no claim about `1/φ`). -/
theorem cfCoin_const_false : cfCoin (fun _ => false) = (Real.sqrt 5 - 1) / 2 := by sorry

end NormalNumbers.BadNormal
```

Stretch, same lap: every finite alphabet `A` with `|A| = 2^k` (`k` coins per digit).  The same
proof with `A = {1,…,N}` gives `F(N)` for all `N ≥ 2`, uniformly.

## 2. Bugeaud 10.37: a Liouville number in the middle-third Cantor set, normal to base 2 (20%; paper 70%)

**Audited and frozen 2026-10-03** on branch `proof/cantorliou`: `src/NormalNumbers/CantorLiouville.lean`, verdict in `docs/CANTOR-LIOUVILLE-AUDIT-2026-10-03.md` (sound; open as far as found).  The frozen statements supersede the draft in §2.4.

### 2.1 Source and freshness

Bugeaud 2012, p. 219, verbatim: "There exist Liouville numbers in the middle third Cantor set K
and there are Liouville numbers which are normal to base 2.  Furthermore, K contains numbers
normal to base 2.  But we do not know whether there are real numbers with all these three
properties.  **Problem 10.37.** Prove that the middle third Cantor set contains Liouville numbers
which are normal to base 2."  The book adds: "The above problem concerns the intersection of three
sets, any two of them having non-empty intersection."

**Prior-art search done:**
1. `papers followups` on Bluhm 2000 (PAMS, the Rajchman-measure-on-Liouville paper; 31 citers):
   none about `K`.
2. `papers followups math/0505074` (Levesley–Salp–Velani, Mahler's Cantor problem), filtered for
   Liouville / normal: all hits are dyadic or intrinsic approximation (Allen–Chow–Yu, Baker, Tan–
   Wang–Wu, Bandi 2606.27034, Gilson 2601.11799).  No normality-plus-Liouville result.
3. The Becher–Heiber–Slaman 2015 paper grepped for Cantor: none.  The BLD 2607.06773 intro
   discusses Bluhm's Liouville measure but not `K`.
4. The Becher–Carton survey (2018): lists Cassels and BHS, and does not mention 10.37 as
   answered.
5. Four web searches (combinations of "Liouville", "middle third / triadic Cantor set",
   "normal to base 2", "Bugeaud problem"): nothing.
6. The arXiv API (`all:Liouville AND all:"Cantor set"`): no relevant hit.

**Freshness about 55%.**  The mechanism below is a modest modification of Cassels 1959, which
makes a missed answer plausible.  ⚠️ A referee pass should read Bugeaud–Durand 1305.6501 and the
newest Becher / Bugeaud papers before any lap.

### 2.2 Mechanism

Let `R = ⋃_k [n_k, w_k n_k]` with `w_k → ∞` slowly (`w_k ≤ log n_k`) and `n_{k+1} ≥ e^{w_k n_k}`.
Let `μ` give fair independent `{0,2}` ternary digits at positions `T = ℕ∖R` and `0` on `R`.

1. **`K` and Liouville, for every point of `supp μ`.**  Each point lies in `K`, and
   `|x − p_k/3^{n_k}| ≤ 3^{-w_k n_k} = q_k^{-w_k}` with `w_k → ∞`.  `μ` has no atoms, so
   `μ`-a.e. `x` is irrational.
2. **Second moment.**  For `ξ = h(2ⁱ − 2ʲ)`, `|μ̂(ξ)| = Π_{k∈T} |cos(2πξ/3ᵏ)|`.  Take
   `M = log₃ N − C`.  Over `j ∈ [0, N)`, `2ʲ mod 3ᴹ` runs through full periods (2 is a primitive
   root mod `3ᴹ`), so for fixed `m = i − j` the ternary digits of `ξ mod 3ᴹ` above `v₃(h(2ᵐ−1))`
   are uniform over units.  Spaced positions in `T ∩ [1, M]` then give independent factors
   `≤ θ < 1` with positive probability, which yields
   `𝔼‖Σ_{j<N} e(h2ʲx)‖² ≤ N + C N² θ^{c|T∩[1,M]|} + (pairs with 3ᴹ | 2ᵐ−1, which contribute ≤ C N)`.
3. **Free fraction.**  `|T ∩ [1, M]| ≥ M/(w+1)` at the worst `M`, so the bound is
   `N^{2 − c/w(N)}`.  This is summable along `N_j = ⌊(1+ε)^j⌋` when `w` grows like `log`.
   Interpolate, and Wall gives normality in base 2.
4. **Computable version.**  Coins are the free digits.  The prefix determines `x` within
   `3^{-(next free position)}`, so this needs `ComputableNormal`'s rate-generic variant.

### 2.3 Difficulty check

- **Proved implications:** the Liouville and `K` membership (elementary); Wall; the
  Weyl-to-normality step.
- **Unproved premise:** the quantitative Cassels lemma in step 2 (the content), and the
  `DecayAeNormal` refactor from "polynomial decay" to "second moment `≤ N^{2−g(N)}` with
  `Σ_j N_j^{-g(N_j)} < ∞`" (bookkeeping).
- **Known-false siblings:**
  - *Normality to base 3*: the mechanism must fail, and it does.  The frequencies `h(3ⁱ − 3ʲ)`
    are divisible by high powers of 3 and the Riesz factors are `1`.
  - *Runs with `w_k` fixed*: gives exponent-`w` approximable points, not Liouville.  The theorem
    is still true there, but it is not the claim.
  - *A free set `T` of density zero with `|T ∩ [1,M]| = o(M/log M)`*: the bound degrades to
    `N^{2−o(1)}` along every subsequence and the method stops.  This matches the BLD barrier that
    dimension-zero sets need `≥ log k` free digits per window.
- **Lean cost:** the Cassels lemma is new (a units-mod-`3ᴹ` digit-independence count).  The
  Stoneham proof's `3ⁿ mod 2ᵏ` counts are the mirror image and may port.  Estimate: 3–5 laps.

### 2.4 Draft Lean statement (to freeze)

```lean
namespace NormalNumbers.CantorLiouville

open NormalNumbers.ExplicitOmegaK

/-- The middle-third Cantor set, read through base-3 digits (no digit `1`). -/
def InMiddleThird (x : ℝ) : Prop :=
  x ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ i, digitOf 3 x i ≠ 1

/-- **Bugeaud 2012, Problem 10.37.** -/
theorem exists_liouville_middleThird_normal_two :
    ∃ x : ℝ, InMiddleThird x ∧ Liouville x ∧ IsNormal 2 x := by sorry

/-- The quantitative Cassels lemma (the content).  `T` is the set of free ternary positions. -/
theorem second_moment_cantorT (T : Set ℕ) [DecidablePred (· ∈ T)] (h : ℤ) (hh : h ≠ 0) :
    ∃ C θ : ℝ, 0 < C ∧ θ < 1 ∧ ∀ N : ℕ, 2 ≤ N →
      ∫ x, ‖∑ j ∈ Finset.range N, DecayAeNormal.ee (h * 2 ^ j * x)‖ ^ 2
        ∂(cantorMeasureT T) ≤ C * N + C * N ^ 2 *
          θ ^ (((Finset.range (Nat.log 3 N)).filter (· ∈ T)).card) := by sorry

/-- Computable strengthening. -/
theorem exists_computable_liouville_middleThird_normal_two :
    ∃ e : ℕ → Bool, Computable e ∧ InMiddleThird (cantorLiouvilleReal e) ∧
      Liouville (cantorLiouvilleReal e) ∧ IsNormal 2 (cantorLiouvilleReal e) := by sorry

/-- Guard rule, known-false sibling: the same measure is never normal in base 3. -/
theorem not_isNormal_three_of_inMiddleThird {x : ℝ} (hx : InMiddleThird x) :
    ¬ IsNormal 3 x := by sorry

end NormalNumbers.CantorLiouville
```

`cantorMeasureT T` (the pushforward of coins placed on `T`, digit `2·ω`) and
`cantorLiouvilleReal` (with `T = ℕ ∖ R` for the run set above) are to be defined at freeze time.
`not_isNormal_three_of_inMiddleThird` is immediate (digit `1` has frequency 0).

## 3. Levin rate in base 2, normal in every odd base (30%)

### 3.1 Source and freshness

Aistleitner–Becher–Scheerer–Slaman, arXiv:1707.02628 §1.  Their theorem is an absolutely
normal `x` with `D_N(bⁿx) = O(N^{-1/2})` for every `b`.  They write that `N^{-1/2}` "is a kind of
barrier when constructing the absolutely normal number using probabilistic methods.
Accordingly, any further improvement … would require some truly novel ideas".  They record
Levin's one-base `(log N)²/N` and Bugeaud's 2017 question: Korobov-optimal discrepancy in all
bases at once.  Becher–Scheerer–Slaman 1702.04072 and Alvarez–Becher 1510.02004 say the same.

**Prior-art search done:**
- `papers followups` on 1707.02628 (11 citers: Manai ×4, Nandakumar–Pulari, Carella, Seiller–
  Simonsen, Becher–Carton, Lutz–Mayordomo), 1510.02004 (7) and 1511.03582 (10).  None improves a
  base-2 rate under a normality constraint in other bases.
- `papers followups 2607.06773` (BLD): 0 citers.
- Scheerer's thesis, discrepancy section: no such construction.
- **Freshness about 70%.**  The idea of combining a low-discrepancy number with a dimension-0
  perturbation that is normal elsewhere was not found anywhere.

### 3.2 Mechanism

1. **Base 2.**  `{2ⁿ(α+y)} = {2ⁿα + δₙ}` with `δₙ = {2ⁿy} ≤ 2^{n+1−s⁺(n)}`, where `s⁺(n)` is the
   next element of `S`.  So `δₙ ≤ 1/N` except for `n` within `log₂N` before an element of
   `S ∩ [1, N + log₂N]`.  BLD-sparse sets can be chosen with `|S∩[1,N]|` polylogarithmic (at most `(log N)²`, to be
   checked against BLD's exact sparsity definition at audit), so there are `O((log N)³)` exceptions.  A shift lemma (points moved by `≤ η` off an exceptional set `B`)
   gives `D_N(x) ≤ C·D_N(α) + 2η + |B|/N = O((log N)³/N)`.
2. **Odd bases.**  BLD Lemma 7 bounds `∫‖(1/N)Σ e(rʲhx)‖² dμ_S ≤ C(log N)^{-1.005}` through
   `|μ̂_S(t)| = Π_{k∈S}|cos(πt/2ᵏ)|` only.  The integrand for the translate `α + y` has the same
   absolute Fourier coefficients, so the same bound holds.  DEL (`Σ (1/N)·𝔼|A_N|² < ∞`) then
   gives `α + y` normal in every odd base for `μ_S`-a.e. `y`.
3. **Base 2 normality** follows from step 1; all powers of 2 follow by Maxfield / `PowerBaseReal`.

### 3.3 Difficulty check

- **Proved implications:** the shift lemma (elementary) and translation invariance (exact).
- **Unproved premises (cited):** Levin 1999 (a Literature Prop: `∃ α, D_N(2ⁿα) ≤ C(log N)²/N`),
  BLD Lemmas 5/7 in their `|cos|`-product form (faithful), and DEL (classical; cite it, or prove
  it as a side quest).
- **Known-false sibling:** a positive-dimension perturbation (density-`ε` free binary digits)
  would destroy step 1 (`εN log N` exceptions), and the mechanism correctly refuses it.  Taking
  `y ∈ C(S)` alone (`α = 0`) gives `D_N(2ⁿy) ≍ 1` (`y` is not normal in base 2), so the content
  sits in the `α` + sparse-`y` split, not in either piece.

### 3.4 The absolutely-normal upgrade (open)

Even bases independent of 2 (6, 10, 12, …) are not covered.  For `r = 2ᵃm` (`m` odd), the factor
`2^{an}` shifts the relevant positions of `S` out to `≍ N`, where `S` has density `≍ log N/N`.
BLD's window count then fails, and BLD's Theorem 2 constructs `C(S)` points that are non-normal in
even bases.  BLD's intro says Schmidt's tools extend Theorem 1 to all bases independent of 2.
That extension is the real premise for an absolutely normal number with Levin rate in base 2,
which would be a genuine step past the ABSS barrier in one base.

### 3.5 Draft Lean statement (to freeze)

```lean
namespace NormalNumbers.LevinSparse

/-- Star discrepancy of the first `N` terms of `u` (via `visitCount`). -/
noncomputable def disc (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  ⨆ c ∈ Set.Icc (0 : ℝ) 1, |(visitCount u 0 c N : ℝ) / N - c|

namespace Literature
/-- Levin, Acta Arith. 88 (1999): a base-2 orbit with discrepancy `≪ (log N)²/N`. -/
def Levin1999 : Prop :=
  ∃ α C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    disc (fun n => Int.fract (2 ^ n * α)) N ≤ C * Real.log N ^ 2 / N
/-- Becher–Lew Deveali 2607.06773, Lemma 7, in absolute-Fourier form (for every odd `r ≥ 3`). -/
-- def BLDLemma7 (S : Set ℕ) : Prop  -- transcribe at freeze, in `|μ̂_S|`-product form
-- def BLDSparse (S : Set ℕ) : Prop   -- BLD's sparsity definition, transcribed at freeze
end Literature

/-- **Headline.** -/
theorem exists_levinRate_oddNormal (hL : Literature.Levin1999) (S : Set ℕ)
    (hS : Literature.BLDSparse S) (hB : Literature.BLDLemma7 S) :
    ∃ x : ℝ, (∀ r : ℕ, 3 ≤ r → r % 2 = 1 → IsNormal r x) ∧ IsNormal 2 x ∧
      ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
        disc (fun n => Int.fract (2 ^ n * x)) N ≤ C * Real.log N ^ 3 / N := by sorry

/-- The shift lemma (the content of the base-2 half).  Provable now, 85%. -/
theorem disc_le_of_close (u v : ℕ → ℝ) (N : ℕ) (η : ℝ) (B : Finset ℕ)
    (h : ∀ n < N, n ∉ B → |u n - v n| ≤ η) :
    disc v N ≤ 3 * disc u N + 2 * η + (B.card : ℝ) / N := by sorry

end NormalNumbers.LevinSparse
```

## 4. Bugeaud 10.17 / 10.18 (Rivoal): normal `ξ` with `1/ξ` not normal (85%, same seam)

Verbatim: "Problem 10.17. Let b ≥ 2 be an integer. To give an explicit example of a positive
real number ξ which is simply normal (resp., normal) to base b and for which 1/ξ is not simply
normal (resp., not normal) to base b.  Problem 10.18. To give an explicit example of a positive
real number ξ which is absolutely normal and for which 1/ξ does not share this property."

**Prior art.**
- Existence: Manai 2609.24665 Thm 1.2 (no non-affine `C²` preserver).  The repo's
  `manai-2026-normality-preserving-operations.pdf` was grepped for reciprocal / Rivoal / Bugeaud
  / explicit / computable: no hit.
- Becher–Madritsch 2108.06804 answer the opposite question (`x` and `1/x` both normal).
- A web search ("reciprocal not normal computable … 10.17/10.18") found nothing computable.
- **Freshness about 60%.**

**Mechanism.**  `F(t) = 1/t` on `[1/2, 1]` satisfies the hypotheses of
`BakerBanajiUniformQuarterCantor` with `A₁ = 4`, `a₁ = 1`, `A₂ = 16` and `a₂ = 2`.  So the
`ExplicitOmegaK` / `ExplicitPQ` pipeline gives a computable `e` with `ξ = 1/cantorReal e`
absolutely normal, and `1/ξ = cantorReal e` is not normal in base 2.  This answers 10.17 (`b = 2`)
and 10.18 in the computable sense.  Other bases `b` need the base-`b` quarter-Cantor analogue.

This is a corollary-sized lemma on the seam the instructions said to leave.  Recommendation: add
it as a paragraph to the next outward note, not as a campaign.

## 5. Pramanik–Zhang: optimal decay on the absolutely non-normal numbers (8%)

Verbatim (2408.03473, Remark 2 after Thm 1.1): "for the set of absolutely non-normal numbers
… the Rajchman measure µ given by Theorem 1.1 decays like `1/(log^{(3)}|ξ|)` … We do not know
whether this is optimal."  The obstruction is `(log log|ξ|)^{-1-κ}`, which forces almost-sure
absolute normality (PVZZ Remark 1).  `papers followups 2408.03473`: 3 citers (Lai–Xie
2601.03402, Algom 2504.18192, and the same authors' 2403.01358), none answering it.  The repo has
no construction engine for Rajchman measures on non-normal sets; listed for completeness.

## Recommendation

**Run candidate 1 next.**
- It is engine-native: the generic computable-absolutely-normal engine plus one cited decay Prop
  and a CF-cylinder approximation lemma.
- It points at a new object class for this repo (CF Cantor sets / BAD).
- It answers a stated gap in a survey, Queffélec 2006 on Montgomery's question.
- Plan an audit (SS/JS hypotheses, the referee pass on the cited Prop) plus 1–2 laps.

Fold candidate 4 into the same note as a corollary.

**Candidate 2 (Bugeaud 10.37) is the meatier follow-on.**  It is an existence statement from a
problem list, with a paper-level mechanism at about 70%.  Before any lap, the Lean cost is a new
quantitative Cassels lemma and a rate-generic `DecayAeNormal`.  Run a fresh prior-art pass first
(Bugeaud–Durand 1305.6501, Bugeaud's own post-2012 papers, Becher's group); an expert could plausibly
have done it.

Candidate 3 is a good third: a clean shift lemma on two cited inputs.  Its full absolutely-normal
form is the real prize, and it is blocked on even bases.
