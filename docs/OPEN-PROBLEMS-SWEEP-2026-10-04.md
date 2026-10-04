# Open-problem sweep, 2026-10-04 🔎

Fifth harvest.  Aim: open questions that the engines built on 2026-10-02/03 can reach for the
first time, namely the nested-interval potential (`UniformBad.exists_avoid_of_stagePotential`), the
Cassels second moment with forced zero runs (`CantorLiouville`, `CantorLiouvilleAll`), the slow-schedule
and family derandomizers (`SchedDerandomize`, `SchedFamily`, `FamilyDerandomize*`,
`ComputableNormalB`), sparse perturbation (`LevinSparse`), the cylinder cut (`ExplicitOmegaK`,
`ExplicitPQ`), missing-digit mass distribution (`DigitCantor`) and packing covers
(`DeterministicBD`).  Direction only; nothing here is a result.  The column "Engines" also tags
candidates that the **proposed** engines of `docs/ENGINE-PROPOSALS-2026-10-04.md` would open
(E1 constructive games, E2 log-average statistics, E3 finite-state selection, E4 linear forms in
logarithms, E5 Host / Hochman–Shmerkin entropy).

**Negative inventory read first:** sweeps 10-02, 10-03, 10-03b, 10-03c; `STATUS.md` closed
campaigns to 2026-10-03 (10.36, 10.37 profile, Hertling 10.31 audit, LevinSparse, BadNormal,
ReciprocalNormal, ExplicitPQ, DeterministicBD, `Ω_k`, #257); every `Maze.lean` row title (147
rows, last: "free 2-adic kill plus forced band for E"); `docs/notes/*.md`; the module docstrings of
`UniformBad`, `CantorLiouville`, `CantorLiouvilleAll`, `SchedDerandomize`, `SchedFamily`,
`LevinSparse`, `DeterministicBD`, `DigitCantor`, `ExplicitPQ`, `ComputableNormalB`, `Hertling`,
`EDensityAudit`.  Not re-proposed: E density (closed), Hertling 10.31 (parked, about 12%), Bugeaud
10.60 / 10.39, Pramanik–Zhang, Hughes, Hochman (graded at most 8%), #257 squarefree (Duverney–Tachiya
2019), all of Bugeaud ch. 10 already graded in 10-03b/10-03c.

**Instrument limits.**
- The arXiv API (`export.arxiv.org`) returned HTTP 429 for the whole session, including a retry
  loop with 20 s to 120 s backoff; no API phrase query completed.  Paper texts were fetched from
  `arxiv.org/pdf/` directly, author listings and forward citations came from OpenAlex and
  `papers followups` (Semantic Scholar).  So "no arXiv hit" in this doc means "not found by
  OpenAlex, Semantic Scholar followups and web search", not "not on arXiv".
- Calude–Staiger (ToCS 2018) is paywalled and the CDMTCS report URL is dead; its question was
  seen only in search-engine summaries, so it is listed under "Rejected", not ranked.
- Bugeaud's book was read from the session copy of `staff.dc.uba.ar/becher/aa/Bugeaud2012.pdf`
  (pp. 140–169 and 214–222 this pass).

## Ranked table

| # | Problem | Exact source and verbatim wording | Engines | Crux (unproved premise) | % |
|---|---|---|---|---|---|
| 1 | **A computable point of the middle-third Cantor set `K` with irrationality exponent exactly `μ₀`, normal to every base coprime to 3** (every `μ₀ > 1 + 2 log 3/log 2 ≈ 4.17`) | Unstated interpolation between two items of Bugeaud 2012.  p. 219: "There exist Liouville numbers in the middle third Cantor set K and there are Liouville numbers which are normal to base 2. Furthermore, K contains numbers normal to base 2. But we do not know whether there are real numbers with all these three properties."  p. 220: "The above problem concerns the intersection of three sets, any two of them having non-empty intersection."  p. 158, Thm 7.21: "Let μ be a real number with μ ≥ 2. The middle third Cantor set K contains uncountably many elements whose irrationality exponent is equal to μ." | current: `CantorLiouvilleAll.secondMoment_le_b`, `SchedFamily`, `DigitCantor`-style Frostman bound; no E-engine needed | a Borel–Cantelli upper bound for the irrationality exponent of the forced-run measure, from its Frostman exponent plus the triangle inequality at the forced approximations (§1.3) | **50%** (range `μ₀ > 4.17`); 10% for all `μ₀ > 2` |
| 2 | **`K ∩ BAD` contains a point normal to every base coprime to 3** (computable) | Unstated triple of the same shape.  p. 167: "It was proved in [383, 384, 409] that the set of badly approximable numbers lying in the middle third Cantor set K has the same Hausdorff dimension as K. However, μK-almost no element of K is badly approximable."  Pairwise: `K ∩ BAD` (KTV, KW), `K ∩ N(2)` (Cassels), `BAD ∩ N(2)` (Kaufman) | current: `UniformBad` engine on the `3^m`-adic tree of `K`, `CantorLiouvilleAll` second moment; **E1**, **E5** | a Cassels second moment for a game-built (non-product) measure; per-block total-variation closeness to the product measure is provably not enough (§2.3) | 15% |
| 3 | **Computable `ξ` with `‖bⁿξ‖ > b^{−C}` for every base `b ≥ 2` and `n ≥ 0`, with bounded partial quotients** (computable, uniform-constant 10.36, plus BAD) | Bugeaud 2012 p. 217, "**Problem 10.23.** Give an explicit example of a real irrational number which is rich neither to base r, nor to base s."  p. 219, Problem 10.36 (solved here, noncomputably, `UniformBad.bugeaud_10_36`).  ⚠️ Temur arXiv:2609.16362 (2026-09-14) Thm 1: a **computable** `ξ` with partial quotients in `{1,2}` and "`‖bᵏξ‖ > δ_b := 154^{−2^b}`" for every `b ≥ 2`, `k ≥ 0` | current: `UniformBad` (effectivized stage choice); **E1** | effectivity of the stage choice: the stage-`k` obstacle set is finite and decidable, the `√`-potential comparison needs rational upper bounds with slack (§3.2); polynomial time is a separate open crux | 60% (weight low: upgrade of Temur's `154^{−2^b}` to `b^{−C}`) |
| 4 | **Uniform-constant 10.36 on fractals and in dimension:** `dim_H(F ∩ ⋂_b Bad_b(C)) ≥ dim F − ε` with `C = C(ε, F)` for Ahlfors-regular `F`, and `dim_H ⋂_b Bad_b(C) ≥ 1 − O(2^{−C/4})` | Broderick–Bugeaud–Fishman–Kleinbock–Weiss, arXiv:0909.4251 §5.1: "one can show that given C, γ, ε > 0 and integer b ≥ 2, there exists δ = δ_{C,γ,b,ε} such that dim(K ∩ ⋂_{b∈Z≥2} Ê(b, B(0, δ_{C,γ,b,ε}))) > γ − ε whenever K supports a (C, γ)-absolutely decaying measure. Details will be described elsewhere." | current: `UniformBad` engine on an Ahlfors-regular tree, `DigitCantor.le_dimH_of_one_le_nu`; **E1** | the per-stage count of obstacles meeting a child on a fractal tree, with the constant depending on the regularity constants (a constant independent of `F` is false, §4.3) | 50% (weight low) |
| 5 | **Problem 7.3 / 10.35 below the golden ratio:** for one base `b` and `0 < v < 1`, some `ξ` with `v_b(ξ) = v̂_b(ξ) = v`, `v_{b'}(ξ) = 0` for `b'` multiplicatively independent of `b`, and `μ(ξ) = 2` | Bugeaud 2012 p. 142, "**Problem 7.3.** … Prove that there exist real numbers ξ such that v₁(ξ) = v₁, v_b(ξ) = v_b and v̂_b(ξ) = v̂_b, for every b ∈ B."  Thm 7.5 (Amou–Bugeaud) solves it only under "(1+√5)/2 ≤ v_b ≤ v₁"; "The lower bound (1+√5)/2 in (7.9) is typical of proofs whose main argument is the triangle inequality" | current: forced runs (`CantorLiouville` pattern), `UniformBad` avoidance; **E1**, **E4** | rationals `p'/q'` with `q' ∈ (b^{n/2}, b^n)` near the forced approximations `a/bⁿ`: the union bound over the free choice of `a` diverges (§5.2) | 8% |

Ranking is by expected value, not by probability: row 3 is the likeliest win but only sharpens
a constant in a two-week-old paper.

## 1. `K` ∩ exact irrationality exponent `μ₀` ∩ normal to every base coprime to 3 (50%)

### 1.1 Source and statement

Bugeaud's 10.37 framing (quoted in the table) names three sets that meet pairwise but not, as far
as he knew, jointly: `K`, the Liouville numbers, `N(2)`.  `CantorLiouville` and
`CantorLiouvilleAll` answered it with the profile `IsNormal b x ↔ ¬ 3 ∣ b`.  Theorem 7.21 is the
finite-exponent version of the first pair.  The triple with "Liouville" replaced by "irrationality
exponent exactly `μ₀`" meets pairwise:
- `K ∩ {μ = μ₀}`: Bugeaud Thm 7.21 (explicit `ξ_{μ,λ} = Σ 2·3^{−⌊λμʲ⌋}`), after
  Levesley–Salp–Velani (math/0505074) for `μ ≥ (3+√5)/2`;
- `K ∩ N(2)`: Cassels 1959, Schmidt 1960;
- `{μ = μ₀} ∩ N(2)`: Bugeaud 2002 (C. R. Acad. Sci. 335), via Kaufman/Bluhm measures, and
  Becher–Reimann–Slaman (Monatsh. 2018, `eie.pdf`) give exponent `a` with prescribed dimension;
- `μ₀ = 2` jointly: Weiss 2001 (`μ_K`-a.e. point has exponent 2) plus Cassels, so the triple is
  known at `μ₀ = 2` and serves as a control.

**Statement.**  For every rational `μ₀ > 1 + 2 log 3/log 2`, there is a computable `x ∈ K` with
irrationality exponent exactly `μ₀`, normal to every base `b ≥ 2` with `3 ∤ b`, and not normal to
any base with `3 ∣ b`.

### 1.2 Mechanism

1. **Measure.**  The `CantorLiouville` coin measure with runs `[a_k, μ₀ a_k)` of ternary zeros
   (exponent-`μ₀` runs instead of Liouville runs) and `a_{k+1} ≥ λ_k a_k`, `λ_k → ∞` slowly.
   The run gives `|x − p_k/3^{a_k}| < 3^{−μ₀ a_k}`, so `μ(x) ≥ μ₀` for every coin sequence with
   infinitely many 2s before the runs.
2. **Normality.**  The runs occupy a smaller fraction than the Liouville runs, so
   `secondMoment_le_b` and `le_freeCount` apply verbatim (free count at scale `M` is at least
   `M/μ₀`).  `not_isNormal_of_three_dvd` also transfers (the runs still put `bʲx` near an integer
   for a positive fraction of `j`, though not a fraction tending to 1; the failure for `3 ∣ b`
   then needs the frequency of digit 0 to exceed `1/b`, which holds since runs have positive
   upper density).
3. **Upper bound on the exponent, `τ = μ₀ + ε`.**  For `p/q` with `3^{a_k} ≤ q`:
   - `q ≤ 3^{(μ₀−1)a_k}/2` or `q ≥ (2·3^{a_{k+1}})^{1/(τ−1)}`: the triangle inequality against
     `p_k/3^{a_k}` (resp. `p_{k+1}/3^{a_{k+1}}`) gives `|x − p/q| ≥ 1/(2q·3^{a})` `≥ q^{−τ}`, for
     every coin sequence;
   - the middle range: Borel–Cantelli.  The ball `B(p/q, q^{−τ})` has mass at most
     `2^{−(free digits up to depth τ log₃ q)}`.  Summing `q` balls per `q`, the worst range is
     `q ≈ 3^{a_{k+1}/(τ−1)}`, where the depth enters the next run and the mass stalls at
     `3^{−γ a_{k+1}}` (`γ = log 2/log 3`).  The sum is `≈ 3^{a_{k+1}(2/(τ−1) − γ)}`, summable in
     `k` iff `τ > 1 + 2/γ ≈ 4.17`.
4. **Computable point.**  The upper bound is a countable family of clopen-ish bad events with
   summable mass, which is the `bad'` slot of `SchedDerandomize.exists_computable_normal_sched`
   ("Extra clopen tests (`bad'`) are avoided as well"); `SchedFamily` carries all bases `3 ∤ b`.

### 1.3 Difficulty check

- **Proved implications:** normality and non-normality legs are the existing `CantorLiouvilleAll`
  lemmas with a different run schedule; the lower bound on `μ(x)` is the 10.37 truncation argument.
- **Unproved premise:** step 3, the exponent upper bound.  Its paper form is about one page; the
  Lean form needs a rational-counting Borel–Cantelli over all `p/q` (new infrastructure, no
  existing repo lemma) and the conversion of `¬ LiouvilleWith τ x` into finitely many clopen tests
  for the derandomizer.
- **Mechanism:** Frostman + Borel–Cantelli in the middle range, triangle inequality at the ends.
  For `2 < μ₀ ≤ 4.17` the middle-range sum diverges.  That range needs a count of rationals near
  `K` better than the trivial `q` per denominator, i.e. Broderick–Fishman–Reich Conjecture 1.3 /
  Chow–Varjú–Yu 2402.18395 territory (Fourier `ℓ¹` dimension).  No mechanism known to the repo.
- **Known-false siblings the mechanism must refuse:** base 3 (refused, `tdig_mul_three_pow`
  kills the saving, and every point misses digit 1); `μ₀ < 2` (Dirichlet; the Borel–Cantelli sum
  needs `τ > 4.17`, so nothing below 2 is claimed); "normal to base 6" (refused by
  `not_isNormal_of_three_dvd`; the `μ_K`-a.e. contrast is `Literature.Cassels1959`).
- **Lap estimate:** 2–4 laps for the `μ₀ > 4.17` range.

### 1.4 Prior-art log

| Search | Result |
|---|---|
| `papers followups math/0505074` (LSV, 96 citers) | Cantor-set Diophantine approximation: Bandi 2606.27034, Gilson 2601.11799, Chow–Varjú–Yu 2402.18395, Allen–Chow–Yu 2005.09300, Baker 2203.12477, Schleischitz 1812.10689, Tan–Wang–Wu 2103.00544, Amou–Bugeaud 2010.  None combines exponent with normality |
| `papers followups 1305.6501` (Bugeaud–Durand, 41) | dimension of `K ∩ M(μ)`; no normality |
| `papers followups 1302.5792` (Hochman–Shmerkin, 86) | normality in fractals (Algom, Baker, Dayan–Ganguly–Weiss, Becher–Lew Deveali, Manai, Lai–Xie); no exponent |
| `papers followups 1410.1017` (Becher–Bugeaud–Slaman, computable exponents) | 12 citers, none on `K` or normality |
| `papers followups 2402.18395` (CVY) | He–Liao 2602.01307, Chen 2510.17096, Wyatt 2512.07204: dimension of `K ∩ W(τ)` and `K ∩ E(τ)`; read abstracts and grepped "normal": no normality statements |
| OpenAlex newest works, Bugeaud (to 2026-09-24), Becher (to 2026-07-07), Schleischitz (to 2026-08-27), Shmerkin (to 2026-04-21) | Bugeaud–Kim 2510.02059, Bugeaud–Kaneko–Kim 2510.17177 (exponent vs complexity), Guo–Hussain–Li–Schleischitz 2608.26818 (products of exact sets); none on this triple |
| Becher–Reimann–Slaman `eie.pdf` | exponent `a` with Hausdorff dimension `b ≤ 2/a` on Cantor-like sets in `[0,1]`; no normality, not inside `K` |
| web: "middle third Cantor set prescribed irrationality exponent normal to base 2" | LSV, Bugeaud–Durand, Bugeaud 2008; nothing on the triple |
| web: "Liouville normal Cantor" / "badly approximable" "normal to base" Cantor | 2409.03331 (Tan–Zhou, Fourier dimension of Dirichlet non-improvable vs well-approximable), Fraser–Wheeler 2309.05851 (Exact(ψ) contains normal numbers, not in `K`) |
| `gh pr list --repo google-deepmind/formal-conjectures --search` "Cantor", "irrationality exponent", "Bugeaud", "Liouville" | no file for Bugeaud 10.23/10.35/10.36/10.37; Bugeaud files on `main` (fetched today): 10.4–10.9, 10.32, 10.53, 10.61 |

**Freshness:** about 60% that the triple is unrecorded.

### 1.5 Draft Lean statement (to freeze in a worktree)

```lean
namespace NormalNumbers.CantorExponent

/-- Exact irrationality exponent, in Mathlib's `LiouvilleWith` vocabulary. -/
def HasIrrExponent (x μ₀ : ℝ) : Prop :=
  (∀ p < μ₀, LiouvilleWith p x) ∧ ∀ p > μ₀, ¬ LiouvilleWith p x

/-- Bugeaud 10.37 / Thm 7.21 interpolation: exponent `μ₀`, normal exactly off `3 ∣ b`. -/
theorem exists_computable_mem_cantorSet_irrExponent_normalProfile
    (μ₀ : ℚ) (hμ : 1 + 2 * Real.logb 2 3 < (μ₀ : ℝ)) :
    ∃ x : ℝ, x ∈ cantorSet ∧ HasIrrExponent x μ₀ ∧
      (∃ e : ℕ → Bool, Computable e ∧ x = cantorExpReal μ₀ e) ∧
      ∀ b : ℕ, 2 ≤ b → (IsNormal b x ↔ ¬ 3 ∣ b) := by sorry

/-- Control: at `μ₀ = 2` the triple is literature (Weiss 2001 + Cassels 1959). -/
theorem exists_mem_cantorSet_irrExponent_two_of_literature
    (hW : Literature.Weiss2001CantorExponentTwo) (hC : Literature.Cassels1959) :
    ∃ x ∈ cantorSet, HasIrrExponent x 2 ∧ IsNormal 2 x := by sorry

end NormalNumbers.CantorExponent
```

## 2. `K ∩ BAD ∩ N(b)` for every `b` coprime to 3 (15%)

### 2.1 Statement

Some (computable) `x` in the middle-third Cantor set with bounded partial quotients, normal to
every base `b ≥ 2` with `3 ∤ b`.  `μ_K`-almost no point of `K` is badly approximable
(Einsiedler–Fishman–Shapira 0908.2350), so the Cassels measure does not reach it, and `K` carries
no Rajchman measure, so no Fourier-decay measure reaches it either.

### 2.2 Mechanism (candidate)

- **Set.**  Play the `UniformBad` engine on the `3^m`-adic tree of `K` (children are the `2^m`
  cylinders with digits in `{0,2}`) against the BAD obstacles `B(p/q, c/q²)`, charged early.
  Rationals with `q ≤ Q` are `1/Q²`-separated, so at most 2 obstacles of a stage meet a window,
  and with exponent `1/2 < γ` the cheapest-child step works once `2(√3/2)^m < 1`.  The number of
  bad children is `O(3^{m/2})`, a fraction `O((√3/2)^m)` of `2^m`.
- **Measure.**  The law `ν` of the path that picks a uniformly random good child (coins mapped to
  children with the bad children's slots reassigned) is supported on `K ∩ BAD(c)`.
- **Normality.**  Run the `CantorLiouvilleAll` second moment for `ν`.

### 2.3 Difficulty check

- **The crux, sharpened by a guard.**  The tempting step is "each block's conditional law is
  within total variation `δ_m → 0` of uniform, so the Cassels product survives".  It does not:
  conditioning bounds `|ν̂(ξ)|` by **one** block's saving, not the product, because the good set
  of block `l` depends on the past.  **Known-false sibling:** run the same game against the
  base-2 obstacles `B(a/2ⁿ, 2^{−n−C})` with `C ≈ 3m`.  The per-block bad fraction is equally
  small, and the same "TV-close" argument would prove base-2 normality on `K ∩ Bad₂(C)`, which
  is false (the block `0^C` never occurs).  So a correct proof must use the arithmetic of the
  BAD obstacle centres (cancellation of `Σ_p e(ξ p/q)`, as in Kaufman's measures), which the
  `Bad₂` centres `a/2ⁿ` lack against frequencies `h·2ʲ`.
- **Unproved premise:** a second-moment bound for `ν` at frequencies `h(bᵖ − b^q)`, `3 ∤ b`,
  with a summable rate along a slow schedule.  No mechanism is known to the repo.
- **E5 route:** Hochman–Shmerkin Thm 1.2 needs the scenery distribution of `ν`; the same `Bad₂`
  sibling shows scenery closeness to `μ_K` is not automatic either, since the excluded fraction
  per scale is a constant, not `→ 0`.
- **Weight:** a natural triple in Bugeaud's own framing, not a posed problem.

### 2.4 Prior-art log

| Search | Result |
|---|---|
| `papers followups 0908.2350` (EFS, 47) | Datta–Shao 2504.06795, Beresnevich–Datta–Ghosh 2307.10109 ("Bad is null"), Fishman–Merrill–Simmons 1605.07953, Badziahin–Harrap 1503.04738: winning and nullity; no normality |
| `papers followups 0909.4251` (BBFKW, 33) | Wu 2609.22016, Neckrasov–Wu–Yang 2608.24401, Huang–Li–Wang–Yuan 2512.07686, Lambert–Simmons–Zheng 2512.04236, Algom–Rodriguez Hertz–Wang 2012.06529, Dayan–Ganguly–Weiss 2002.00455; none combines BAD in `K` with normality |
| Hochman–Shmerkin 1302.5792 §1.3.3, read | BAD normal numbers via `C_Λ`; their open question is the converse ("almost all points in the middle-1/3 Cantor set … normal with respect to the Gauss map?"), not this triple |
| Simmons–Weiss (Invent. 2019, White Rose copy) | `μ_K`-a.e. point not BAD; no construction inside `K ∩ BAD` |
| web: "badly approximable" "middle third Cantor set" "normal to base 2" (2 queries) | no paper states the triple |
| Temur 2609.16362, read | computable BAD `ξ` (partial quotients `{1,2}`) rich in no base; not in `K`, not normal |

**Freshness:** about 55%.

## 3. Computable uniform 10.36, with BAD (60%, low weight)

### 3.1 Source and the prior art that resets it

Problem 10.23 asks for an explicit irrational rich in neither of two independent bases.
`UniformBad.exists_irrational_not_isDisjunctive` gives existence for all bases at once, but the
witness is noncomputable (`Classical.choice` in the stage selection).  **Temur arXiv:2609.16362
(2026-09-14), Theorem 1**, verbatim: "There is a computable irrational number ξ = [0; 1, 1+ε₁, 1,
1, 1, 1+ε₂, 1, 1, 1, 1+ε₃, 1, 1, …], εⱼ ∈ {0,1}, such that, for every integer b ≥ 2 and every
k ≥ 0, ‖bᵏξ‖ > δ_b := 154^{−2^b}."  That already gives a computable witness for 10.23 in every
base pair (rich in no base), so the 10.23 reading is prior art.  What remains new is the constant:
`b^{−C}` against Temur's doubly exponential `154^{−2^b}`.

### 3.2 Mechanism and difficulty check

- **Engines:** `exists_avoid_of_stagePotential` with BAD obstacles added (one or two per window
  per stage).  At stage `k` only obstacles with `bⁿ < 64^k` (and `q² < 64^k`) are charged, a finite
  decidable set; the child choice compares finite sums of square roots of rationals with a
  rational threshold.  Replacing `√` by rational upper bounds costs slack in `A`, which
  `newPotential_le` (`< 1/40` against `≈ 0.066`) has.
- **Unproved premise:** none mathematical; the Lean work is a computable re-statement of the
  engine (a `Nat.rec` over decidable child choice) and a `Computable` proof.
- **Open beyond it:** polynomial time.  Stage `k` sees exponentially many bases `b < 64^k`;
  rationals with `q ≤ 64^{k/2}` are found by continued fractions, but `(b, n)` pairs with
  `bⁿ ∈ (64^{k/2}, 64^k]` cannot be enumerated in polynomial time, and the potential argument
  needs all of them.  About 20%.
- **Known-false sibling:** `C ≤ 1` (`not_uniformBad_of_le_one`); refused by `newPotential_le`.

### 3.3 Prior-art log

| Search | Result |
|---|---|
| web: explicit irrational not rich in base 2 and 3 / "Problem 10.23" / computable | found Temur 2609.16362 (above); also Kristiansen et al. APAL 2020 (representation complexity, not richness) |
| `papers followups 2609.16362` | 0 citers |
| web: computable `b`-badly approximable for every base / Schmidt game effective | BBFKW, Kleinbock–Weiss, Lambert–Simmons–Zheng 2512.04236; none computable with a uniform constant |
| `formal-conjectures` PR search "Bugeaud", "rich" | #6790 (normal/rich equivalences, open), no 10.23 or 10.36 file |

## 4. Uniform 10.36 on fractals and in dimension (50%, low weight)

### 4.1 Source

BBFKW §5.1 (quoted in the table) states a dimension bound with a `b`-dependent `δ_{C,γ,b,ε}` on
supports of absolutely decaying measures and defers details.  Akhunzhanov (Mat. Zametki 2002,
2004, via BBFKW refs [1, 2]) gives `dim ⋂_b Ê(b, B(0, δ_{b,ε})) ≥ 1 − ε` with explicit
`b`-dependent `δ_{b,ε}`.  The uniform version (`δ_b = b^{−C(ε)}`) is not stated anywhere found.

### 4.2 Mechanism

The engine already selects among `≥ K − O(√K)` good children per stage (bad children carry old
potential `≥ θ − A`, and `Σ old ≤ 2√K Φ`).  With `K ≈ 2^{C/2}/14` the invariant holds, and a
uniform-branching Cantor subset gives `dim ≥ log(K − c√K)/log K = 1 − O(2^{−C/4})` by mass
distribution (the `DigitCantor.le_dimH_of_one_le_nu` pattern).  On an Ahlfors-regular `F`, run the
engine on `F`'s tree with potential exponent `s < dim F`.

### 4.3 Difficulty check

- **Unproved premise:** the per-stage count "an obstacle of radius `< ℓ/(2K)` meets at most `c(F)`
  children" on a general Ahlfors-regular tree.
- **Known-false sibling (the constant must depend on `F`):** `F` = binary digits in blocks of
  length `L` whose first `C₀` digits are 0 and the rest free.  `F` is Ahlfors regular of dimension
  `(L − C₀)/L`, and every point has `‖2^{jL}x‖ < 2^{−C₀}`, so `F ∩ Bad₂(C₀) = ∅`.  A statement with
  `C` independent of `F` is false; the mechanism refuses it because the stage count needs
  `C ≳ log(regularity constant)`.
- **Prior art:** Huang–Li–Wang–Yuan 2512.07686 prove `dim(S ∩ K) = dim K` for hyperplane
  absolute winning `S` on self-conformal `K`, answering BBFKW §5.4 for β-transformations.
  `Bad_b(C)` with `C` fixed is not winning (only `⋃_C Bad_b(C)` is), so the uniform-constant
  statement is not covered.  Freshness about 55%; weight low.

## 5. Problem 7.3 below the golden ratio (8%)

### 5.1 Source

Bugeaud 2012 Problem 7.3 (= 10.35), quoted in the table, with Amou–Bugeaud's partial solution
Thm 7.5 restricted to `v_b ≥ (1+√5)/2`.  Notes p. 166: Amou–Bugeaud also show that `{v₁ = 2v+1,
v_b = v ∀b}` has dimension `1/(v+1)` (intersective sets), so the coupled values are reachable
metrically; independent small values are not.

### 5.2 Difficulty check

- **Engines:** forced approximations `a/bⁿ` at sparse `n` (the run pattern of `CantorLiouville`)
  and avoidance of everything else (`UniformBad` with exponent-`(2+ε)` obstacles).
- **Crux:** near a forced `a/bⁿ`, rationals `p'/q'` with `q' ∈ (b^{n/2}, b^n)` are
  `b^{−n}`-dense; a union bound over the free choice of `a` sums to `≈ Q²/bⁿ ≫ 1`.  Dimension
  arguments fail too: `dim{μ ≥ 2+ε} = 2/(2+ε) > 1/(1+v) = dim{v_b ≥ v}`.  This is the
  triangle-inequality barrier Bugeaud names.  No mechanism known.
- **Known-false sibling:** prescribing `v₄ ≠ v₂` contradicts (7.6) `v_b = v_{bᵗ}`; any mechanism
  must respect Lemma 7.2's constraints and refuse it.
- **Prior art:** `papers followups math/0505074` lists Amou–Bugeaud 2010 and Guillot 2406.07082
  (subspace exponents); Bugeaud–Liao 1404.1889 (uniform `b`-ary exponents, dimension); none
  closes the small range.

## Questions only a proposed engine reaches

| Engine | Problem, source, verbatim | Prior-art check | Note | % |
|---|---|---|---|---|
| **E4** | **Is the Stoneham constant `α_{2,3} = Σ 3^{−k} 2^{−3^k}` normal to base 3?**  Bailey–Borwein, *Nonnormality of Stoneham constants*, Ramanujan J. 29 (2012), §5 (davidhbailey.com copy): "it is not known at the present time whether or not α2,3 is 3-normal, although it appears to be. … But there is no proof of 3-normality. Similar questions remain in the more general case of αb,c" | OpenAlex citers of the paper (11, listed 2026-10-04): Coons 1212.3449 (digit counts of `1/pᵐ`, proves two Aragón–Bailey–Borwein conjectures, not this), Vandehey 1512.00337, surveys; none answers it.  Repo: `Stoneham*.lean` cover base 2 and the base-6 failure; Maze rows "sparse Stoneham relative as open", "Stoneham base-6 as a new method" | Base-3 digits at positions `≈ [0.63·3^K, 1.89·3^K)` are `3ⁿ a mod 2^{3^K}` for `n` of order `3^K`, a window exponentially shorter than the period `2^{3^K−2}`: the high 2-adic digits of `3ⁿ`, Lagarias / Erdős #406 territory.  E4 supplies scale separation, not this short-orbit equidistribution.  Known-false sibling: base 6 (`StonehamSixFailure`) | 3% |
| **E1** | Row 4 above in its winning-set form: "is the 10.36 set winning on `K` with a uniform constant" (BBFKW §5.1) | as row 4 | E1 turns row 4 into one application of `winning_iInter` + `dimH_eq_one_of_winning` | (row 4) |
| **E3** | No new question found.  Carton 1904.09133, 2006.00891 and Carton–Vandehey 1905.05801 were grepped for open questions: none stated.  The standing E3 candidate is Pulari 2602.01199 (10-02 sweep rank 4) | | | |

E2 and E5: no new question found this pass beyond those already graded (E5: Hochman 2609.21481,
Bugeaud 10.60; Hochman–Shmerkin's "almost all points of `K` Gauss-normal?" is out of reach of E5 by
their own remark, "our methods do not seem to help with this problem").

## Rejected (one line each)

- **Calude–Staiger (ToCS 62 (2018)), "are there computable, Borel absolutely-normal, non-Liouville
  numbers?"**: verbatim not obtained (paywalled, CDMTCS report 448 dead link); answered by the
  repo's `BadNormal.exists_computable_absNormal_bad` (partial quotients in `{1,2}`, hence exponent 2),
  and folklore via Becher–Heiber–Slaman 2015 plus Queffélec–Ramaré; 4 citers (OpenAlex), none
  claims it.  Worth one sentence in the BadNormal note, not a campaign.
- **Bugeaud 10.23, computable reading**: Temur 2609.16362 (§3.1).
- **Hochman–Shmerkin 1302.5792 §1.3.3, "a point which is Gauss normal but not n-normal for any
  n"**: answered by Vandehey, *Absolutely abnormal and continued fraction normal numbers*, Bull.
  Aust. Math. Soc. (2016), arXiv:1512.00337.
- **BBFKW §5.4 (non-integer bases)**: answered for β-transformations by Huang–Li–Wang–Yuan
  2512.07686.
- **Becher–Heiber–Slaman question quoted in Scheerer's thesis (TU Graz), "Is there an absolutely
  normal number computable in polynomial time having a nearly optimal discrepancy of
  normality?"**: the repo's form is `LevinSparse.exists_absNormal_base2_fast` (ABSS barrier, 20%),
  already recorded.
- **Scheerer thesis, "a more explicit example [absolutely normal and CF-normal] is desirable"**:
  informal, no theorem target.
- **Fraser–Wheeler 2309.05851 (Exact(ψ) has positive Fourier dimension, "contains normal
  numbers")**: no stated question; a computable absolutely normal point of Exact(ψ) is a cheap
  derandomizer corollary, a remark at most.
- **Bugeaud–Kim 2510.02059, Bugeaud–Kaneko–Kim 2510.17177 (complexity vs irrationality
  exponent)**: subword-complexity questions, no engine.
- **Guo–Hussain–Li–Schleischitz 2608.26818 (products of exact sets)**: dimension theory, no engine.
- **Bugeaud 10.39 / 10.40 / 10.41 re-checked against the new engines**: forced runs give ternary,
  not dyadic, approximations (10.39); 10.40 is about one explicit series; 10.41 is thermodynamic
  formalism.  Unchanged.
- **"Normal in every base of `R`, `b`-badly approximable in every base of `S`"**: implies Hertling
  10.31 and is strictly harder; 10.31 is parked, so not proposed.
- **Liouville points of decimal missing-digit sets normal to base 2** (10-03c §2.4 remark):
  unstated, our own extension, low weight.

## Recommendation

**Row 1.**  It is the engine-native continuation of the 10.37 profile: the normality legs are the
existing `CantorLiouvilleAll` lemmas with a new run schedule, and the one new lemma is a
Borel–Cantelli exponent bound whose paper proof is short.  It meets a triple in Bugeaud's own
framing at every exponent `μ₀ > 4.17`, and the residual range `2 < μ₀ ≤ 4.17` is a clean,
literature-linked open node (rational counting near `K`).  Audit focus: the middle-range sum at
the point where the ball depth enters the next run, and the transfer of
`not_isNormal_of_three_dvd` to runs of bounded relative length.  Row 3 is a one-lap side job if a
computable uniform witness is wanted for a note; row 2 should not be run until someone has a
mechanism that refutes the `Bad₂` sibling.
