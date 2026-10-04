# Open-problem sweep, 2026-10-03c: Bugeaud ch. 10, the remainder 🔎

Fourth harvest, the follow-up to `OPEN-PROBLEMS-SWEEP-2026-10-03b.md`, which graded part of
Bugeaud, *Distribution modulo one and Diophantine approximation* (Cambridge Tracts 193, 2012),
Chapter 10 (61 problems).  Done since then, not re-graded here:
- **10.17, 10.18** proved (`ReciprocalNormal`);
- **10.37** proved (`CantorLiouville`);
- **10.23** closed by Maze rows;
- **10.49, 10.51, 10.53, 10.54, 10.56** answered in the literature.

This pass grades every remaining problem.  It re-checks the two "no engine" verdicts (10.36,
10.50) against `CantorLiouville`, `LevinSparse` and `SchedDerandomize`, and works out the cheap
variants of 10.37.

**Headline.**  **10.36 (strong form) has an elementary proof**, a potential-function
nested-interval argument (§1).  None of our measure engines is involved: the problem asks for an
every-`n` avoidance property on a Lebesgue-null set, not an almost-everywhere one.  It looks like
the answer the post-2017 potential-game technology (Broderick–Fishman–Simmons, Yavicoli) makes
easy.  No one appears to have written it down.

**Book text.**  Read in full from `staff.dc.uba.ar/becher/aa/Bugeaud2012.pdf` (fetched to the
session scratchpad; not adopted into `~/personal/papers`, as it is a book).  Problem statements
are on pp. 214–222.

**Negative inventory read first:**
- sweeps 10-02, 10-03 and 10-03b;
- `STATUS.md` achievements to 2026-10-03 and `DIRECTION.md`;
- the notes in `docs/notes/` (`bugeaud-10-37-cantor-liouville.md`, `deterministic-numbers.md`,
  `odd-bases-fast-base-2-discrepancy.md`, …);
- the `CantorLiouville.lean` declaration list (`secondMoment_le`, `block_sum`,
  `orderOf_two_zmod_three_pow`).

**Instrument limits:**
- OpenAlex lists only **200** forward citations of the book (`W1557463835`), a partial set.  It
  was filtered by keyword: badly / uniform / thick / rich / disjunct / Hertling / Cantor /
  Liouville / self-normal / beta / determin / translat / all bases / intersect.
- arXiv API phrase search is weak again: `abs:"b-badly approximable"` and
  `abs:"self-normal"` returned noise.
- Journal-only work was reached only through web search.  "Not found" means not found by these
  instruments.

## Ranked table (top 5)

| # | Problem | Statement (short) | Mechanism | Unproved premise | Conf. (audit + 2–4 laps) | Prior art | Weight |
|---|---|---|---|---|---|---|---|
| 1 | **10.36** | `∃ ξ, c > 0` with `‖bⁿξ‖ > b^{−c}` for **every** base `b ≥ 2` and every `n ≥ 0` (uniform in `b`) | Potential-function nested intervals.  Obstacles `B(a/bⁿ, b^{−n−C})` are charged **early** (at relative size `ε_b = 2K b^{−C}`), when at most 7 per base meet the current interval.  The `√`-potential then sums over `b` as `Σ b^{−C/2}`.  Gives `c = 24` | none (elementary); the proof needs an audit | paper 85%; Lean 70% (2–3 laps) | not found answered (§1.1) | medium: a listed Bugeaud problem, strong form; **uniform** version of Akhunzhanov / Thm 7.8 |
| 2 | **10.37 profile** (variant) | Computable `x ∈ K`, Liouville, with **`IsNormal b x ↔ 3 ∤ b`** for every `b ≥ 2` | `CantorLiouville`'s Cassels second moment with `2 → b`.  Primitive roots mod 9 are verbatim; other `b` coprime to 3 use a bounded-index subgroup `⊇ 1+3ᵗℤ`.  Failure for `3 ∣ b` comes from the runs: `bʲx` is near an integer for most `j ≤ N` | a coset version of `block_sum` (loses `t = v₃(b²−1)` digits); a family (all-`b`) `SchedDerandomize` | 65% (a.e. form 75%) | rides on the 10.37 search; Schmidt 1960 is the `μ_K` contrast (§2.1) | low–medium: sharpens our own 10.37 note into an exact normality profile |
| 3 | **10.31** (Hertling) | For each partition `R ⊔ S` of `{b ≥ 2}` closed under multiplicative dependence, some `x` is rich (disjunctive) in every base of `R` and in no base of `S` | `S` side: engine 1 with `S` in place of all bases (`Bad_s(24)` omits `0²⁴`).  `R` side: forcing blocks against the potential | a **block-forcing lemma**.  Forcing `|D|` digits costs a factor `(2K^{1/2})^{|D|}` in the worst case, and that must be beaten by spreading of the `s`-adic obstacles across `r`-adic cylinders (§3.3) | 25% | `R = ∅` is Bugeaud, Rev. Mat. Iberoam. 28 (2012) Thm 2.1; `|S| = 1` class is Hertling / Schmidt; general partition not found | medium: the richness analogue of Schmidt's Thm 6.3 |
| 4 | **10.60** | For `μ_K`-a.e. `β ∈ K`, `1+β` is self-normal | none: base-varying β-expansions of 1; Schmeling's a.e. proof is Lebesgue-only | the whole parametric-family transversality on a fractal | 8% | not found | medium |
| 5 | **10.39** | Points of `K` with prescribed `v₂` | none: dyadic approximation on `K` is ×2×3-flavoured | the whole thing | 5% | active literature (Allen–Chow–Yu, Selecta 2022; Baker arXiv:2203.12477; arXiv:2606.25305), partial | medium |

**Recommendation: run 10.36 (§1).**
- It is elementary and fully unconditional.
- It answers a listed Bugeaud problem in its strong form.
- It installs a reusable engine, "countably many base-indexed obstacle families with summable
  potential".  That engine is the `S` half of 10.31 for free.

## Graded this pass, everything not in the top 5

| Problem | Verdict |
|---|---|
| 10.1–10.8, 10.10–10.13 | Pisot / Hardy / `(3/2)ⁿ` / `‖eⁿ‖` / p-adic Littlewood: no engine.  Ralf Stephan (+Claude) is working this Mahler/Pisot corner (`rwst/Confinement-Certificates`, `Ceiling-Orbits`). |
| 10.9 | Mahler Z-numbers: no engine; Stephan's confinement certificates touch it. |
| 10.14–10.16 | Korobov-optimal discrepancy: headline-hard (as 10-03b).  `LevinSparse` *uses* Levin's rate; it does not improve it. |
| 10.15 | "Simple construction": informal, not a theorem target (computable constructions exist: Becher–Figueira, BHS). |
| 10.19 | `∩_b D_b` contains an irrational (`D_b` = completely deterministic, Rauzy; Manai arXiv:2609.24665 Thm 1.2 confirms the `∩_b D_b` reformulation and leaves it open).  The simultaneous small-orbit requirement for every base is ×2×3-type (gcd(2ᵐ−1, 3ᵐ−1) ≤ e^{εm}).  3%. |
| 10.20–10.22, 10.24–10.29 | Furstenberg-type (as 10-03b).  10.22 (density-zero nonzero digits in two independent bases) is the cleanest ×2×3 instance. |
| 10.30 | Colebrook–Kemperman prescribed `V(ξ, sₙ)`: contains 10.22 (`Vₙ = {δ₀}`), so it is ×2×3-hard. |
| 10.32 | Very likely answered by Adamczewski–Bell, *An analogue of Cobham's theorem for fractals*, Trans. AMS 363 (2011) (a number automatic in two independent bases is rational).  Not verified against Bugeaud's "slightly modified form"; ~80%. |
| 10.33, 10.34, 10.42–10.48, 10.57, 10.58 | Transcendence / algebraic expansions: no engine. |
| 10.35, 10.40 | Exponents `v_b` / irrationality exponent of lacunary series: no engine. |
| 10.38 | Algebraic approximation on `K`: no engine.  Zhang–Liu–Shi (Bull. Aust. MS 2022) studies the dimension, which is not this question. |
| 10.41 | Dimension of BAD with prescribed digit frequencies: a thermodynamic-formalism computation (Fan–Liao–Ma–Wang style), no engine. |
| 10.50 | Re-checked: still no engine.  CF-normality almost everywhere for a dimension-0, low-complexity measure is not a Fourier/second-moment statement, and none of `CantorLiouville`/`LevinSparse`/`SchedDerandomize` addresses Gauss-map statistics. |
| 10.52 | Bugeaud's Thm 8.9 forbids both expansions being `p(n) ≤ n+k`-simple; Kempner-type `Σ 2^{−2ʲ}` (badly approximable, low complexity) shows the boundary.  The intended meaning of "simple" is unclear; no engine. |
| 10.55, 10.59 | Berend–Boshernitzan; β-expansion `N(β)` vs `D(β)`: no engine. |
| 10.61 | Mendès France `C(α)`: partial results by Stephan + Claude (vibemathed `bugeaud-problem-10-61`, `rwst/Pisot-Cantor-61`: criteria + instances `2+√5`, `2+√3`).  Our measure engines are refused by the Erdős–Pisot obstruction (`ν̂(hαⁿ) ↛ 0`). |

## 1. Bugeaud 10.36: a number uniformly badly approximable to every base (paper 85%)

### 1.1 Statement, source, freshness

Verbatim (p. 219): "**Problem 10.36.** There exist a real number ξ and a positive real number c
such that `||bⁿξ|| > b^{−c}` for every base b ≥ 2 and every integer n ≥ 0 (resp., every integer n
sufficiently large in terms of b)."  The book's best result is Theorem 7.8 (after Akhunzhanov):
`||bⁿξ|| > b^{−1100 b log 3b}`, a constant that decays super-exponentially in `b`.  Its proof
plays Schmidt's `(α, β)`-game, whose countable-intersection property cannot hold the constant
uniform.

**Prior-art search done:**
1. OpenAlex citers of the book (200 listed), keyword-filtered: Bugeaud–Liao and Wang–Wu on
   uniform approximation for β-expansions, "Random fractals and their intersection with winning
   sets" (2021), "Dirichlet uniformly well-approximated numbers", "Rotational beta expansions and
   Schmidt games" (2025).  None addresses a uniform-in-`b` constant.
2. `papers followups 1910.10057` (Yavicoli, *Patterns in thick compact sets*, 25 citers): all are
   about patterns or thickness, none about bases.  Yavicoli–Yu arXiv:2503.09528 (missing digits in
   several bases) treats finitely many bases for integers.
3. Broderick–Fishman–Simmons arXiv:1703.09015 (the potential game; Acta Arith. 188 (2019)), TeX
   grepped for base / digit / Bugeaud: CF and Cantor-set applications only.
   Broderick–Fishman–Simmons arXiv:1508.03734 answers a *different* Bugeaud question (decaying
   BAD).
4. Yavicoli's survey arXiv:2212.02023, TeX grepped: no base-`b` application.
5. Bugeaud, Rev. Mat. Iberoam. 28 (2012) 931–946 (*On the expansions of a real number to several
   integer bases*): Thm 2.1 has the `b`-dependent constant `b^{−c b log b}`.
6. Five web searches (uniform constant / every base / potential game / Akhunzhanov / "independent
   of b"): nothing.

**Freshness about 55%.**  The proof is a page long once the potential idea is in hand.  An expert
in potential games could regard it as an exercise, but none was found written.

### 1.2 Mechanism (the proof)

Fix `K = 64`, potential exponent `c = 1/2`, block constant `C = 24`.  Obstacles:
`O_{b,n,a} = [a/bⁿ − r, a/bⁿ + r]` with `r = b^{−n−C}`.  Avoiding every obstacle is exactly
`‖bⁿξ‖ > b^{−C}` for all `b`, `n`.

- **Nested intervals.**  `J₀ = [1/4, 3/4]`, `ℓ_k = |J_k| = K^{−k}/2`, and `J_{k+1}` is one of the
  `K` equal closed children of `J_k`.
- **Early charging.**  Put `ε_b = 2K b^{−C}`.  Obstacle `O` of base `b` is *assigned* to the stage
  `k` with `r ∈ (ε_b ℓ_{k+1}, ε_b ℓ_k]`.
  - Every obstacle is assigned at some stage `≥ 0`: `r > ε_b ℓ₀` would need `b^{−n} > 64`.
  - **Count:** at most 7 obstacles of one base are assigned to a stage and meet a given interval
    of that stage.  A ratio-`K` window holds `≤ ⌊log K/log b⌋ + 1 ≤ 7` values of `n`.  For each
    `n`, the spacing `b^{−n} = r b^C > 2ℓ` exceeds the length `ℓ + 2r` of the window of centres,
    so at most one centre meets.
- **Potential.**  `Φ_k = Σ_{O assigned ≤ k, O ∩ J_k ≠ ∅} (r_O/ℓ_k)^{1/2}`, as an `ℝ≥0∞` tsum.
  The invariant is `Φ_k < θ := (2K)^{−1/2}`.  It forces every carried obstacle to have
  `r_O < ℓ_k/(2K)`, half a child.
- **Step.**  A carried obstacle meets at most 2 children and contributes `K^{1/2}` times as much
  to each one.  So the children's old potentials sum to `≤ 2K^{1/2}Φ_k`, and the cheapest child
  has old part `≤ 2K^{−1/2}Φ_k = Φ_k/4`.  New obstacles assigned at `k+1` add at most
  `A = 7 Σ_b ε_b^{1/2} = 7(2K)^{1/2} Σ_{b≥2} b^{−C/2}`.  Hence `Φ_{k+1} ≤ Φ_k/4 + A < θ` once
  `A < 3θ/4`.  Numerically `A ≈ 79.2 · 2^{−12}·1.0003 ≈ 0.0194` against `3θ/4 ≈ 0.066`.
- **Limit.**  `ξ = ⋂ J_k`.  Take any obstacle `O` and pick `k` with `ℓ_k < r_O θ^{−2}`.  Then `O`
  cannot meet `J_k`, since that would give `Φ_k ≥ (r_O/ℓ_k)^{1/2} > θ`.  So `ξ ∉ O`.

The same argument shows `{ξ}` can be chosen among `≥ K/2` children at each step, so the set of
solutions is uncountable, with positive Hausdorff dimension.  This is the BFS / Yavicoli route,
cross-check below.

**Cross-route (paper only).**  The same count shows each `Bad_b(C)` is
`(α_b, β, ½, ρ)`-potential-winning with `α_b^{1/2} ≍ b^{−C/2}`.  The countable-intersection
property gives `α^{1/2} = Σ α_b^{1/2}`.  Then Yavicoli 1910.10057, Thm "teoexplicito" (the
explicit BFS Thm 5.5), gives `dim_H(⋂_b Bad_b(C) ∩ B) > 0` once
`α^{1/2} ≤ (1 − β^{1/2})/720²`, which holds for `C ≈ 50`.

### 1.3 Difficulty check

- **Proved implications:** all of it, on paper; no cited input.
- **Unproved premise:** none mathematical.  The risk is an error in the counting.  The audit
  should recheck the per-base count (closed vs half-open intervals, the `b = 2, 3` windows) and
  the constants.
- **Known-false siblings:**
  - *`c ≤ 1`.*  The statement is false: Dirichlet gives `‖qξ‖ < 1/q` for infinitely many `q`
    (and `ξ` rational fails at `n = 1`, `b = q`).  The mechanism refuses it, since the potential
    sum `Σ_b b^{−Cc'}` needs `C > 1/c' > 1`.
  - *All integers `q` in place of the powers `bⁿ`* (`‖qξ‖ > q^{−1−c}`).  This is true
    (irrationality exponent `< 2 + c`), and the mechanism proves it too: one level per `q`,
    `Σ q^{−c/2}`.  A sanity check, not a refutation.
  - *Normal to some base:* every solution is normal to **no** base (the block `0^C` never occurs),
    consistent with Bugeaud's Cor. 7.9.  The mechanism makes no normality claim.
- **Why the old method stalled:** a classical Schmidt-game argument charges each obstacle at its
  own scale, where infinitely many bases can stack up near one point (the 10-03b worry).  Early
  charging spreads base `b`'s obstacles over the `log_K b^C` coarser stages, where they are sparse.

### 1.4 Draft Lean statement (to freeze)

**Frozen 2026-10-03** as `NormalNumbers.UniformBad` (`src/NormalNumbers/UniformBad.lean`, branch `proof/avoid`): headline `bugeaud_10_36`, engine `exists_avoid_of_stagePotential` (proved from `potential_step`), guards, prior-art note in the module docstring (Falconer–Yavicoli 2022 thickness route).

```lean
import Mathlib

namespace NormalNumbers.UniformBad

/-- Distance to the nearest integer. -/
noncomputable def dnear (x : ℝ) : ℝ := |x - round x|

/-- **Bugeaud 2012, Problem 10.36 (strong form).** -/
theorem exists_uniformBad_allBases :
    ∃ ξ : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ,
      (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * ξ) := by sorry

/-- Explicit constant `c = 24`, with `ξ ∈ [1/4, 3/4]`. -/
theorem exists_uniformBad_allBases_24 :
    ∃ ξ ∈ Set.Icc (1 / 4 : ℝ) (3 / 4), ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ,
      (b : ℝ) ^ (-(24 : ℝ)) < dnear ((b : ℝ) ^ n * ξ) := by sorry

/-- The engine: nested `K`-adic intervals avoiding a countable family of closed intervals whose
early-charged `√`-potential per stage is below `A`.  (Exact hypothesis shape fixed at freeze.) -/
theorem exists_avoid_of_stagePotential : True := by trivial  -- placeholder, see §1.2

/-- Guard: false for `c ≤ 1` (Dirichlet). -/
theorem not_uniformBad_of_le_one {c : ℝ} (hc : c ≤ 1) :
    ¬ ∃ ξ : ℝ, ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ, (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * ξ) := by sorry

/-- Content locator: a uniform witness is normal to no base (the block `0^⌈c⌉` is absent). -/
theorem not_isNormal_of_uniformBad {ξ c : ℝ} (h : ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ,
      (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * ξ)) (b : ℕ) (hb : 2 ≤ b) :
    ¬ NormalNumbers.IsNormal b ξ := by sorry

end NormalNumbers.UniformBad
```

`exists_avoid_of_stagePotential` is deliberately left as a placeholder.  The engine's
hypothesis shape (index type, stage map, per-stage count) should be fixed by the auditor, so that
§3 can reuse it with `S` in place of all bases.

## 2. The 10.37 normality profile: `IsNormal b x ↔ 3 ∤ b` (65%)

### 2.1 Statement and freshness

Not a Bugeaud problem by itself.  It is the strongest cheap corollary of our 10.37 machinery:
**a computable Liouville number in the middle-third Cantor set, normal to exactly the bases
coprime to 3.**  The contrast is with Schmidt (1960): `μ_K`-almost every point is normal to every
base that is not a power of 3, including 6, 12, 15, ….  Adding the Liouville runs *provably*
destroys normality in every base divisible by 3.  Its freshness rides on the 10.37 note's
prior-art search (about 55%).

### 2.2 Mechanism

1. **`b ≡ 2, 5 (mod 9)`, primitive roots mod `3ᴹ`.**  `secondMoment_le` with `2ᵏ → bᵏ`, verbatim.
   `orderOf_two_zmod_three_pow` generalizes to "`b` generates `(ℤ/9)ˣ` ⇒ `b` generates `(ℤ/3ᴹ)ˣ`".
2. **Other `b` coprime to 3.**  `⟨b²⟩ = 1 + 3ᵗℤ/3ᴹ` with `t = v₃(b² − 1)`, a cyclic 3-adic
   group.  So the orbit of `c·bʲ` covers a coset of a subgroup of index `≤ 2·3^{t−1}`, and ternary
   digits above position `t + v₃(c)` stay uniform.  `block_sum` loses `t` places, a constant.
   `bad_count` is untouched.
3. **`3 ∣ b`: failure for every `ω`.**  On run `k`, `x = p/3^{a_k} + θ` with
   `0 ≤ θ < 3^{−(k+2)a_k}`.  For `b = 3^a m` and `a_k/a ≤ j ≤ (k+2)a_k/log₃b − s`, the number
   `bʲx` lies within `3^{−s}` of an integer.  That is a fraction `→ 1` of `j ≤ N_k`, so digit 0 has
   upper frequency 1 in base `b`.
4. **Computable.**  `SchedDerandomize` is base-2 specific.  The all-bases form needs a family
   version (the `FamilyDerandomizeVar` pattern applied to the slow schedule).  The a.e. form needs
   only the countable intersection.

### 2.3 Difficulty check

- **Proved implications:** steps 1 and 3 on paper (step 3 is elementary, about 100%), plus
  everything in `CantorLiouville` past the arithmetic lemma.
- **Unproved premise:** the coset version of `block_sum` (step 2, 80%) and the family-schedule
  derandomizer (Lean bookkeeping, 75%).
- **Known-false sibling:** base 6 for these points is false, and the mechanism refuses it.  In
  `h·6ʲ = 3ʲ·(h2ʲ)` the factor `3ʲ` zeroes the low ternary digits, and the free places the Riesz
  product needs lie inside the runs for most `j`.

### 2.4 Draft Lean statement

```lean
namespace NormalNumbers.CantorLiouville

/-- Base-`b` normality of the Liouville–Cantor points for `b` coprime to 3 (a.e. in the coins). -/
theorem ae_isNormal_of_coprime_three {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (cantorLiouvilleReal ω) := by sorry

/-- Guard (every `ω`): never normal to a base divisible by 3. -/
theorem not_isNormal_of_three_dvd {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) (ω : ℕ → Bool) :
    ¬ IsNormal b (cantorLiouvilleReal ω) := by sorry

/-- **Normality profile.** -/
theorem exists_computable_liouville_mem_cantorSet_normalProfile :
    ∃ e : ℕ → Bool, Computable e ∧ cantorLiouvilleReal e ∈ cantorSet ∧
      Liouville (cantorLiouvilleReal e) ∧
      ∀ b : ℕ, 2 ≤ b → (IsNormal b (cantorLiouvilleReal e) ↔ ¬ 3 ∣ b) := by sorry

end NormalNumbers.CantorLiouville
```

**Other Cantor sets and base pairs.**  The same proof covers missing-digit sets in base `r` (digit
set `D`, `|D| ≥ 2`, `D` not in a single residue class mod any `d > 1` dividing `r`), with
normality to every `b` coprime to `r`.  For composite `r`, `(ℤ/rᴹ)ˣ` is not cyclic, but every
bounded-index subgroup still contains a congruence subgroup `1 + rᵗℤ`.  This is 55% and adds
generality without a new idea, so record it as a remark and do not run it as a campaign.  Pairs
`(r, b)` that share a prime but are independent (`r = 10`, `b = 2`) are **not** covered: the runs
make `bʲx` close to `p·b^{j}/r^{a_k}`, which is a Korobov-type piece, not a near-integer.  That case
is open for this construction.

## 3. Bugeaud 10.31 (Hertling): rich in `R`, rich in no base of `S` (25%)

### 3.1 Statement and freshness

Verbatim: "Let `R ∪ S` be a partition of the set of integers greater than or equal to 2 into two
classes such that any two multiplicatively dependent integers fall in the same class.  There are
real numbers which are rich to every base from `R` but not rich to every base from `S`."  Here
"not rich to every base from `S`" means rich to no base of `S`.

**Prior-art search done:**
- The two-class case is classical.  `S = {3ᵏ}` follows from Schmidt / Cassels: `μ_K`-a.e.
  points are normal to every non-power of 3.  Hertling's `Σ r^{−j!−j}` (J.UCS 1996) settles a
  single class of `S`.
- `R = ∅` is Bugeaud, Rev. Mat. Iberoam. 28 (2012), Thm 2.1, via Schmidt games.
- Web search ("Hertling" + rich / disjunctive + "every base from R"): only the RMI paper, Becher's
  and Slaman's normality papers, and overviews.
- arXiv `abs:disjunctive AND abs:"multiplicatively independent"`: nothing.
- **Freshness about 60%; the general partition looks open.**

### 3.2 Mechanism

- **`S` side.**  Engine 1 with the obstacle family restricted to `b ∈ S` gives
  `x ∈ ⋂_{s∈S} Bad_s(24)`.  Then `0²⁴` never occurs in base `s`, so `x` is not rich there.
- **`R` side.**  Enumerate the pairs `(r, D)` with `r ∈ R` and `D` a block.  At stage `k`, choose
  `t` free digits `u` and then force `D`, making the next interval `[w u D]_r`.

### 3.3 Difficulty check

- **Unproved premise: the block-forcing lemma.**  A forced step has no choice, so its potential
  can grow by the factor `2K^{1/2}`, and `|D|` forced steps by `(2K^{1/2})^{|D|}`.  Meanwhile the
  potential floor `A > 0` is fixed by the active `S` bases, so the invariant cannot simply absorb
  long blocks.
- **What should rescue it:** averaging over the `r^t` placements `u`.  An obstacle of radius
  `ρ ≤ spacing` meets `≤ 2` candidates.  The average old potential then carries the factor
  `2 r^{−t(1−c)} r^{|D|c}`, which is small for `t ≳ |D|`.
- **What breaks the naive version:** obstacles assigned at the intermediate `t` levels.  Their
  total length grows linearly in `t`.  They must be handled level by level, with the choice of
  `u` made by conditional expectation over the *post-forcing* potential (a derandomization of a
  random `u`).  That step is not checked.
- **Known-false siblings:**
  - a partition that splits a dependence class is false (`isDisjunctive_pow_iff`, already in
    `Disjunctive.lean`);
  - `S` containing every base and `R = ∅` is true (engine 1);
  - the mechanism must not force richness in a base of `S`, and it does not: the forcing
    enumerates `R` only.
- **Lean cost:** engine 1 plus the forcing lemma, 4–6 laps.

### 3.3a Audit, 2026-10-03 (branch `audit/hertling`)

Verdict: not run, lap estimate 12% (truth about 85%).  The record is `src/NormalNumbers/Hertling.lean`.
- **Proved there**: the reduction `richExactly_of_blockForcing` (10.31 follows from the single
  node `blockForcing`).  Also the guards `not_exists_richExactly_two` and
  `depClosed_of_blockForcing`, the corners `richExactly_empty` / `richExactly_univ`, and the
  wired edge `richExactly_singleClass_of_hertling`.
- **Crux**: inside a forced block of length `L` there are about `L log_s r − 24` fatal base-`s`
  levels.  The union bound dies once `L ≳ s^{24}`, and the joint bound needs a Schmidt-lemma
  (`×r ×s`) equidistribution of the placements' low digits at every scale, uniformly in `s`.
- **Becher–Slaman Thm 5 does not cover it**: its base-`s` constraint is active only during the
  stages devoted to `s` (digit `s − 1` omitted).  `exists_rich_and_not_normal_everywhere`
  shows not-normal does not imply not-rich.

### 3.4 Draft Lean statement

```lean
namespace NormalNumbers.HertlingRich

/-- Multiplicative dependence of two bases. -/
def MulDep (a b : ℕ) : Prop := ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ a ^ m = b ^ n

/-- **Bugeaud 2012, Problem 10.31 (Hertling).** -/
theorem exists_rich_exactly (R : Set ℕ)
    (hR : ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → MulDep a b → (a ∈ R ↔ b ∈ R)) :
    ∃ x : ℝ, (∀ b : ℕ, 2 ≤ b → (IsDisjunctive b x ↔ b ∈ R)) := by sorry

/-- The `S` half, from engine 1: no richness in any base of a given set. -/
theorem exists_not_rich_on (S : Set ℕ) :
    ∃ x : ℝ, Irrational x ∧ ∀ s ∈ S, 2 ≤ s → ¬ IsDisjunctive s x := by sorry

/-- Guard: a partition splitting a dependence class admits no such `x`. -/
theorem not_exists_rich_exactly_of_split {R : Set ℕ} {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : MulDep a b) (haR : a ∈ R) (hbR : b ∉ R) :
    ¬ ∃ x : ℝ, ∀ c : ℕ, 2 ≤ c → (IsDisjunctive c x ↔ c ∈ R) := by sorry

end NormalNumbers.HertlingRich
```

## 4–5. 10.60 and 10.39 (no engine)

- **10.60.**  The base varies with the point, so the relevant statistic is the β-transformation
  orbit of 1.  Schmeling's a.e. theorem uses Lebesgue-parameter transversality.  A fractal
  parameter measure would need a Schnellmann-type typicality theorem for `μ_K`, which nothing
  here supplies.  8%.
- **10.39.**  A prescribed `v₂` on `K` needs `K` to come within `2^{−n(1+v)}` of dyadics
  infinitely often.  That is exactly the active, ×2×3-flavoured dyadic-approximation literature:
  Allen–Chow–Yu, Selecta 2022; Baker arXiv:2203.12477; arXiv:2606.25305.  Our second-moment
  engines see only `log`-scale equidistribution.  5%.

## Recommendation

**Audit and run 10.36 (§1).**
- Audit focus: the per-base count lemma, and the potential step with closed children.
- Plan 2–3 laps.  The first lap builds the generic engine `exists_avoid_of_stagePotential` over
  an abstract countable obstacle family with a stage map and per-stage count.  The second
  instantiates it at `b^{−n−24}` and proves the two guards.
- Write the note in `docs/notes/` per the outward-note rule, citing BFS / Yavicoli as the method's
  lineage.
- 10.31 is the natural follow-on, since engine 1 is its `S` half.  It needs the block-forcing
  lemma (§3.3) to be audited on paper first.
- The 10.37 profile (§2) is a one-paragraph upgrade of the existing 10.37 note.  It is worth a
  lap only if the family-schedule derandomizer is wanted for other reasons.
