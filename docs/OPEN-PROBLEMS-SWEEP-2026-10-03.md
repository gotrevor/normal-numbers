# Open-problem sweep, 2026-10-03 🔎

Second harvest of explicitly stated open problems, after the 2026-10-02 sweep
(`docs/OPEN-PROBLEMS-SWEEP-2026-10-02.md`) whose ranks 1, 2 and 3 have since been answered here
(Erdős #257 for `k·S` and for every infinite prime set; Manai's explicit `x` with `x²` non-normal;
Manai's `Ω_k`, computable points and `dim_H = 1`).  Direction only: per `lean-is-the-record`, the
top three candidates carry draft Lean statements below, to be frozen in a worktree.

**Negative inventory read first:** the 2026-10-02 sweep, `DIRECTION.md`, `HEADLINES.md` (ranked
bets, "Don't fund" list), `STATUS.md` (2026-10-02/03 entries), every `Maze.lean` register row
(143 rows, last two: "site factorization via log-power BV", "Erdős #257 gap sets via an
S-restricted moment cap alone"), the five `docs/*AUDIT*` headers, and the row-5 barriers in
`ExplicitSquareNonNormal.lean` (`not_polyDecay_sparse_of_densityZero`,
`not_logDecay_sparse_of_littleLog`, open `inv_logDecay_squares`).  Nothing below re-proposes a
closed hall.

**Sources this pass.**
- `papers followups` on 2508.09319, 2506.15422 (3 citing papers each, all Manai's own),
  2401.01241 (30 citing papers, Fourier decay of fractal measures), 2512.01739 (2: Hughes
  2609.28526, Lau 2604.15042), 2506.12929 (4: Manai 2609.24665, Manai 2606.08325,
  Farhangi–Mance 2512.01239, Downarowicz–Weiss 2308.04540).
- Bergelson–Downarowicz 2506.12929v1 read in TeX (`Final2.tex`), §7 and "Some natural open
  problems" in full; the arXiv API shows v1 (2025-06-15) is still the only version.
- Erdős problems: every page tagged *irrationality* or *base representations* and its forum
  thread, fetched 2026-10-03; `teorth/erdosproblems` YAML; a `google-deepmind/formal-conjectures`
  clone at `df3f12d` plus `gh pr list` for open PRs; `ftargets lean-status`.
- arXiv harvest (TeX of the followups above and of math.NT/DS/CA submissions 2026-08-15 to
  2026-10-03): see §"arXiv harvest".

**Instrument limits.**  Erdős-side: no literature search beyond the site, forum, FC files and
open FC PRs.  B-D side: forward citations are only what `papers followups` indexes (4 papers,
all read or grepped for "deterministic"/"reciprocal"/"Bergelson"); one web search found nothing
answering items 2 or 4.  Journal versions of 2506.12929, if any, were not reached.

## Ranked table

| # | Source | Statement (short) | Mechanism | Unproved premise | Conf. (2 h lap + audit) | Weight |
|---|---|---|---|---|---|---|
| 1 | Bergelson–Downarowicz 2506.12929 §7 "Some natural open problems", item 2 | Is the reciprocal of a nonzero deterministic number always deterministic?  **No.** | Hua's identity `1/(1/s − 1/(s+1)) = s² + s` inside the additive group `D(2)`, fed by B-D's own Cor. `x^2` (or Manai 2606.08325 Cor. `quadratic-log`) | none new; cited inputs are B-D Cor. `rrr`(2) (subgroup) and Cor. `x^2` | 90% | medium: answers a stated question of two well-known ergodic theorists; the proof is 5 lines |
| 2 | Same list, item 4 (i)-(iii) | Can every nonzero real be a product / ratio / product of reciprocals of two deterministic numbers?  **No; the representable set is Lebesgue-null, `dim_H = 0`.** | `D(r)` has packing dimension 0 (B-D Def. `detb`: subexponential ε-complexity), so `D × D` is covered at every scale `r^{-N}` by `r^{o(N)}` boxes; the product map is locally Lipschitz | none new; cited input is B-D Thm. `detdet` (only to say the Lean definition is theirs) | 40% (the word-counting lemma is the work) | medium, same audience |
| 3 | Manai 2606.08325v1 §1.1 "Overview of related literature" | "an intrinsic algorithm constructing a number `x` for which `P(x)` is normal and `Q(x)` is non-normal - provided that the polynomials `P` and `Q` are linearly independent" | Generalize `ExplicitOmegaK` from `Q = Xᵏ` to any `Q ∈ ℤ[X]`: `x = Q⁻¹(a + c·y)` on a monotone branch, `y` quarter-Cantor; `G = P ∘ Q⁻¹` has `G'' ∝ W_P(x)/Q'(x)³` with `W_P = P''Q' − P'Q''`, so the cylinder cut and family derandomizer run with `W_P` in place of `qPoly` | none new (cited `BakerBanajiUniformQuarterCantor`, already refereed 93%); the work is re-running `deriv2_Gk_lower` / `approx_Gfam` for a general branch inverse | 30% (multi-lap 75%) | medium: Manai only, but the answer is *sharp* (all `P ∉ span_ℚ(1, Q)` at once, and Wall kills the rest) and engine-native |
| 4 | Erdős #257 (site edited 2026-04-15; forum through 2026-09) | `A` = squarefree integers (more generally `k`-free, semiprimes): is `Σ_{n∈A} 1/(2ⁿ−1) = Σ 2^{ω(m)}/2ᵐ` irrational? | Rerun the Campbell / CaptainSude / joint-Lambert construction with `f_A(m) = 2^{ω(m)}` in place of `τ(m)` | a power-of-two encoding lemma replacing `EvenEncoding` (`{2a/bˢ}` degenerates at `b = 2` when `2a` is a power of 2) | 15% (paper 60%) | high: a divergent, non-prime #257 support; Kovač expects some `A` to fail at base 2, so structure matters |
| 5 | B-D item 3, and item 5(i)/(iii) at `z = 1` | Is there a normal `x` with `1/x` deterministic? | Hua dichotomy from Manai's deterministic `X` with `X²` normal: either `1/X` or `1/(X+1)` is non-deterministic, or `w = 1/(X(X+1))` answers item 3 | which branch holds; otherwise the row-5 lemma `inv_logDecay_squares` | 15% | medium |
| 6 | 2026-10-02 sweep leftovers: rank 4 (Pulari 2602.01199, non-invertible finite-state relabelings) and rank 6 (Becher–Lew Deveali 2607.06773, odd-base non-normality in sparse Cantor sets) | as in that sweep | as in that sweep | as in that sweep | 15% each | low-medium |
| 7 | Hughes 2609.28526v1 §6 "Remarks" | "An intermediate target with content is `sup_{𝔥≤(log ω)^β} abs(·) ≪ (log ω)^{1−γ}` for all windows" (effective log two-point Chowla, growing shifts) | the repo's two-point log-Elliott (`ElliottTwoPointLog`) | an effective every-window rate, which the repo is not known to have (its constants were not checked this pass) | 8% | medium (analytic NT) |
| 8 | Hochman 2609.21481v1 §1, Problems 1-3 | ×a-invariant zero-entropy sets: do they contain base-`b` disjunctive points?  Implicit: an *explicit* `x` of minimal complexity in base `a` and maximal in every independent `b` | joint multi-base occurrence; BLD sparse Cantor algorithm | no mechanism for a fixed Sturmian orbit | 8% | medium-high (Hochman) |

Items 2 and 4 of B-D's list, together with item 5(ii) (trivially No, see §1.4) and a reduction of
item 7, would make one outward note on the Bergelson–Downarowicz questions.  Items 1
and 6 were answered by Manai 2609.24665 (`thm:2`) and Dayan–Ganguly–Weiss / Manai `thm:1`.

## arXiv harvest (2026-08-15 to 2026-10-03, plus the followups above)

Read in TeX, newest versions.  Questions not promoted to the table:

- **Manai 2606.08325v1** Conjecture `con:summability` and the critical window (2026-10-02 sweep
  row 12): probabilistic with non-constant `p_n`; BB covers constant weights only.  Its §1 also
  repeats B-D's multiplicative-preserver question, which Dayan–Ganguly–Weiss already answered.
  Its Cor. `cor:quadratic-log` is used above as a second source for "square of a deterministic
  number need not be deterministic".
- **Manai 2609.24665v1**: no stated open problem.  ⚠️ Thm 1.3 (a locally `C²` preserver of
  `𝒩_b` is rational-affine plus a deterministic translation) runs on the same Baker–Banaji input
  as `ExplicitOmegaK`; the unstated `C²`-versus-`C^{1,1}` gap is not a target.
- **Manai 2508.09319v4** (2026-09-22): Ω_k text unchanged (answered here); the polynomial-time
  LIL-normal / transcendentally-normal algorithm question is the 2026-10-02 row 9 (10%); "is
  `p(x)` normal for any `t`-normal `x` and algebraic `p`" quantifies over all `t`-normal `x`, out
  of reach.
- **Banaji–Yu 2503.07508v2 §5, 2606.09743v1 §8**: Conj. 5.14 (polynomial decay for analytic
  non-degenerate maps of self-similar measures in `ℝᵏ`), Q. 5.15 (Salem images), relaxing
  analyticity to non-flat `C^∞`.  Upstream of the repo's cited input; a `C^∞` relaxation would
  widen `BakerBanajiAnalytic`, nothing more.
- **Baker–Banaji 2602.05593v1**: every question posed is answered negatively in the paper.
  Useful negative: a Rajchman self-similar measure (Liouville `t`) can have no shrinking-target
  rate, so a quantitative normality statement cannot come from Rajchman alone.
- **Charamaras–Richter Conj. 1.10** (via 2608.16108v3): Cesàro `k`-point equidistribution of
  `(Ω(n), …, Ω(n+k−1))`; the repo's two-point engine is logarithmic.  C1-C3 territory, not funded.
- **Lau 2604.15042v2**, **Leclerc–Ren 2609.17743v1**, **Seo–Steiner 2610.00856v1** (Arnoux–Rauzy
  transcendence, Subspace Theorem), **Nguyen 2608.20191v1**: no bearing.
- **Answered elsewhere:** Temur 2609.16362 answers Bugeaud Problem 10.53 with a computable
  number; Lai–Shi–Xie 2609.22772 answer their own questions with deterministic Salem Moran sets
  (a possible future input: Fourier decay on deterministic digit sets gives a.e.-normal points
  there).  Bugeaud's *Distribution modulo one* Ch. 10 problem list is a seam for a later sweep.

Harvest limits: abstract-level API queries (an `abs:"normal number"` query in the window returned
only Manai 2609.24665); priority papers were grepped for problem environments and read at
intro and conclusion; `papers followups` lags (September papers show 0 citers).

## 1. Bergelson–Downarowicz item 2: reciprocals of deterministic numbers (90%)

### 1.1 Source and freshness

Bergelson–Downarowicz, *On preservation of normality and determinism under arithmetic
operations*, arXiv:2506.12929v1 (2025-06-15, 67 pp., still the only arXiv version on
2026-10-03), end of §7, verbatim:

> 2. Is the reciprocal of a nonzero deterministic number always deterministic?

`papers followups 2506.12929` lists four citing papers.  Manai 2609.24665 and 2606.08325 cite it
only for the multiplicative-preserver question (item 6); Farhangi–Mance 2512.01239 cites it once
in passing; Downarowicz–Weiss 2308.04540 predates it.  None addresses item 2 (each grepped for
"deterministic", "reciprocal", "Bergelson").

### 1.2 The answer

Write `D = D(2)` for the base-2 deterministic numbers (B-D Def. `detn`: every measure
quasi-generated by the binary expansion has entropy 0).  B-D prove:

- Cor. `rrr`(2): `D` is a subgroup of `(ℝ, +)`.  Rationals are in `D` (eventually periodic
  digits), so `1 ∈ D`.
- Cor. `x^2` (from Thm. `cex` and Prop. `1/y`): there is `s ∈ D` with `s² ∉ D`.  Independently,
  Manai 2606.08325 Cor. `cor:quadratic-log` gives one almost surely: with `p_n ≍ √(log n / n)`
  the random `X` has digit-1 frequency 0, hence `X ∈ D`, while `X²` is absolutely normal.

**Theorem (new, as far as the instruments above see).**  Some nonzero deterministic number has a
non-deterministic reciprocal.  Explicitly, if `s ∈ D` and `s² ∉ D` then one of `s`, `s + 1`,
`u = 1/(s(s+1))` is a nonzero element of `D` whose reciprocal is not in `D`.

*Proof.*  `s ≠ 0, −1`, since `0² = 0` and `(−1)² = 1` lie in `D`.  Suppose `1/s ∈ D` and
`1/(s+1) ∈ D`.  Then `u = 1/s − 1/(s+1) = 1/(s(s+1)) ∈ D` (subgroup), `u ≠ 0`, and
`1/u = s² + s`.  If also `1/u ∈ D` then `s² = (s² + s) − s ∈ D`, a contradiction.  ∎

This is Hua's identity: an additive subgroup of a field that contains 1 and is closed under
inversion is closed under squaring.  B-D proved the square statement one paragraph before posing
item 2, so the answer was one identity away.

### 1.3 Difficulty check

- **Proved implications:** all of the above; the algebra is exact.
- **Unproved premise:** none new.  The trust points are B-D's Cor. `x^2` (which rests on their
  Gray-code normal number `κ`, Thm. `kappanor`, and Thm. `cex`) and Cor. `rrr`(2).  Two
  independent routes to the square input (B-D explicit, Manai probabilistic) reduce the risk.
- **Known-false sibling:** the mechanism uses only "additive subgroup ∋ 1, not closed under
  squaring".  On `G = ℚ + ℚ√2 + ℚ√3` it predicts a non-invertible element: `s = √2 + √3`,
  `s² = 5 + 2√6 ∉ G`, and indeed `1/(s+1) ∉ G`.  On fields (`ℚ(√2)`) the premise fails, as it
  must.  No false conclusion is reachable because the step is an identity.

### 1.4 Companions on the same list

- **Item 7** ("irrational `b` with `by` deterministic for every deterministic `y`?").  Taking
  `y = 1` forces `b ∈ D`, so item 7 is exactly: does some irrational deterministic `b` multiply
  `D` into itself?  The multiplier set `M = {b : bD ⊆ D}` is a subring of `ℝ` inside `D`.  If
  `b ∈ M` is algebraic irrational then `ℚ(b) ⊆ M ⊆ D`, so `BorelConjecture` (a normal number is
  never deterministic, B-D Prop. `nordet1`) excludes every algebraic irrational.  This is a
  consequence-graph edge for `MasterConjectures.lean`, not an answer.
- **Item 5(ii)** ("every nonzero `z` a ratio of a normal and a deterministic number?").  No, and
  trivially: at `z = 1` the ratio forces `x = y`, and `N ∩ D = ∅`.  For every rational `z ≠ 0`
  the same holds, since `zD = D`.  Worth one sentence in the note; it suggests B-D meant a
  different quantifier, so phrase it as a remark, not a result.
- **Item 5(i)/(iii) at `z = 1`** is item 3 (candidate 5).

### 1.5 Draft Lean statement (to freeze)

```lean
import NormalNumbers.RealDefs
import NormalNumbers.SeqDefs

namespace NormalNumbers.Deterministic

open Filter

/-- Upper density of `S` is at most `ε`. -/
def UpperDensityLE (S : Set ℕ) (ε : ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ N in atTop,
    (((Finset.range N).filter (· ∈ S)).card : ℝ) ≤ (ε + δ) * N

/-- Bergelson–Downarowicz Def. `complexity`: the length-`m` blocks in `F` cover every window of
`ω` outside a set of upper density at most `ε`. -/
def EpsCover (ω : ℕ → ℕ) (ε : ℝ) (m : ℕ) (F : Finset (List ℕ)) : Prop :=
  ∃ S : Set ℕ, UpperDensityLE S ε ∧
    ∀ i, i ∉ S → (List.ofFn fun j : Fin m => ω (i + j)) ∈ F

/-- B-D Def. `detb` (subexponential ε-complexity).  B-D Thm. `detdet` (Weiss, Lemma 8.9) shows it
is equivalent to their Def. `deta`: every quasi-generated measure has entropy 0. -/
def IsDeterministicSeq (ω : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∃ (m : ℕ) (F : Finset (List ℕ)), EpsCover ω ε m F ∧ (F.card : ℝ) < 2 ^ (ε * m)

/-- B-D Def. `detn`: deterministic in base `b`. -/
def IsDeterministic (b : ℕ) (x : ℝ) : Prop :=
  IsDeterministicSeq (digitOf b (Int.fract x))

end NormalNumbers.Deterministic

namespace NormalNumbers.Literature.BergelsonDownarowicz

open NormalNumbers.Deterministic

/-- B-D 2506.12929, Cor. `rrr`(2): `D(2)` is a subgroup of `(ℝ,+)` (stated: closed under
subtraction). -/
def DetSub : Prop :=
  ∀ x y : ℝ, IsDeterministic 2 x → IsDeterministic 2 y → IsDeterministic 2 (x - y)

/-- B-D Cor. `x^2`: the square of a deterministic number need not be deterministic. -/
def DetSqNotDet : Prop :=
  ∃ s : ℝ, IsDeterministic 2 s ∧ ¬ IsDeterministic 2 (s ^ 2)

/-- B-D item 2, the open question, as a Prop. -/
def ReciprocalQuestion : Prop :=
  ∀ y : ℝ, y ≠ 0 → IsDeterministic 2 y → IsDeterministic 2 y⁻¹

end NormalNumbers.Literature.BergelsonDownarowicz

namespace NormalNumbers.Deterministic
open NormalNumbers.Literature.BergelsonDownarowicz

/-- `1` is deterministic: its fractional part is `0`, all digits `0`.  Provable, ~98%. -/
theorem isDeterministic_one : IsDeterministic 2 1 := by sorry

/-- **Answer to Bergelson–Downarowicz item 2: No.** -/
theorem not_reciprocalQuestion (hsub : DetSub) (hsq : DetSqNotDet) :
    ¬ ReciprocalQuestion := by sorry

/-- The explicit form: the witness is one of `s`, `s + 1`, `(s * (s + 1))⁻¹`. -/
theorem exists_det_inv_not_det (hsub : DetSub) {s : ℝ}
    (hs : IsDeterministic 2 s) (hs2 : ¬ IsDeterministic 2 (s ^ 2)) :
    ∃ y ∈ ({s, s + 1, (s * (s + 1))⁻¹} : Set ℝ),
      y ≠ 0 ∧ IsDeterministic 2 y ∧ ¬ IsDeterministic 2 y⁻¹ := by sorry

/-- Guard-rule content locator: the premise is not vacuous on rationals (no rational has a
non-deterministic square), so the witness is irrational. -/
theorem witness_irrational (hsub : DetSub) {s : ℝ} (hs2 : ¬ IsDeterministic 2 (s ^ 2)) :
    Irrational s := by sorry

end NormalNumbers.Deterministic
```

`witness_irrational` needs "rationals are deterministic" (eventually periodic digits), a routine
lemma; it is the guard rule's degenerate-case verdict.  The Manai route can be added as a second
`Literature` Prop (`Manai2026QuadraticLog`) implying `DetSqNotDet` via "digit-1 frequency 0 ⇒
deterministic" (provable: one block family `{0^m}` covers all windows off a density-`mε` set).

## 2. Bergelson–Downarowicz item 4: products of two deterministic numbers (40%)

### 2.1 Source

Same list, verbatim:

> 4. Can any nonzero real number be represented as (i) the product, (ii) the ratio, or (iii) the
> product of reciprocals, of two deterministic numbers?

B-D's Prop. `seven` answers the normal analogue by a measure argument and the remark after it
answers the non-normal analogue by Baire category.  Neither applies to `D`, which is null and
meagre, which is presumably why item 4 was left open.

### 2.2 The answer

**Theorem (new as far as seen).**  The sets `D·D`, `D/D` and `(D·D)⁻¹` have Hausdorff dimension 0.
In particular Lebesgue-almost every real is not a product, a ratio, or a product of reciprocals of
two deterministic numbers, so the answer to (i)-(iii) is No.

*Proof sketch.*  Fix `δ > 0`.  Choose `ε` and `m` with `C_ω(ε, m) < 2^{εm}` and
`2ε + H(2ε)/m + ε log₂ r < δ` (B-D Def. `detb`).  For `ω` deterministic and `N` large, the bad
set `S` has `|S ∩ [0,N)| ≤ 2εN`, so some phase `φ < m` has at most `2εN/m` bad aligned windows
among `φ + mℕ`.  So the length-`N` prefix of `ω` is one of at most
`m · C(N/m, 2εN/m) · |F|^{N/m} · r^{2εN} · r^m ≤ r^{δN}` words, for `N ≥ N₀`.  The finite family
`F` ranges over finitely many sets for each `m`, so `D ∩ [0,1)` is a countable union of sets
`E(m, F, N₀)`, each covered for every `N ≥ N₀` by `r^{δN}` cylinders of length `r^{-N}`.  Hence
`dim_P D = 0`.  For two such pieces, the product map on `[−K, K]²` is `2K`-Lipschitz, so the image
of a pair of rank-`N` cylinders lies in an interval of length `≤ 4K r^{-N}`, and there are at most
`r^{2δN}` pairs.  Total length `≤ 4K r^{(2δ−1)N} → 0`, and the box-counting exponent is `≤ 2δ`.
Countable union: `dim_H(D·D) = 0`.  Ratio and reciprocal products use the locally Lipschitz maps
`(a, b) ↦ a/b` and `(a, b) ↦ 1/(ab)` away from `0`.  ∎

So `D` generates a subring of dimension 0 (every polynomial image of `Dᵏ` has dimension 0) which
nevertheless contains normal numbers (B-D Cor. `xynn`).

### 2.3 Difficulty check

- **Proved implications:** the covering bound and the Lipschitz image step; standard.
- **Unproved premise:** none mathematical.  The Lean work is the word count (a types-style bound
  `C(k, j) ≤ 2^{k H(j/k)}`, or the cruder `C(k, j) ≤ (ek/j)^j`) and the measure-zero cover.
- **Known-false siblings, which the mechanism must not "prove":**
  - *Liouville numbers.*  `dim_H L = 0`, yet every real is a product (and a sum) of two Liouville
    numbers (Erdős 1962).  The argument does not apply because it uses *packing* dimension 0,
    and `L` is a dense `G_δ` with packing dimension 1.  This is the exact separation: Hausdorff
    dimension 0 alone would "prove" a false statement.
  - *Non-normal numbers.*  Every real is a product of two (B-D remark after Prop. `seven`); the
    set is comeagre with packing dimension 1, so again the premise fails, as it must.
  - *Zero-frequency sets with a fixed upper density of free digits*, e.g. digits free on a set of
    upper density 1/2 and lower density 0: not deterministic (a quasi-generated measure has
    entropy `(log 2)/2`), and indeed packing dimension positive.  Consistent.

### 2.4 Draft Lean statement (to freeze)

```lean
namespace NormalNumbers.Deterministic

open MeasureTheory

/-- The word-count lemma: deterministic prefixes are subexponentially many.  The content. -/
theorem card_detPrefixes_le (b : ℕ) (hb : 2 ≤ b) (δ : ℝ) (hδ : 0 < δ) :
    ∃ cover : ℕ → Set ℝ,
      (∀ x ∈ Set.Ico (0 : ℝ) 1, IsDeterministic b x → ∃ i, x ∈ cover i) ∧
      ∀ i, ∃ N₀, ∀ N ≥ N₀, ∃ T : Finset ℕ, (T.card : ℝ) ≤ (b : ℝ) ^ (δ * N) ∧
        cover i ⊆ ⋃ t ∈ T, Set.Ico ((t : ℝ) / (b : ℝ) ^ N) ((t + 1 : ℝ) / (b : ℝ) ^ N) := by
  sorry

/-- **B-D item 4(i): No.**  The products of two deterministic numbers form a null set. -/
theorem volume_detProducts (b : ℕ) (hb : 2 ≤ b) :
    volume {z : ℝ | ∃ y₁ y₂, IsDeterministic b y₁ ∧ IsDeterministic b y₂ ∧ z = y₁ * y₂} = 0 := by
  sorry

theorem volume_detRatios (b : ℕ) (hb : 2 ≤ b) :
    volume {z : ℝ | ∃ y₁ y₂, IsDeterministic b y₁ ∧ IsDeterministic b y₂ ∧ y₂ ≠ 0 ∧
      z = y₁ / y₂} = 0 := by sorry

/-- (iii) follows from (i) through `z ↦ z⁻¹`. -/
theorem volume_detRecipProducts (b : ℕ) (hb : 2 ≤ b) :
    volume {z : ℝ | ∃ y₁ y₂, IsDeterministic b y₁ ∧ IsDeterministic b y₂ ∧
      z = y₁⁻¹ * y₂⁻¹} = 0 := by sorry

/-- The headline form of the answer. -/
theorem exists_not_detProduct (b : ℕ) (hb : 2 ≤ b) :
    ∃ z : ℝ, z ≠ 0 ∧ ¬ ∃ y₁ y₂, IsDeterministic b y₁ ∧ IsDeterministic b y₂ ∧ z = y₁ * y₂ := by
  sorry

/-- Stretch: `dimH = 0`. -/
theorem dimH_detProducts (b : ℕ) (hb : 2 ≤ b) :
    dimH {z : ℝ | ∃ y₁ y₂, IsDeterministic b y₁ ∧ IsDeterministic b y₂ ∧ z = y₁ * y₂} = 0 := by
  sorry

/-- Guard-rule content locator: `D` is nonempty and infinite (all rationals), so the null set
is not empty for a trivial reason. -/
theorem isDeterministic_ratCast (b : ℕ) (hb : 2 ≤ b) (q : ℚ) : IsDeterministic b q := by sorry

end NormalNumbers.Deterministic
```

The integer part needs one line: `IsDeterministic` reads `Int.fract`, so split `ℝ` into unit
intervals and use the cover on each translate.  The Maze gets the Liouville sibling as a row:
"Hausdorff dimension 0 alone" (`refuted`, cited Erdős 1962), so no later lap weakens the premise.

## 3. Manai's `P`/`Q` algorithm: `P(x)` normal, `Q(x)` non-normal (30%; multi-lap 75%)

### 3.1 Source and freshness

Manai, *Digit Mixing under Polynomial Maps*, arXiv:2606.08325v1, §1.1, verbatim: "A natural next
step would be an intrinsic algorithm constructing a number `x` for which `P(x)` is normal and
`Q(x)` is non-normal - provided that the polynomials `P` and `Q` are linearly independent."  Here
"normal" is absolute normality (the paper's convention).  Its two citers (Manai 2609.24665,
2508.09319v4) do not take it up.  Hypothesis as written is too weak: `P = Q + 1` is linearly
independent of `Q` and `P(x)` is normal iff `Q(x)` is.  The right condition is
`P ∉ span_ℚ(1, Q)`.

### 3.2 The answer, and why it is sharp

**Claim (paper 80%).**  For every non-constant `Q ∈ ℤ[X]` there is a computable `x` with `Q(x)`
not normal in base 2 and `P(x)` absolutely normal for **every** `P ∈ ℤ[X]` with
`P ∉ span_ℚ(1, Q)`.  Conversely, if `P = αQ + β` with `α, β ∈ ℚ` then `P(x)` is not absolutely
normal whenever `Q(x)` is not (Wall, `isNormal_rat_mul_add`; `α = 0` gives a rational).  So one
computable `x` realizes the whole dichotomy.  `Ω_k` is the case `Q = Xᵏ` restricted to
`deg P < k`.

**Mechanism.**  Pick a rational window `[l, r]` on which `Q' ≠ 0`, and rationals `a, c` with
`a + c·[1/2, 1] ⊆ Q([l, r])`.  For `y` in the quarter-Cantor set put `x = Q⁻¹(a + c y)`.  Then
`Q(x) = a + c y` is non-normal by structure (`not_isNormal_rat_affine_cantorReal`).  For each `P`,
`G_P(y) = P(Q⁻¹(a + c y))` is analytic on a neighbourhood of the window, and

    G_P''(y) = c² · W_P(x) / Q'(x)³,     W_P = P''Q' − P'Q'' ∈ ℤ[X],

with `W_P ≡ 0` iff `(P'/Q')' ≡ 0` iff `P ∈ span(1, Q)`.  So `G_P''` vanishes only at the
finitely many roots of the integer polynomial `W_P` in the branch, each of finite order.  That is
exactly the situation `ExplicitOmegaK` handles for `G_p = p(t^{1/k})` with `qPoly`:
`pushFourier_le_of_deriv2_lower` cuts cylinders near the roots, the uniform Baker–Banaji Prop
bounds the rest, and `FamilyDerandomize.exists_computable_absNormal_family` runs over `(P, b,
level)` with computable thresholds from heights.

### 3.3 Difficulty check

- **Proved here already:** the derandomizer, the cylinder cut, the uniform BB wiring, the `Xᵏ`
  instance of every analytic step.
- **Unproved premise:** none mathematical beyond the refereed `BakerBanajiUniformQuarterCantor`.
  The Lean work is (i) a computable branch inverse `Q⁻¹` with exact integer lower approximations
  (bisection on an integer polynomial, the analogue of `approx_Gfam`), (ii) `deriv2` lower bounds
  for `G_P` from a root clamp on `W_P` (the analogue of `deriv2_Gk_lower`), (iii) the height bounds
  feeding `decay_Gfam`.
- **Known-false sibling:** `P = αQ + β` must fail, and it does: `G_P` is rational-affine and
  `not_polyDecay_rat_affine` blocks the decay step.  A second sibling: `Q` with no monotone branch
  is impossible for non-constant `Q`, and a branch with `Q' = 0` inside is excluded by the window
  choice, so the premise is never vacuous.  The quarter-Cantor `y` itself is non-normal, so the
  mechanism cannot be "proving" normality of `Q(x)`.
- **Freshness gap:** "intrinsic" may mean efficient.  The derandomizer is primitive recursive and
  astronomically slow; say so in any note.

### 3.4 Draft Lean statement (to freeze)

```lean
namespace NormalNumbers.ExplicitPQ

open Polynomial NormalNumbers.ExplicitOmegaK NormalNumbers.ExplicitSquare

/-- `P` is a rational affine function of `Q`. -/
def AffineIn (P Q : ℤ[X]) : Prop :=
  ∃ α β : ℚ, P.map (Int.castRingHom ℚ) = α • Q.map (Int.castRingHom ℚ) + C β

/-- Evaluate an integer polynomial at a real. -/
noncomputable def ev (P : ℤ[X]) (x : ℝ) : ℝ := P.eval₂ (Int.castRingHom ℝ) x

/-- Sharpness (Wall): an affine-in-`Q` polynomial inherits non-normality.  Provable now, 95%. -/
theorem not_isAbsNormal_of_affineIn {P Q : ℤ[X]} (h : AffineIn P Q) {x : ℝ}
    (hx : ¬ IsNormal 2 (ev Q x)) : ¬ IsAbsNormal (ev P x) := by sorry

/-- The a.e. form, from the analytic BB corollary (as `ae_mem_Omega`).  85%. -/
theorem exists_PQ_of_analytic (hBB : BakerBanajiAnalyticQuarterCantor) (Q : ℤ[X])
    (hQ : 0 < Q.natDegree) :
    ∃ x : ℝ, ¬ IsNormal 2 (ev Q x) ∧ ∀ P : ℤ[X], ¬ AffineIn P Q → IsAbsNormal (ev P x) := by
  sorry

/-- **Manai 2606.08325 §1.1, answered (computable form).**  One computable coin sequence `e`,
rational branch data, and `x = Q⁻¹(a + c·cantorReal e)` realize the full dichotomy. -/
theorem exists_computable_PQ (hBB : BakerBanajiUniformQuarterCantor) (Q : ℤ[X])
    (hQ : 0 < Q.natDegree) :
    ∃ (a c : ℚ) (e : ℕ → Bool) (x : ℝ), Computable e ∧ c ≠ 0 ∧
      ev Q x = a + c * cantorReal e ∧
      ¬ IsNormal 2 (ev Q x) ∧
      ∀ P : ℤ[X], ¬ AffineIn P Q → IsAbsNormal (ev P x) := by sorry

/-- Guard-rule content locator: `Q = Xᵏ` recovers the `Ω_k` witness family. -/
theorem omegaK_of_PQ (k : ℕ) (hk : 2 ≤ k) (p : ℤ[X]) (h1 : 1 ≤ p.natDegree)
    (hk' : p.natDegree < k) : ¬ AffineIn p (X ^ k) := by sorry

end NormalNumbers.ExplicitPQ
```

`x` is a computable real as well (a branch root of a computable value), but the frozen form keeps
the repo's `Computable e` convention from `exists_computable_mem_Omega`.

## 4. Erdős #257 for squarefree `A` (15%; paper 60%)

### 4.1 Source and freshness

erdosproblems.com/257, edited 2026-04-15, verbatim: "Let `A ⊆ ℕ` be an infinite set. Is
`Σ_{n∈A} 1/(2ⁿ−1)` irrational?"  The page and forum (fetched 2026-10-03) list: `A = ℕ` (Erdős
1948), pairwise-coprime summable (Erdős 1968), any summable `A` at every base (Cook, forum
2026-09-11, FC PR #6529), Cook's weighted / mixed supports (FC PR #6528, `LogBudgetCover`, a
summability hypothesis), even/odd `A` (Kovač via Borwein), primes and prime powers
(Tao–Teräväinen).  This repo adds every infinite prime set (conditional) and `k·S`.  **No source
lists squarefree, `k`-free, or semiprime `A`.**  Kovač (forum) expects a *negative* answer for
some `A` at base 2 (the subsum set is a fat Cantor set), so the target must use structure.

### 4.2 Mechanism

`Σ_{n squarefree} 1/(bⁿ−1) = Σ_m 2^{ω(m)} b^{-m}`, since the squarefree divisors of `m` number
`2^{ω(m)}`.  The Campbell / CaptainSude construction for `E_b` (`τ(m)` coefficients), which
`JointLambertUnconditional` formalizes, places one designed position `m` whose coefficient
encodes the target word, and keeps a buffer of positions `m + j = (large prime)·(small)` with
small coefficients.  For `2^{ω}` the buffer step transfers unchanged (`2^{ω(p·c)} = 2·2^{ω(c)}`).
The encoding does not: `EvenEncoding` uses `{2a/bˢ}` with arbitrary `a`, and `2^{ω}` takes only
powers of 2, which at `b = 2` are dyadic and encode nothing.  Replacement: encode across
`L` consecutive designed positions with `ω(m + j) ∈ {1, 2}`, so the window value is
`Σ_j 2^{ε_j + 1} b^{L−j}`, which realizes every residue pattern needed in base 2 (twice a 0/1
word plus a constant).  CRT then has to make `m + 1, …, m + L` squarefree with prescribed `ω`,
which is standard.

### 4.3 Difficulty check

- **Proved:** the identity; the buffer and tail estimates for `τ` (Lean, unconditional).
- **Unproved premise:** the multi-position encoding plus squarefree CRT, and re-running the tail
  bound with `2^{ω}` (no larger than `τ` on squarefree `m`, at most `τ` always: fine).
- **Known-false sibling:** the mechanism needs CRT control of `f_A` at chosen positions, so it
  says nothing about unstructured `A` (where Kovač expects failure), and it does not "prove"
  irrationality for `A` with a rational sum, because none is known.  A sharper sibling test before
  any lap: run the encoding on `f ≡ 2` constant (`A = {1, p}`-type supports are finite, excluded),
  i.e. check the construction really uses the variability of `ω`.
- **Lean cost:** the joint-Lambert modules are specialized to `τ`; a refactor over a coefficient
  function is several laps, hence the 15%.

### 4.4 Draft Lean statement

```lean
namespace NormalNumbers.Erdos257

/-- #257 for the squarefree integers. -/
theorem erdos257_squarefree :
    Irrational (∑' n : {n : ℕ // 0 < n ∧ Squarefree n}, (1 : ℝ) / (2 ^ (n : ℕ) - 1)) := by sorry

/-- The digit form: binary disjunctivity of `Σ 2^{ω(m)} 2^{-m}`. -/
theorem isDisjunctive_twoPowOmega (b : ℕ) (hb : 2 ≤ b) :
    IsDisjunctive b (∑' m : ℕ, (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors (m + 1)) /
      (b : ℝ) ^ (m + 1)) := by sorry

end NormalNumbers.Erdos257
```

## 5. B-D item 3: a normal number with deterministic reciprocal (15%)

Verbatim: "3. Does there exist a normal number whose reciprocal is deterministic?"  Item 5(i) and
5(iii) at `z = 1` are the same question.  The repo's route (`exists_oneFreqZero_inv_normal`,
open input `inv_logDecay_squares`, audit `EXPLICIT-SQUARE-NONNORMAL-AUDIT-2026-10-02.md`) is
unchanged at 15%.  New this pass: Hua's identity gives a dichotomy from Manai 2606.08325's
deterministic `X` with `X²` normal.  Then `X² + X` is normal (Rauzy, B-D Cor. `rrr`(1)), and
either (a) `1/X` and `1/(X+1)` are both deterministic, and `w = 1/(X(X+1))` is a deterministic
number with normal reciprocal, answering item 3; or (b) one of them is not, which re-answers
item 2 and leaves item 3 open.  The open premise is deciding the branch, and nothing in hand does.
A tiling attempt (`x·v = 1` with no carries, each column hit once, as in B-D Prop. `1/y`) fails
for a structural reason: de Bruijn's classification makes both tiles of `ℕ` digit-restricted
sets in a mixed radix, so both indicator sequences are deterministic.

## 6. Leftovers and things checked and dropped

- **Pulari relabelings, BLD odd bases:** unchanged from the 2026-10-02 sweep, 15% each.
- **Erdős #257 false at base 2 (Kovač).**  Every subsum point has a unique greedy support
  (`1/(2ⁿ−1)` exceeds its tail), so "rational `r` is a subsum" is an infinite greedy run with
  growing denominators; no engine here proves membership.  Dropped.
- **Erdős #1049, #249, #251, #252, #269, #406:** no engine bearing (integer base needed, signed
  Möbius, factorial base, Hecke–Mahler, single orbits).  #251 has an active normality route by
  StefanRinger (forum).  FC/site status mismatches noted for outreach only: FC marks #260, #267,
  #254 solved while the site says open, and FC's #270 `linear` variant is stale.
- **Base `b ≥ 3` #257 for Mertens-rate prime sets** is already proved here
  (`isDisjunctive_subsetLambert`) and is unlisted on the site and FC; an outreach item, not a
  target.

## Recommendation

**Freeze candidates 1 and 2 together** in one worktree module
(`src/NormalNumbers/DeterministicBD.lean`).  Candidate 1 is a one-lap certainty (the only work is
the definition and the Hua algebra on two cited B-D Props); candidate 2 is the meatier word-count
lemma behind the same note.  The outward deliverable is one
`docs/notes/bergelson-downarowicz-questions.md` answering items 2, 4 and 5(ii) and reducing 7.
Honest caveat: these answers use elementary algebra and fractal counting, not the repo's
engines, and item 2 is small enough that B-D may regard it as an oversight rather than a theorem.

**The engine-native target is candidate 3** (Manai's `P`/`Q` algorithm): the same machinery that
just closed `Ω_k`, generalized to an arbitrary `Q`, with a sharp answer.  Run it as a 2-3 lap
campaign after the B-D lap; the a.e. form (`exists_PQ_of_analytic`) is a one-lap warm-up.
Candidate 4 (#257 squarefree) has the most cultural weight but is a multi-lap refactor of the
joint-Lambert engine; schedule it as a campaign, not a lap.
