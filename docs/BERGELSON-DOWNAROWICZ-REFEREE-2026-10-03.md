# Referee: cited hypotheses in `DeterministicBD.lean` (2026-10-03)

Scope: `src/NormalNumbers/DeterministicBD.lean` at `f5a1fbd0` (leaf (b) now proved).  I checked each
definition and cited `Prop` quantifier by quantifier against the sources:

* Bergelson–Downarowicz, arXiv:2506.12929v1.  I used the TeX `Final2.tex` and the **printed v1 PDF**,
  which settles the numbering.
* Manai, arXiv:2606.08325v1.  I used `bernoulli.tex` and the printed PDF.
* Erdős, Michigan Math. J. 9 (1962) 59–60 ([Project Euclid](https://projecteuclid.org/euclid.mmj/1028998621)),
  read through the restatement in Chalebgwa–Morris, *Topology meets number theory*
  ([PDF](https://sidneymorris.net/Morris185.pdf)), Thm. 17.

Numeric tripwire: `probes/deterministic_block_count_probe.py`.  It exits 0 when every assertion
passes (see the last section).

## 0.  Every B-D theorem number outside §3 is wrong (they must be fixed)

The file's numbers were "computed from the TeX".  The TeX has two hidden traps:

1. a commented-out `%\begin{rem}\label{allthesame}` at TeX line 548, which shifts §4 by one;
2. a `\begin{comment}` … `\end{comment}` block (lines 1706–1891) that removes a whole `\section`
   ("Topological version of Rauzy theorem").  That shifts every section after §6 down by one.

The printed PDF (`pdftotext` of arxiv.org/pdf/2506.12929v1) gives the correct numbers:

| file says | printed v1 | label |
|---|---|---|
| Prop. 4.8(1),(4) | **Prop. 4.7**(1),(4) | `nordet1` |
| Cor. 4.11(4) | **Cor. 4.10**(4) | `rauzy` |
| Cor. 4.12(2) | **Cor. 4.11**(2) | `rrr` |
| Cor. 9.15 | **Cor. 8.15** | `x^2` |
| Thm. 9.11 | **Thm. 8.11** | `cex` |
| Prop. 9.13 | **Prop. 8.13** | `1/y` |
| §9.6 open problems | **§8.6** (questions (2), (4) verbatim as quoted) | `S7` |
| "B-D's §9 examples" | **§8** | |

The §3 numbers (Def. 3.5, 3.6, 3.8, Thm. 3.9, Def. 3.10, Prop. 3.11) are correct.

**Fix** (docstrings only): lines 16, 69, 106, 108, 114–115, 119, 125, 215, 244 per the table.  Also
replace the module-doc sentence "theorem numbers … computed from the v1 TeX source" with "numbers
from the printed v1 PDF".

## 1.  Definitions: `UpperDensityLE`, `EpsCover`, `IsDeterministicSeq`, `IsDeterministic`

**Verdict: faithful (95%).**

* `UpperDensityLE S ε` is the statement `∀δ>0, eventually |S∩[0,N)| ≤ (ε+δ)N`.  This is exactly
  `limsup |S∩[0,N)|/N ≤ ε`, which is B-D Def. 2.2 with "not exceeding ε" (Def. 3.6).  B-D count
  `[1,n]` and the file counts `[0,N)`, and densities are shift-invariant.  `ω` is 0-indexed, so
  `ω i` is B-D's `x_{i+1}`.
* `EpsCover` / Def. 3.6: B-D take `F ⊂ Λ^m` and the windows `ω|[i,i+m-1]` for `i ∉ 𝕊`, and so does
  the file.  `List.ofFn (fun j : Fin m => ω (i+j))` is that window.  Junk lists in `F` only raise
  `|F|`.
* **≤ ε vs < ε, base 2 vs `r` or `e`, ε ∈ (0,1) vs ε > 0: none of these matter.**  The Lean
  predicate is monotone in ε.  The same `(S, F)` serves every larger ε, because `d̄(S) ≤ ε' ≤ ε`
  and `2^{ε'm} ≤ 2^{εm}`.  So:
  * "< ε" follows from "≤ ε/2", and that witness costs only `2^{εm/2} ≤ 2^{εm}`.
  * For a base `c^{εm}`, apply the base-2 condition at `ε' = ε·min(1, log_2 c)`, and the other way
    at `ε' = ε·min(1, 1/log_2 c)`.  The density side only gets tighter.
  * For ε ≥ 1 the condition follows from ε = 1/2.  (For ε ≥ 1 it is even trivially true: `S = ℕ`,
    `F = ∅`, `m = 0`.  That is harmless, because the ∀ε quantifier is decided by small ε.)
  * B-D's `log` is `log_2` (§3, item 1), so "2" is their own base.
* `m = 0` cannot cheat for ε < 1: with `F = {[]}` the bound needs `1 < 2^0`, which is false, and
  `F = ∅` forces `S = ℕ`, whose upper density is 1.
* `IsDeterministic b x := IsDeterministicSeq (digitOf b (Int.fract x))` matches B-D in three ways:
  * It uses the alias of `{x}`, as in B-D §4.1 and Remark 4.5(4): `x ∈ 𝒟(r) ⟺ {x} ∈ 𝒟(𝕋,R)`.
  * b-adic rationals get the 0-ending expansion, as in the Remark after Prop. 4.1.  The floor
    formula gives exactly that.
  * Negative `x` cause no ambiguity.  `fract(−x) = 1 − fract x` has the digits `r−1−d`, which is
    a conjugacy, and B-D Remark 4.8 gives `−𝒟 = 𝒟`.

**Thm. 3.9 (Def. 3.5 ⟺ Def. 3.8) holds (90%).**  Weiss [W3, Lemma 8.9] states it without proof.
A full proof is BDV Thm. 6.11, and the B-D Appendix gives a sketch.  The sketch handles all of `M_ω`
in both directions:

* (⇒) uses compactness of `M_ω`.  Dini gives `(1/n)H_μ(P^n) ↓ 0` uniformly on `M_ω`.  The sketch
  produces `C ≤ 2^{2εm}`, which reparametrises to Def. 3.8 by the monotonicity above.
* (⇐) works for every quasi-generic `μ` along its own subsequence.

There is one cosmetic gap in (⇐).  "By letting m grow" is not legitimate, because `m` is tied to ε.
Their own bound repairs it: `(1/m)H(ζ,1−ζ) ≤ H(ε)` for ζ < ε ≤ 1/2, which gives
`h(μ) ≤ H(ε) + ε + ε log r → 0` for any `m ≥ 1`.  Quasi-generic measures are fully covered.  The
transcription "Def. 3.8 in Lean, corollaries proved for Def. 3.5" is sound.

## 2.  `DetSub b` (B-D **Cor. 4.11(2)**, not 4.12)

**Verdict: implied for every b ≥ 2 (93%), and trivially true for b ≤ 1** (all digits are 0).

* B-D state it for "a fixed (but arbitrary) base r ≥ 2" (§4.2 preamble).
* Cor. 4.11(2) says "`𝒟(r)` is a subgroup of `(ℝ,+)`".  Closure under `x − y` is a weakening.
* `Int.fract` is handled by Remark 4.5(4).
* **Carries are absorbed by the torus model, and the proof covers them.**  Prop. 4.9(d)
  (`h̄(x+y) ≤ h̄(x) + h̄(y)`) is proved on `(𝕋, R)`.  The pair `(x,y)` generates a joining along a
  subsequence, and `(t,u) ↦ t+u` is a continuous equivariant factor map `𝕋² → 𝕋`.  So the
  measure generated by `x+y` is a factor of the joining, and entropy is subadditive on joinings
  (3.2).  No digit-level carry analysis is needed.
* Moving between the alias and the torus point uses Prop. 4.1.  `φ_r` is at most 2-to-1, so
  `h(φ_r^*μ) = h(μ)`, even with atoms (finite-to-one factors, [LW, Thm 2.1]).  Remark 3.3 /
  Remark 2.9 give `M_{φ(ω)} = φ^*(M_ω)`.
* Negation is Remark 4.8.

**Fix:** citation numbers only.

## 3.  `DetSqNotDet` (B-D **Cor. 8.15**) and `NormalNotDet` (B-D **Prop. 4.7**(1),(4))

**`DetSqNotDet`: implied, base 2 (88%).**  The printed statement is "The square of a deterministic
number need not be deterministic".  The proof sets `s = (a+b)/2`, `t = (a−b)/2` with
`a = xy ∈ 𝒟(2)` and `b = 1/y ∈ 𝒟(2)` (Thm. 8.11, Prop. 8.13).  Then `s² − t² = ab = x` is normal,
so `s²` or `t²` is not deterministic.  Everything is binary.

My confidence is below 95% only because I did not re-verify the §8 constructions (Thm. 8.11,
Prop. 8.13).  The deduction itself is two lines.  Side note: the Cor. 8.15 proof in the printed v1
cites "Theorems 4.9 and 4.25", which are actually Prop. 4.9 and Prop. 4.25.  That is a typo in the
paper, not in the Lean file.

**`NormalNotDet b`: implied for b ≥ 2 (97%), but FALSE for b ∈ {0, 1}.**

* For b ≥ 2: normal means generic for the uniform Bernoulli measure, so `M_x` is a singleton with
  entropy `log_2 r > 0` (Prop. 4.7(4)).  So `x` is not deterministic (Prop. 4.7(1)), and Thm. 3.9
  transfers this to Def. 3.8.
* For b = 1: `digitOf 1 _ ≡ 0`.  `IsNormalSequence 1 0^ω` holds, because the only admissible
  blocks are `0^k`, with frequency `1 = 1^{-k}`.  `IsDeterministic 1 x` holds by
  `isDeterministicSeq_zero`.
* For b = 0: `IsNormalSequence 0` is vacuous and `digitOf 0 ≡ 0`.

Nothing is inconsistent, because only `NormalNotDet 2` is ever assumed (`detSqNotDet_of_manai`).
But a `Literature.*` family that is false at some parameter is a defect.

**Fix:** use `def NormalNotDet (b : ℕ) : Prop := 2 ≤ b → ∀ x : ℝ, IsNormal b x → ¬ IsDeterministic b x`.
In `detSqNotDet_of_manai`, use `hN le_rfl _ hX2`.  Optionally add the control
`theorem not_normalNotDet_one : ¬ (∀ x : ℝ, IsNormal 1 x → ¬ IsDeterministic 1 x)`, proved via
`isDeterministicSeq_zero`.

## 4.  `Literature.Manai2026.QuadraticLogWitness` (claimed Manai **Cor. 1.4**; the number is correct)

Manai's Cor. 1.4 (printed v1) says: there is an absolute constant `A₀ > 0` such that if
`v_n = p_n(1−p_n) ≥ A (log n / n)^{1/2}` for all sufficiently large `n`, with `A ≥ A₀`, then `X²`
is a.s. absolutely normal.  Here `X = Σ_{n≥1} ξ_n 2^{-n}` with independent `ξ_n ~ Bernoulli(p_n)`.

**Verdict: true (93%), but NOT faithful-or-weaker.**  `∃ X, OneFreqZero X ∧ IsNormal 2 (X²)` is a
corollary of Cor. 1.4 plus three steps of our own, none of them in Manai:

1. choose `p_n → 0` at the threshold rate;
2. a law of large numbers for *non-identically distributed* Bernoullis (Mathlib's `strong_law_ae`
   is for identically distributed variables, so this is not off the shelf);
3. a.s. the digit sequence of `Int.fract X` equals `ξ`.

The base-2 weakening of absolute normality is fine.

**Fix: split the Prop.**  Replace it with a faithful statement and a sorry'd bridge:

```lean
/-- Manai 2606.08325v1 **Cor. 1.4** (label `cor:quadratic-log`), weakened from absolute normality
to base 2.  Index shift: Lean `ξ n` sits at `2^{-(n+1)}`, i.e. is Manai's `ξ_{n+1}`; since
`(log n / n)^{1/2}` is eventually decreasing, the hypothesis below on `p n` implies Manai's on
`p_{n+1}`, so this is weaker than the source. -/
def Cor14 : Prop :=
  ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A ≥ A₀, ∀ p : ℕ → ℝ, (∀ n, p n ∈ Set.Icc (0 : ℝ) 1) →
    (∀ᶠ n : ℕ in atTop, A * (Real.log n / n) ^ (1 / 2 : ℝ) ≤ p n * (1 - p n)) →
    ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
      (ξ : ℕ → Ω → ℕ), (∀ n, Measurable (ξ n)) → ProbabilityTheory.iIndepFun ξ volume →
      (∀ n, volume.real {ω | ξ n ω = 1} = p n ∧ volume.real {ω | ξ n ω = 0} = 1 - p n) →
      ∀ᵐ ω, IsNormal 2 ((∑' n, (ξ n ω : ℝ) / 2 ^ (n + 1)) ^ 2)
```

(Adjust the `iIndepFun` argument form to the pinned Mathlib.)  Keep `QuadraticLogWitness` as a
plain `def` outside `Literature`, and add:

```lean
/-- Confidence 90%.  English proof: take `A = A₀`, `p n = min (1/2) (2 A₀ (log n / n)^{1/2})`
(so `p n (1 - p n) ≥ p n / 2 ≥ A₀(…)^{1/2}` once the min is the second branch, and `p n → 0`).
`Ω = ℕ → Bool` with `Measure.infinitePi` of Bernoulli(`p n`), `ξ` the coordinates.  (i) Digit-1
frequency `0` a.s.: `E S_N = Σ_{n<N} p n = o(N)` (Cesàro), `Var S_N ≤ E S_N ≤ N`; Chebyshev at
`N = 2^k` gives `P(|S_{2^k} − E| > δ 2^k) ≤ 2^{-k}/δ²`, summable, so Borel–Cantelli plus
monotonicity of `S_N` on `[2^k, 2^{k+1}]` gives `S_N / N → 0` a.s.  (ii) A.s. `ξ` is not eventually
`1` (`∏_{n ≥ M} p n = 0`), so `X < 1` and `digitOf 2 (Int.fract X) n = ξ n` for all `n`.
(iii) Intersect with the a.s. event of `Cor14`; a probability measure has a point in it. -/
theorem quadraticLogWitness_of_cor14 (h : Literature.Manai2026.Cor14) : QuadraticLogWitness := by
  sorry
```

Then `detSqNotDet_of_manai` takes `hM : Literature.Manai2026.Cor14` and calls the bridge.  The
current docstring already flags the extra conjunct honestly.  The fix moves it out of the cited
statement and into a theorem the compiler tracks.

## 5.  Liouville Props

**`Erdos1962Product`: faithful (97%).**  Erdős (1962) proves every real is a sum of two Liouville
numbers and every *nonzero* real is a product of two.  Chalebgwa–Morris, Thm. 17(ii), restate it
as "`s ≠ 0` ⇒ `s = c·d`, `c, d ∈ X`" for any dense G_δ `X ⊆ ℝ`, in particular for the Liouville
numbers.  Mathlib's `Liouville` matches the classical definition.

**Upgrade available:** this is provable now, because Mathlib has `eventually_residual_liouville`,
`IsGδ.setOfPred_liouville` and `dense_liouville`.  The sets `{x ≠ 0 | Liouville (z / x)}` and
`{x | Liouville x}` are both dense G_δ, so Baire gives a common point.  That is roughly 40–60
lines, and it would demote a `Literature` Prop to a theorem.

**`DimHZero`: the Prop is faithful (95%), but its docstring makes a FALSE claim.**  It says
"`h`-measure zero for every dimension function", and that is false in ZFC:

* A set that is `H^h`-null for every gauge `h` has strong measure zero (Besicovitch).
* A dense G_δ contains a Cantor set, which maps uniformly continuously onto `[0,1]`, so it is never
  strong measure zero.

(85% on this argument.  It also shows the "Jarník" attribution is misplaced.  Jarník–Besicovitch
gives `dimH {τ-approximable} = 2/τ`, which also implies `dimH L = 0`.)

**Fix the docstring** to: "the Liouville numbers have `s`-dimensional Hausdorff measure `0` for
every `s > 0` (Oxtoby, *Measure and Category*, Springer GTM 2, **Thm. 2.4**, as cited by
Chalebgwa–Morris [44, Thm. 2.4]); hence `dimH = 0`".  Confidence on the Oxtoby theorem number is
80%: I have it from Chalebgwa–Morris, not from Oxtoby directly.  The fact itself is elementary and
could be proved in Lean.  Cover `L` by `⋃_{q ≥ Q} ⋃_{p} B(p/q, q^{-n})`.  Then
`H^s ≤ Σ_{q≥Q} (q+1)(2q^{-n})^s → 0` for `ns > 2`.  That is the covering in Mathlib's
`Liouville/Measure.lean`, rerun with `hausdorffMeasure_le_liminf_tsum`.

## 6.  Is anything vacuous or false?

* **False:** `NormalNotDet b` at b ≤ 1 (§3), and the `DimHZero` docstring (§5).  Both are harmless
  to the headlines, and both should be fixed.
* **Not vacuous:** the answers to Q2 and Q4 are genuine.
  * `hua_witness` is correct algebra: `1/s − 1/(s+1) = 1/(s(s+1))`, then `(s²+s) − s = s²`.
  * Q4 `dimH (𝒟·𝒟) = 0` does not conflict with B-D Cor. 8.14 (a product of two deterministic
    numbers can be normal).  A null set can contain normal numbers.
  * I re-derived the English proof of leaf (a): the phase pigeonhole, the bad-window binomial
    `≤ 2^{(N/m)H(2ε')}`, and the countable index `(k, m, F, N₀)`.  It is sound (85%).  One small
    point: its ε' condition `H(2ε') + ε' + 2ε' log₂ b < ε log₂ b` is stronger than needed (the
    `H` term carries a `1/m`), which is fine.
* **`not_dimH_prod_zero_of_dimH_zero` is a meaningful control (95%).**
  * Erdős gives *multiplication* onto ℝ∖{0}, which matches the Lean `z = x * y` with `z ≠ 0`.
  * The conclusion is a true fact: multiplication is locally Lipschitz, so
    `dimH (L × L) ≥ dimH (L·L) = 1`.  `L` has `dimH 0` but packing dimension 1 (it is comeager),
    which is the classical example of `dimH(A×B) > dimH A + dimH B`.
  * It refutes the weakening of leaf (b) to hypotheses on `dimH` alone.  It is not a control for
    leaf (a), which needs its own known-false sibling.  A suggestion: show that the
    positive-entropy sets `{x : h̄(x) ≤ η}` fail `SubexpCylinderCount b ε` for ε < η / log₂ b.

## Numeric tripwire: `probes/deterministic_block_count_probe.py`

Setup: prefix length `L = 2^25`, `m = 1..24`.  The script asserts against hand-derived values,
never against its own output.

* **Fibonacci word:** `p(m) = m + 1` exactly at every `m` (Sturmian).
* **Thue–Morse:** `p(1..3) = 2, 4, 6`, by hand from overlap-freeness.  `p(4..8) = 10, 12, 16, 20,
  22` match OEIS A005942.  `p(m) ≤ 4m` holds throughout.
* **Pseudo-random control:** `p(m)` is within 2% of the occupancy formula
  `2^m(1 − (1−2^{-m})^{L−m+1})` at every `m`.

Block-count exponent `log2 p(m) / m` at `m = 24`:

| sequence | exponent | expected limit |
|---|---|---|
| Fibonacci | 0.193 | → 0 |
| Thue–Morse | 0.260 | → 0 |
| random control | 0.991 | ≈ 1 |

The control shows the instrument separates positive entropy from deterministic sequences.
