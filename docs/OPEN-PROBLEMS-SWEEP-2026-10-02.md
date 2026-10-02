# Open-problem sweep, 2026-10-02 🔎

Ranked bet #5 of `HEADLINES.md`: harvest explicitly stated open problems from 2024-2026 papers on
normal numbers, disjunctivity, explicit constants and normality-preserving maps, and grade each
against this repo's machinery.  Sources were read in full TeX (arXiv e-print) or on the
erdosproblems.com page and forum thread; every quoted statement below was copied from the source,
not from a search summary.  Forward citations were checked with `papers followups <id>`, and the
newest arXiv version of each paper was the one read.

**Scope.**  arXiv API queries over math.NT / math.DS / math.CO / math.LO for 2024-01 to
2026-10-02 (normal, absolutely normal, simply normal, disjunctive, continued fraction + normal,
Champernowne, Stoneham, BBP, Lambert, Erdős-Borwein, finite-state dimension, Poisson generic,
Rauzy/deterministic, Cantor series), the `teorth/erdosproblems` metadata (tags *irrationality*,
*base representations*) with the live problem pages, the `formal-conjectures` upstream file for
#257 and its open PRs, and two web searches for continued-fraction normality and BBP/Stoneham.
30 papers were downloaded and grepped for problem/question/conjecture environments and for
"open", "we ask", "it would be interesting", "we do not know".

**Instrument limits.**  The arXiv API phrase search is weak, and continued-fraction normality
(Vandehey and coauthors) produced **no 2024-2026 paper** with a stated problem; the newest CF
papers found are 2015-2021 and therefore out of window.  Papers not on arXiv were not reached.
So "no CF candidate" here means "none found by this instrument", not "none exists".

**Excluded by rule.**  Normality of π, e, √2, ln 2, log₃ 2 and other headline constants;
abelian-normality of π and e (Campbell 2603.04396 §Conclusion, which already needs simple
normality of π); anything the repo already proved.

## Ranked table

| # | Source | Statement (short) | Status | Machinery | Mechanism | Conf. |
|---|---|---|---|---|---|---|
| 1 | Erdős #257; Tao-Teräväinen 2512.01739 §1 "An irrationality result" | Is `Σ_{n∈A} 1/(2ⁿ−1)` irrational for every infinite `A`?  Sub-case `A = k·S`, `k ≥ 2`, `S` a prime set | Open in general; listed known cases are `A = ℕ`, primes, prime powers, pairwise-coprime summable, summable (Plectis note), eventually periodic | `isDisjunctive_subsetLambert` (Mertens-rate prime sets, any base `b ≥ 3`), C′ `isNormal_subsetLambert_of_sqrtFreshMassZero`, `PowerBaseReal` | `Σ_{n∈kS} 1/(2ⁿ−1) = Σ_{p∈S} 1/((2ᵏ)ᵖ−1) = subsetLambert S (2ᵏ)`, base `2ᵏ ≥ 4`.  Disjunctive ⇒ irrational.  For `k = 2` and C′ sets the sum is even **normal in base 2** | 90% |
| 2 | Same, base 2 itself | `A = S ⊆ primes` with `S` "sufficiently similar to the primes" (TT: "likely", not pursued) | Open; TT prove only `S = all primes` | binary prime-Lambert draft `docs/prime-lambert-disjunctivity-draft.md`, Elliott front, residue-class Mertens | Rerun the binary disjunctivity draft with `ω_S` in place of `ω`; the needed input is a two-point correlation for `ω_S` at `b = 2`, where the fixed-base threshold `b > 2^{5/4}` fails | 25% |
| 3 | Manai 2506.15422 §1; Manai 2508.09319 second "Open problem" (after Def. `def:deg`) | Explicitly *determine* a normal `x` with `x²` not normal; construct explicit `x ∈ Ω_k` | Existence answered by Manai 2609.24665, theorem `thm:2` (non-affine `C²` maps do not preserve normality); explicit example open | Wall rational, B5′ explicit constructions, Becher-Yuhjtman-style digit-by-digit builders | Build `y` in a sparse Cantor-type set (deterministic, base-2 non-normal) whose square root is base-2 normal, by derandomizing a Fourier-decay bound for the `√` pushforward, as Becher-Lew Deveali do for odd bases | 20% |
| 4 | Pulari 2602.01199 "Discussion and open questions" | Does a weaker condition (levelwise surjective or bounded-to-one) on a finite-state relabeling suffice for the equidistribution characterization of `f`-normality? | Open | Agafonov / transducer state-tracking from the §7 campaign | The paper proves the invertible (finite-state coherent) case; the question is whether non-invertible relabelings keep the equidistribution side, and a counterexample likely comes from a two-state non-injective relabeling | 15% |
| 5 | Bergelson-Downarowicz 2506.12929 "Some natural open problems", items 2, 3 | Is the reciprocal of a deterministic number deterministic?  Is there a normal number whose reciprocal is deterministic? | Open (followups 2609.24665, 2606.08325, 2512.01239 do not address them) | Rauzy (H4 frontier), Wall rational | One deterministic `y` with `1/y` normal answers Q2 (no) and Q3 (yes) at once; candidate `y` from the Becher-Lew Deveali sparse Cantor sets, with `1/y` controlled by the same `C²` pushforward decay as row 3 | 15% |
| 6 | Becher-Lew Deveali 2607.06773 Introduction | Non-normality in odd bases inside the sparse Cantor set `C`; a polynomial-time construction blocked by residue multiplicities of `⌊ℓrⁿ/2ᵃ⌋ mod 2ᵏ` | Open | Korobov / Stoneham orbit counting (`isNormal_two_stoneham23`) | The named obstacle is a Korobov-type count of `rⁿ` modulo powers of 2, which is what the Stoneham proof already does for `3ⁿ mod 2ᵏ` | 15% |
| 7 | Clanin-Rayman 2506.02332 concluding section | Bounds on `|dim_FS(CE_b(A)) − dim_FS(CE_b(p(A)))|` for polynomials of degree `≥ 2` | Open | Weyl criterion, Davenport-Erdős | Davenport-Erdős Weyl-sum argument made quantitative in block entropy; degree 1 is done in the paper | 10% |
| 8 | Becher-Lew Deveali 2607.06773 Introduction | Conjecture: among base-2 deterministic numbers, normality in all bases multiplicatively independent of 2 is generic | Open | none | Needs a topology on deterministic numbers in which Schmidt-type Fourier decay is generic | 10% |
| 9 | Manai 2508.09319 first "Open problem" (§1) | Polynomial-time algorithm for an LIL-normal or transcendentally normal number | Open | B5′ constructions | Becher-Heiber-Slaman polynomial-time absolute normality, extended to countably many polynomial images | 10% |
| 10 | Manai 2506.15422 §1 | Conjecture: no non-constant continuous `φ` with `φ(𝒩ᶜ) ∩ 𝒩ᶜ = ∅` | Open | none | Topological; super-dense set method needs nowhere-constancy | 10% |
| 11 | Kaneko-Mance 2510.23380 "Open problems" section | `N(α)` is `Π⁰₃`-complete for every `|α| > 1`, and four relatives | Open | none (descriptive set theory) | Becher-Heiber-Slaman reductions transplanted to `ξαⁿ` | 8% |
| 12 | Manai 2606.08325 Conjecture `con:summability` | Summability `Σ s·exp(−c_d R_d(s)) < ∞` ⇒ `P(X)` a.s. absolutely normal; critical window | Open | none | Overlapping-tuple dependency control in Fourier decay | 8% |
| 13 | Farhangi-Mance 2512.01239 Question `Borel`, Conjectures `HotSpot`/`ZeroEntropy`/`PositiveEntropy` | Is `{Q : N(Q) = DN(Q)}` Borel?  Zero/positive-entropy conjectures for dynamically generated Cantor series | Open | none | | 5% |
| 14 | Algom 2504.18192 "Some open problems" section | Effective rates; pointwise β-normality beyond Pisot; Rajchman ⇒ normal in Pisot bases | Open | none | | 5% |
| 15 | Lai-Xie 2601.03402 "Discussions and open problems" | Qu 1-3: Moran sets supporting pointwise absolutely normal measures; gauge-function largeness | Open | none | | 5% |
| 16 | Erdős #249 | Is `Σ φ(n)/2ⁿ` irrational? | Open | Lambert ladder (signed) | `Σ φ(n)/2ⁿ = Σ_d μ(d) 2ᵈ/(2ᵈ−1)²`: signed and with growing coefficients, so the gap/carry arguments of the ladder do not apply | 5% |
| 17 | Andrieu-Eliahou-Vivion 2510.11723 Conjecture `conj:normality`, Question on AMS18 Problem 71 | Minimal and maximal rational-base words are normal; all minimal words are finite-state equivalent (AMS18 Problem 71) | Open; the conjecture implies Mahler's `Z`-number conjecture | none | | 2% |
| 18 | Mendonça 2604.17136 | Is `0.F₁F₂F₃…` normal? | Open | none | Reduced in the paper to `(ε,k)`-normality of almost all `F_n`, deep-digit equidistribution of `φⁿ` | 3% |
| 19 | Erdős #1049 | Is `Σ 1/(tⁿ−1)` irrational for rational `t > 1`? | Open (Erdős: integer `t`) | E_b machinery is integer-base only | | 3% |
| 20 | Erdős #406; Roettger-Ren 2511.03861 | Finitely many powers of 2 with only digits 0, 1 in base 3; uniform ternary digit distribution of `2ⁿ` | Open | none | Lagarias-type 3-adic dynamics | 2% |

## Already answered (9 found)

| Source | Question | Answered by |
|---|---|---|
| Campbell 2605.24160 §Conclusion | "whether or not *every* binary string appears infinitely often in the base-2 expansion of `E`" | **This repo**, unmerged: `jointWords_quantitative` (branch `proof/joint-lambert-unconditional`, checkout `normal-numbers-lambert`), bases `≥ 2` including 2, count `≥ N exp(−C(log log N)² log log log N)`; scalar case also in CaptainSude's `erdos-borwein-disjunctivity` paper (GitHub, read at the pin cited in `docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md` §7).  `papers followups` shows 0 citing papers, so Campbell has likely not seen either |
| Crandall 2012 (restated in 2605.24160 §1) | Does `11` occur infinitely often in binary `E`? | Campbell 2605.24160 (and the repo result above) |
| Bergelson-Downarowicz 2506.12929 open-problem list, item 1 | "Is the reciprocal of a normal number always normal?" | No: Manai 2609.24665 theorem `thm:2`, every locally `C²` normality preserver is affine, and `x ↦ 1/x` is not |
| Bergelson-Downarowicz item 6 | "Are there irrational numbers `a` with the property that `ax` is normal for all normal `x`?" | No: Dayan-Ganguly-Weiss, reproved as Manai 2609.24665 theorem `thm:1` |
| Manai 2506.15422 §1 (existence form) | a normal `x` with `x²` not normal | Exists by 2609.24665 theorem `thm:2`; the explicit form is row 3 |
| Erdős #69 | `Σ ω(n)/2ⁿ` irrational | Tao-Teräväinen 2512.01739, theorem `thm:irrational` ("Erdős #69") |
| Shmerkin (personal comm., in 2607.06773) | non-uniform limiting frequencies in one base, normal in the independent bases | Becher-Lew Deveali 2607.06773 theorem `thm:3` |
| Mayordomo 2025 (in 2602.01199) | characterize `f`-normality by equidistribution of `(|Σ|ⁿ a_nᶠ(x))` | No in general: Pulari 2602.01199 theorem `thm:negative` |
| Campbell 2603.04396 §1 | does an abelian-normal, non-normal number exist? | Yes, decimal, in the same paper (v1 2026-03-04) |

⚠️ **Priority note for H5.**  Campbell 2603.04396 (v1 2026-03-04, v2 2026-08-21) constructs an
explicit abelian-normal non-normal *decimal* number.  This predates the repo's binary
`exists_abelianNormal_not_normal` (C4 campaign, closed 2026-09-25).  Different base and
different construction, so it is a parallel result, but `Literature.lean` should cite it and no
outward text should claim the existence statement as first.

## Per-candidate detail

### 1. Erdős #257 for `A = k·S`, `k ≥ 2` (90%)

**Source.**  erdosproblems.com/257 (page edited 15 April 2026), `[Er68d]`, `[ErGr80, p.62]`:
"Let `A ⊆ ℕ` be an infinite set. Is `Σ_{n∈A} 1/(2ⁿ−1)` irrational?"  The page adds: "There is
nothing special about 2 here, and this sum is likely irrational with 2 replaced by any integer
`t ≥ 2`."  Tao-Teräväinen 2512.01739v2, §1 subsection "An irrationality result": "It seems likely that the arguments in this paper can
also treat other sets `A` that are sufficiently similar to the primes, but we do not pursue this
question here.  The method can also be modified to establish the irrationality of
`Σ ω(n)/bⁿ` for any integer base `b ≥ 2`."

**Status.**  Open in general, and Kovač (forum, 2025-08-25) expects the universal statement to
be *false* at base 2, since the subsum set is a fat Cantor set.  The live case map (problem page,
forum, `formal-conjectures` `257.lean` and open PRs #6528/#6529 by wcook04, the Plectis
`erdos257-mersenne-reasoning-surface.md`) covers: `A = ℕ` (Erdős 1948), pairwise-coprime with
`Σ 1/a < ∞` (Erdős 1968), summable supports without coprimality (Plectis/Astra averaging note),
finite-prime weighted-summable and mixed-cover supports (Plectis), eventually periodic supports
(Luca-Tachiya), factorials and powers of 2 (Erdős-Straus), primes and prime powers
(Tao-Teräväinen).  Plectis Remark 6 confirms nothing for divergent non-prime supports.  The
weighted criterion does not reach `2·primes`: with prime set `{2}` the weight of `a = 2p` is
`1/(p(2²−1))`, whose sum diverges.  **No source lists `A = k·S` for a divergent prime set `S`.**

**Machinery.**  The content is already in the repo:
- `G4SubsetAssembly.isDisjunctive_subsetLambert`: for `S` with `MertensRate S c C`
  (`Σ_{p≤N, p∈S} 1/p ≥ c log log N − C`) and `b ≥ 3`, `subsetLambert S b` is disjunctive in base
  `b`, with the residue-class instance `isDisjunctive_residueClass_primeSum`.
- `FamilyGraded.isNormal_subsetLambert_of_sqrtFreshMassZero` (C′): `SqrtFreshMassZero P` and
  `DivergentRecip P` give `IsNormal 4 (subsetLambert P 4)`.
- `PowerBaseReal`: normal in base 4 ⟺ normal in base 2.

**Mechanism.**  `Σ_{n∈kS} 1/(2ⁿ−1) = Σ_{p∈S} 1/((2ᵏ)ᵖ−1) = subsetLambert S (2ᵏ)` by reindexing
along the injection `p ↦ kp`.  Then:
1. For every `k ≥ 2` and every Mertens-rate `S` (all primes, every reduced residue class), the
   `#257` sum is disjunctive in base `2ᵏ`, hence irrational.  `k = 2`, `S` = all primes is the
   base-4 case TT call "a modification"; residue classes and general Mertens-rate sets are
   unrecorded anywhere found.
2. For `k = 2` and every C′ set `P` (divergent, square-root fresh mass `→ 0`), the `#257` sum is
   **normal in base 2**.  This is a frequency statement, much stronger than irrationality, for an
   explicit `#257` support with divergent reciprocal sum.
The Lean deliverable is one reindexing lemma plus two corollaries stated in the exact
`formal-conjectures` shape `Irrational (∑' n : A, (1:ℝ)/(2^n.1 − 1))`.

**Novelty check owed.**  A `gh pr list --search` on `formal-conjectures` and a reread of the
#257 forum thread on the day of writing; this sweep found no match as of 2026-10-02.  Whether to
offer the variant upstream (Google CLA repo: no `Co-Authored-By: Claude` trailer) is Trevor's call.

### 2. Erdős #257 at base 2 for prime subsets (25%)

**Statement.**  As row 1 with `k = 1`: `A = S ⊆ primes`, `S` a residue class or Mertens-rate set,
the case TT call "likely" and do not pursue.

**Machinery and wall.**  `docs/prime-lambert-disjunctivity-fixed-base.md` (5): the fixed-base
error is `(2^{5/4}/b)^K`, which tends to 0 exactly when `b ≥ 3`, "For `b = 2`, this bound does
not tend to zero, so it does not remove the binary two-point input."  The binary draft
(`docs/prime-lambert-disjunctivity-draft.md`) runs on an external quantitative two-point
correlation theorem.  For `S` a residue class the needed input is the TT correlation estimate for
`ω_S`, or a twisted version of the repo's two-point log-Elliott (Elliott front, one hypothesis
left).  Hughes 2609.28526 (effective logarithmic two-point Chowla, 2026-09-22, a forward citation
of TT) is the newest input to read first.  Irrationality alone may be cheaper than
disjunctivity: TT's own route is a digit-gap contradiction, so the repo should first check
whether TT's irrationality section (`irrational-sec`) goes through for `ω_S` with only Mertens in progressions.

### 3. Explicit normal `x` with `x²` non-normal (20%)

**Source.**  Manai 2506.15422v5 §1: "it would be very interesting to determine a normal number
`x` such that `x²` is not normal - mimicking the conjectured property of `√2`."  Manai
2508.09319v4, Definition `def:deg` (`deg_an(x)` = least degree of an integer polynomial `p` with `p(x)`
not normal) and the open problem after it: "Show that the sets `Ω_k` are of Hausdorff dimension 1
(or at least of positive Hausdorff dimension). Construct an explicit number `x ∈ Ω_k` for all
(some) `k ∈ ℕ`."

**Status.**  Existence of a normal `x` with `x²` non-normal (and so `Ω₂ ≠ ∅` in a fixed base,
since Wall rational handles degree 1) follows from Manai 2609.24665 theorem `thm:2` via Baker-Banaji;
that proof is measure-theoretic and gives no explicit `x`.

**Mechanism sketch.**  Take the sparse Cantor set `C(S)` of 2607.06773 (base-2 digits 1 only on a
sparse `S`): every `y ∈ C(S)` is deterministic and non-normal in base 2.  Prove that for the
non-identical Bernoulli measure `μ` on `C(S)`, `√y` is `μ`-a.s. normal in base 2, by bounding
`Σ_n e(h 2ⁿ √y)` through the Fourier transform of `√_*μ` (nonvanishing second derivative gives
the curvature that Baker-Banaji use in the self-similar case).  Then derandomize exactly as
Becher-Lew Deveali do (their `thm:3` algorithm), outputting `x = √y`.  The hard step is the decay
of `√_*μ` on a dimension-zero support; 2607.06773 proves only the linear (odd-base) analogue.

### 4. Finite-state relabelings and `f`-normality (15%)

**Source.**  Pulari 2602.01199v2, "Discussion and open questions": "It would be interesting to determine whether some weaker
condition (e.g. levelwise surjectivity or bounded-to-one behavior on each `Σⁿ`) suffices for the
same equidistribution characterization, or whether non-invertible finite-state relabelings can
already break it."  **Machinery.**  The repo's transducer run-state infrastructure
(`runState`/`runClock`, §7 campaign) is CF-specific but the state-tracking lemmas are generic.
A negative answer by an explicit two-state bounded-to-one relabeling is the likelier outcome.

### 5. Reciprocals of deterministic numbers (15%)

**Source.**  Bergelson-Downarowicz 2506.12929v1, subsection "Some natural open problems", item 2: "Is the reciprocal of a
nonzero deterministic number always deterministic?"; item 3: "Does there exist a normal number
whose reciprocal is deterministic?"; items 4, 5, 7 are the product/ratio representation
questions.  **Mechanism.**  One deterministic `y` with `1/y` normal settles 2 (no) and 3 (yes).
Same Cantor-set-plus-curvature plan as row 3 with `x ↦ 1/x`; the two rows share their hard
lemma, so do them together.

### 6. Odd-base non-normality and a fast algorithm in sparse Cantor sets (15%)

**Source.**  Becher-Lew Deveali 2607.06773v1, Introduction: "We do not know how to prove a similar result
for lack of normality in `C` for odd bases."  And: "The main obstacle to proving Theorem `thm:3` with a
direct adaptation of Schmidt's construction - which could possibly yield a polynomial-time
algorithm - lies in controlling the multiplicities of the residue classes `⌊ℓrⁿ/2ᵃ⌋ mod 2ᵏ` for
fixed positive integers `a, k`, odd `ℓ, r`, as `n` ranges over `0, …, 2ᵏ−1`."

**Machinery.**  That obstacle is a Korobov-type orbit count of `rⁿ` modulo `2ᵏ`, the computation
behind `isNormal_two_stoneham23` (`3ⁿ mod 2ᵏ`).  A heuristic check during this sweep: for
`x = Σ_{s∈S'} 2⁻ˢ` with super-lacunary `S'`, the base-3 digits between gaps are a full period of a
rational with denominator `2^{s_k}`, whose orbit `⟨3⟩ ≤ (ℤ/2^{s_k})ˣ` (the classes `≡ 1, 3 mod 8`)
is equidistributed at every scale above 8, so the obvious lacunary candidate looks *normal* in
base 3, not non-normal.  The multiplicity lemma for general odd `ℓ, r` is the tractable piece.

### 7-20

Rows 7-20 have no repo machinery that moves their crux; the table carries the quote location,
and the one-line mechanism where one was visible.  Row 16 (Erdős #249) is listed because it
looks like a Lambert-ladder constant and is not: the Möbius-signed form defeats the
non-negative-coefficient digit arguments every ladder theorem uses.

## Recommended next move

Row 1 is a one-lap wiring job on proved theorems and turns three closed campaigns into a
statement about a named Erdős problem, including a *normality* result for an explicit #257
support.  Rows 3 and 5 share one hard lemma (Fourier decay of a `C²` pushforward of a sparse
Bernoulli measure) and are the best genuinely new-math pair the sweep found outside the
prime-Lambert line.
