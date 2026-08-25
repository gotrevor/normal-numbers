# The irregularity landscape

*What "irrational", "transcendental" and "normal" each claim, how they sit relative to
one another, and which of those relationships are formalizable here.  Written 2026-08-24
after a status ledger for a constant read `irrational: trivial; transcendental: known;`
and the natural next question was where normality goes on the same page.*

Companion: `docs/how-irregular-is-a-number.html` (the same material with the diagrams).

## 1.  Three claims, two subjects

| Claim | Subject | Why the cost differs |
|---|---|---|
| irrational | relation to `ℚ` | one algebraic relation ruled out; for a digit-concatenation constant it is visible in the construction, hence *trivial* |
| transcendental | relation to `ℚ` | still one relation, but a whole family at once; for Champernowne it is Mahler 1937, hence *known*, meaning **cited** rather than **observed** |
| normal | statistics of one expansion | an infinite family of statistical constraints, separately in every base; nothing turns a closed form into control over digit frequencies |

The first two are arithmetic.  The third is not, and it is base-relative, so it **crosses**
the algebraic/transcendental boundary instead of nesting inside it.

Edges that actually hold:

- `normal ⇒ irrational`.  This is the only implication among the three.
- `normal ⇏ transcendental` and `transcendental ⇏ normal`.  Champernowne is both;
  Liouville's constant is transcendental and normal to no base; Bugeaud (2002) built
  Liouville numbers that are absolutely normal.
- **algebraic ∧ normal: no known member, conjecturally everything.**  Borel (1950)
  conjectured every algebraic irrational is absolutely normal, and not one has ever been
  shown normal in any base.  This is the sharpest fact on the page.

## 2.  Already formalized

Mathlib, at the pinned rev (`0df444a360eaa60ab8c11dca51a86af692955474`, v4.33.1):

| Notion | Where |
|---|---|
| `Irrational` | `Mathlib/NumberTheory/Real/Irrational.lean` |
| `Transcendental` | `Mathlib/RingTheory/Algebraic/Defs.lean` |
| `Liouville`, `Liouville.transcendental` | `Mathlib/NumberTheory/Transcendental/Liouville/Basic.lean` |
| `LiouvilleWith p x` (the exponent as a predicate family) | `.../Liouville/LiouvilleWith.lean` |
| Liouville set is null, and is residual | `.../Liouville/Measure.lean`, `.../Liouville/Residual.lean` |
| `dimH` (Hausdorff dimension) | `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` |

This repo:

| Notion | Where |
|---|---|
| `IsNormal b x`, `IsNormalSequence b s`, `digit`, `Visits` | `RealDefs.lean`, `SeqDefs.lean` |
| `Equidistributed` (mathlib has no equidistribution API) | `RealDefs.lean` |
| `IsAbsolutelyNormal`, `IsCFNormal`, `KhinchinTypical` | `Headline.lean` |
| Wall's theorem, Bailey-Crandall, Stoneham base 2, Pillai, the B5' witness | `Wall.lean`, `LnTwo.lean`, `Stoneham.lean`, `Pillai.lean`, `Headline.lean` |

So mathlib owns the arithmetic axis and this repo owns the expansion axis.  Nothing
anywhere connects them.

## 3.  The ledger: what is missing, and what it would cost

Ordered by (value to this repo) / (cost).

| # | Statement | Cost | Verdict |
|---|---|---|---|
| 1 | `IsNormal b x → Irrational x` | **cheap.**  Wall is already proved, and a rational `x` has a finite forward orbit `{bⁿx mod 1}`, so it cannot be equidistributed.  Pick an interval shorter than the smallest gap and its visit frequency is 0 | **do it.**  It is the only implication in the whole picture and the repo does not have it |
| 2 | Borel 1909: almost every real is absolutely normal | **moderate.**  Borel-Cantelli and the strong law are both in mathlib, and the repo already carries `∀ᵐ` machinery for the Gauss measure | **do it.**  The most famous statement about normal numbers, and the repo currently proves a witness exists without proving witnesses are typical |
| 3 | The dual: absolutely normal numbers are meager | **cheap.**  A short Baire-category argument, and mathlib's `Residual` file for Liouville numbers is the template | **do it,** next to 2.  The pair is the measure-versus-category punchline |
| 4 | The weak hierarchy: disjunctive < simply normal < normal base `b` < absolutely normal, with a separating witness at each step | **moderate.**  Definitions are quantifier weakenings of what exists; the work is the counterexamples | **do it.**  It is what makes the repo's headline legible: it says what `IsAbsolutelyNormal` is *stronger than* |
| 5 | Stoneham `α₂,₃` is **not** normal base 6 (Bailey-Borwein) | **moderate,** and partly scaffolded already (`HotSpot.lean`, `papers/bailey-misiurewicz-2006-hot-spot.md`) | **do it.**  The single sharpest proof that normality is base-relative, and half of it is already here |
| 6 | `irrationalityExponent x := sSup {p | LiouvilleWith p x}` plus the easy endpoints (`= ∞` for Liouville, `≥ 2` always) | **cheap** for the definition and the endpoints | **optional.**  Useful only as the anchor for the second axis; the interesting values need Roth or Mahler |
| 7 | Morse-Hedlund: bounded subword complexity iff eventually periodic | **moderate,** self-contained combinatorics on words | **optional.**  A second irregularity scalar, but it pulls the repo toward word combinatorics |
| 8 | Eggleston 1949: the digit-frequency class has `dimH = H(p)/log b` | **hard,** dominated by building a Hausdorff-dimension toolkit (`dimH` exists but is thin; no mass distribution principle) | **not now.**  The corollary "non-normal numbers have full dimension" is the part worth wanting |
| 9 | **Schnorr-Stimm: normal iff finite-state dimension 1** | **an expedition.**  Needs finite-state gamblers, `s`-gales, and the equivalence.  Weeks, self-contained, no mathlib wall | **the standout candidate.**  It is the bridge from the statistics axis to the information axis, it is squarely about normality, and a survey has not turned up a formalization in any prover (grep tier, not a search of the literature) |

## 4.  Recommendation: make the diagram a Lean file

A `src/NormalNumbers/Landscape/` module whose contents are exactly the arrows and regions
of the diagram, importing mathlib's `Irrational` / `Liouville` on one side and this repo's
`IsNormal` on the other.  Items 1 through 5 above are its first five files.  Every edge in
the picture becomes either a theorem or a documented `-- open` with the reason, which makes
the module self-auditing: an edge with neither is a gap someone has to name.

That fences the work cleanly.  The repo keeps proving hard witnesses; `Landscape/` says
what the witnesses mean.

## 5.  Walls, named so nobody re-derives them

- **Roth 1955** (every algebraic irrational has irrationality exponent 2).  Not in mathlib,
  and a headline formalization in its own right.
- **Adamczewski-Bugeaud** (algebraic irrationals have superlinear subword complexity).
  Rides on the Schmidt subspace theorem, which is not in mathlib.
- **Mahler's A/S/T/U classification.**  The definitions are easy and the only interesting
  theorem (T-numbers exist, Schmidt 1968) is very hard.
- **Martin-Löf randomness implies absolute normality.**  Needs an effective-measure-theory
  layer that does not exist in mathlib.  A neighbouring continent, not an extension.

## 6.  Evidence tiers for the absence claims above

"Not in mathlib" here means **greps clean** at rev `0df444a` (2026-08-24), not a proof of
absence: no `Roth`, no equidistribution API, no Kolmogorov complexity, no normality.
"Not in this repo" for Borel 1909 is the same tier.  Before starting any item, re-check,
including open mathlib PRs: `master` is a ref but it is not the frontier.
