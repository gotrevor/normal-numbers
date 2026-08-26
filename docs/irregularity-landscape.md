# The irregularity landscape

*What "irrational", "transcendental" and "normal" each claim, how they sit relative to
one another, and which of those relationships are formalizable here.  Written 2026-08-24
after a status ledger for a constant read `irrational: trivial; transcendental: known;`
and the natural next question was where normality goes on the same page.*

Companion: `docs/how-irregular-is-a-number.html` (the same material with the diagrams, including
the full digit-side implication lattice from `Irrational` up to 2-randomness).
Prior art worth knowing: Numberphile's *All the Numbers* draws the same crossing by hand
(<https://www.youtube.com/watch?v=5TkIe60y2GI>, at 8:23), and gets the key detail right, that the
normal circle overlaps algebraic and computable but never meets the rationals.

## 1.  Four claims, three subjects

| Claim | Subject | Why the cost differs |
|---|---|---|
| irrational | relation to `ℚ` | one algebraic relation ruled out; for a digit-concatenation constant it is visible in the construction, hence *trivial* |
| transcendental | relation to `ℚ` | still one relation, but a whole family at once; for Champernowne it is Mahler 1937, hence *known*, meaning **cited** rather than **observed** |
| normal | statistics of one expansion | an infinite family of statistical constraints, separately in every base; nothing turns a closed form into control over digit frequencies |
| computable | what it costs to *produce* the digits | Turing 1936: is there an algorithm for digit `n`?  Answered yes before it is asked, for every constant anyone names, hence *free* |

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

## 1b.  The computability axis, which sits underneath both

Added 2026-08-25.  It was under-weighted in the first pass of this doc and of the HTML page,
and it deserves its own section because it is the axis that explains the shape of the others.

`x` is **computable** if some algorithm, given `n`, returns the `n`th digit.

- **The one edge to the arithmetic axis: `uncomputable ⇒ transcendental`, hence irrational.**
  Every rational is computable and every algebraic number is computable (isolate the roots
  of its minimal polynomial to any precision), so anything uncomputable is outside both.
  One way only: `π` is transcendental and computable, so the converse fails as widely as
  a converse can.
- **There is no such thing as an uncomputable integer.**  Uncomputability is a property of
  *infinite* objects; every finite object is printed by the program that prints it.  The
  busy beaver *function* is uncomputable (Radó 1962), but each value `BB(n)` is one
  particular integer and is therefore computable.  What is true: O'Rear's 748-state machine
  halts exactly when ZFC is inconsistent (sharpening Yedidia–Aaronson's 7910), so if ZFC is
  consistent it cannot pin down `BB(748)`.  A program printing that integer exists; no
  theory we trust can say which one.  *Computable* quantifies over algorithms that exist,
  not algorithms we can find.
- **Countably many programs, so countably many computable reals: measure zero.**  Every
  "almost every real is …" theorem on the page is therefore silent about every number
  anyone has ever named.  Borel 1909 says nothing whatsoever about `π`, and that is
  structural, not a weakness of the proof.
- **The ceiling.**  No computable real is random in *any* effective sense, down to the
  weakest rung: for computable `x`, `{x}` is a `Π⁰₁` null class, so `x` is not even Kurtz
  random.  **Absolute normality is the top of what a computable number can reach**, which
  is the same fact as Champernowne having finite-state dimension `1` (maximal) and
  effective Hausdorff dimension `0` (minimal), since `K(x↾n) = O(log n)` for anything a
  program prints.
- **Effectivizing is the history of the subject.**  Sierpiński 1917 constructed an
  absolutely normal number; Turing wrote an algorithm around 1937 (unpublished until 1992,
  with a gap); a genuinely computable example is Becher–Figueira 2002; polynomial time is
  Becher–Heiber–Slaman 2013.  The B5′ witness here is of exactly that kind: the content is
  not that such a number exists but that a program prints it.

Formalization status of this axis, at the pinned rev:

| Claim | In Lean |
|---|---|
| halting problem undecidable | mathlib, `ComputablePred.halting_problem` |
| countably many programs | mathlib, `Nat.Partrec.Code.instDenumerable` |
| Turing degrees as a partial order | mathlib, `TuringDegree` (on `ℕ →. ℕ`, not on reals) |
| `algebraic ⇒ computable` | **not yet.** `Computable` lives on encodable types and `ℝ` is not one, so "computable real" has to be defined first |
| computable reals are null | **not yet**, same blocker |
| a computable absolutely normal number exists | **not yet.**  ⚠️ Be exact here: our witness is an explicit construction, but *computability of it* is not part of any formal statement in this repo, so the row is open however suggestive the Lean looks |
| no computable real is Kurtz random | **not yet**, needs the same effective-measure layer as the Schnorr row |

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
| `IsDisjunctive`, `AbsolutelyDisjunctive`, `OccursAt`; word occurrence ⟺ dense orbit; positive base-power invariance | `Disjunctive.lean` |
| absolutely disjunctive reals are residual; normal-in-base-`b` reals are meagre | `DisjunctiveBaire.lean`, `NormalMeager.lean` |
| a real disjunctive in every base and normal in no base exists | `exists_absolutelyDisjunctive_forall_not_isNormal` |
| Wall's theorem, Bailey-Crandall, Stoneham base 2, Pillai, the B5' witness | `Wall.lean`, `LnTwo.lean`, `Stoneham.lean`, `Pillai.lean`, `Headline.lean` |

So mathlib owns the arithmetic axis and this repo owns the expansion axis.  Nothing
anywhere connects them.

## 3.  The ledger: what is missing, and what it would cost

Ordered by (value to this repo) / (cost).

| # | Statement | Cost | Verdict |
|---|---|---|---|
| 1 | `IsNormal b x → Irrational x` | **cheap.**  Wall is already proved, and a rational `x` has a finite forward orbit `{bⁿx mod 1}`, so it cannot be equidistributed.  Pick an interval shorter than the smallest gap and its visit frequency is 0 | **do it.**  It is the only implication in the whole picture and the repo does not have it |
| 2 | Borel 1909: almost every real is absolutely normal | **moderate.**  Borel-Cantelli and the strong law are both in mathlib, and the repo already carries `∀ᵐ` machinery for the Gauss measure | **do it.**  The most famous statement about normal numbers, and the repo currently proves a witness exists without proving witnesses are typical |
| 3 | The dual: normal-in-base-`b` numbers are meagre (hence absolutely normal numbers are meagre) | **shipped.**  `isMeagre_setOf_isNormal` uses dense open long-zero-run cylinders and Wall's theorem | **proved** in `NormalMeager.lean` |
| 4 | The weakenings below normality, **which are not a chain**: `normal b → disjunctive b` and `normal b → simplyNormal b`, with neither weakening implying the other, and `disjunctive b → Irrational` while simple normality does **not** force irrationality (`1/3 = 0.010101… ` in base 2 is simply normal and rational) | **partial.**  `IsDisjunctive` and its dense-orbit equivalence are formalized; `exists_absolutelyDisjunctive_forall_not_isNormal` gives the generic separation `disjunctive ⇏ normal`.  The other arrows and witnesses remain | **continue.**  The shipped separation is the first edge; the full not-a-chain diagram is still open |
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

## 4b.  Yes, state *every* edge, including the trivial ones

The trivial containments are in mathlib already, but they are there as **instances and coercion
lemmas**, not as edges of this lattice: `isAlgebraic_ratCast` (every rational is algebraic),
the `ℚ → ℝ` coercion, `Irrational` as `x ∉ Set.range ((↑) : ℚ → ℝ)`, `Liouville.transcendental`,
`transcendental_liouvilleNumber`, `irrational_sqrt_two`.  Restating each as an edge costs about a
line, and that is the point: a module where the cheap edges are *missing* is not a diagram, it is a
pile of the interesting facts, and a reader cannot tell a gap from an omission.

**The discipline that makes it finite.**  For every ordered pair of notions in the lattice, the
module says exactly one of three things:

The companion HTML now renders this as a **status board**: one row per claim, with the
mathematical status and the formalization status in separate columns, because they answer
different questions and only one of them is a work plan.  The three verdicts are:

1. **proved** - a theorem, however one-line;
2. **refuted** - a theorem of the form `¬ ∀ x, P x → Q x`, which needs a *witness*, and this is
   where the real work is;
3. **open** - a documented `-- open` with the reason and the citation.

Transitivity collapses the quadratic pair count to the covering relations plus the non-edges, so
the target is finite and small.  The witnesses the refutations need, all of them already named in
this repo's literature: Champernowne (normal, computable, so not Kurtz random), `1/3` in base 2
(simply normal, rational), Liouville's `λ` (transcendental, normal to no base), Bugeaud's number
(Liouville and absolutely normal), Stoneham `α₂,₃` (normal base 2, not base 6), Thue-Morse (not
disjunctive).  Every non-edge in the diagram is a construction someone has already published.

**A finding that fell out of checking this, corrected.**  A first grep suggested nothing anywhere
proves `π` transcendental.  That was an instrument failure: it searched mathlib only.  What is
actually true, from mathlib's own scoreboard (`docs/100.yaml` at rev `0df444a`) and this machine:

| Theorem | mathlib | elsewhere |
|---|---|---|
| `e` transcendental (Freek #67) | none | claimed in `100.yaml` via external `url:`, Jujian Zhang, **Lean 3** (`jjaassoonn/transcendental`).  We also have a Lean 4 proof |
| `π` transcendental (Freek #53) | **entry has no `decl` and no `links`: an unclaimed slot** | `transcendental_pi_axiomClean` in `gotrevor/lean-formalizations`, `NumberTheory/Transcendence/PiTranscendental.lean:24` |
| Hermite-Lindemann (Freek #56) | entry blank | `NumberTheory/Transcendence/HermiteLindemann.lean`, same repo |
| Lindemann-Weierstrass (`1000.yaml` Q1572474) | a comment pointing at PR #6718, which is **CLOSED** (Zhao Yuyang, last touched 2025-08-17) | - |

So mathlib genuinely lacks both, the closest in-flight attempt is a closed PR, and we proved both
in Lean 4 on 2026-06-16, axiom-clean, discharging and deleting the `hermite_lindemann` axiom on the
way (`STATUS.md`, lap 14, `cd5a8ce`, math-axiom count 0).  Background and the proof architecture:
`knowledge/core/projects/lean-journey/reference/2026-06-16-pi-transcendence-full-lindemann-assembly.md`.

**The consequence worth acting on.**  Freek #53 is an *unclaimed slot on mathlib's own board* and we
hold an axiom-clean proof of it.  The route is already paved and is not a mathematics PR: append
`url:` + `authors:` to the `100.yaml` entry, exactly as was done for Goodstein and Kirby-Paris
(`decisions/mathlib-1000-yaml-claim.md`, fork PR then Trevor fires upstream).  One blocker:
`lean-formalizations` is **private**, and a claim URL has to resolve.  `lean-gallery` is public, so
this needs the same publish decision that the Erdős absorptions are waiting on.

⚠️ Evidence tiers: the mathlib absence is `100.yaml`/`1000.yaml` tier, which is the community's own
tracker rather than a grep.  Our two theorems are `STATUS.md` + `#print axioms` tier as of
2026-06-19; the repo is mid-bump to v4.33.1, so re-run the axiom sweep before quoting it outward.

## 5.  Walls, named so nobody re-derives them

- **Roth 1955** (every algebraic irrational has irrationality exponent 2).  Not in mathlib,
  and a headline formalization in its own right.
- **Adamczewski-Bugeaud** (algebraic irrationals have superlinear subword complexity).
  Rides on the Schmidt subspace theorem, which is not in mathlib.
- **Mahler's A/S/T/U classification.**  The definitions are easy and the only interesting
  theorem (T-numbers exist, Schmidt 1968) is very hard.
- **The effective randomness ladder** (Kurtz < Schnorr < computably random < Martin-Löf < 2-random,
  each strictly stronger).  Schnorr randomness already implies absolute normality, so the ladder
  sits *above* this repo's subject and reaches it by one bridge.  Formalizing any of it needs an
  effective-measure-theory layer that mathlib does not have: a neighbouring continent, not an
  extension.  ⚠️ Normality is **not** a rung on that ladder: it neither implies nor is implied by
  Kurtz randomness (Champernowne is normal and computable, so no effective notion touches it).
  The unifying statement, worth knowing even without formalizing it: each rung is *no gambler of
  this class wins betting on the next digit*, and normality is the finite-memory case
  (Schnorr-Stimm 1972).

## 6.  Evidence tiers for the absence claims above

"Not in mathlib" here means **greps clean** at rev `0df444a` (2026-08-24), not a proof of
absence: no `Roth`, no equidistribution API, no Kolmogorov complexity, no normality.
"Not in this repo" for Borel 1909 is the same tier.  Before starting any item, re-check,
including open mathlib PRs: `master` is a ref but it is not the frontier.
