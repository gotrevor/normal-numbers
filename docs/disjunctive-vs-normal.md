# Disjunctive vs normal: where the weaker property actually knows more 🔓

Sibling of [irregularity-landscape.md](irregularity-landscape.md), which places `disjunctive` as
the outermost of the three nested expansion rings.  This file answers the follow-up question: is
the outer ring *only* weaker, or is there a body of results that lives there and provably cannot
live on the normality ring?

**BLUF.**  Yes, there is, and it has a single explanation: disjunctive is the *topological* shadow
of normality, so every theorem below is topological rigidity standing in for a measure-rigidity
statement that is open or vacuous.  Two flagship results (Mahler 1973, Furstenberg 1967).  But the
outer ring buys **nothing** for algebraic numbers or named constants: for those, disjunctivity is
exactly as dead as normality, and in the sharpest sense it is the *same* conjecture.

## 0.  Definitions and the reframing that explains everything

`x` is **disjunctive in base b** (also *rich*, also *b-lexicon*) if every finite base-`b` word
occurs in its expansion.  **Absolutely disjunctive** = disjunctive in every base `b ≥ 2`, also
called a **lexicon** (Calude-Zamfirescu).

The reframing:

| property | orbit statement | tool |
|---|---|---|
| disjunctive in base `b` | `{bⁿx mod 1}` is **dense** in `[0,1]` | topological dynamics, Baire category |
| normal in base `b` | `{bⁿx mod 1}` is **equidistributed** | ergodic theory, measure rigidity |

Everything in §1 is an instance of "the dense version is a theorem, the equidistributed version is
open or empty."

**Base-power freedom is free here.**  `x` disjunctive in base `b` ⟺ disjunctive in base `bᵏ`.
The `⟸` direction is padding.  For `⟹`, given a base-`bᵏ` word `U` corresponding to a base-`b`
word `u` of length `km`, apply disjunctivity to the single word

```
V = u d u d u d … u          (k copies of u, separated by one arbitrary digit d)
```

If `V` occurs at position `p`, then `u` occurs at each `p + i(km+1)` for `i = 0..k-1`, and since
`km + 1 ≡ 1 (mod k)` those positions sweep **every** residue class mod `k`, so one of them is
`k`-aligned.  Elementary; the normality analogue is Maxfield's theorem, a real (if not deep) one.
Consequence: the only free structure on the disjunctive side is the multiplicative-class structure,
same as for normality.

## 1.  What the outer ring knows that the inner ring does not

### 1.1  Mahler 1973 (Theorem M), sharpened by Berend-Boshernitzan 🏆

> For **any** real irrational `α`, any base `g`, and any block `W` of `k` digits, there is an
> integer `m` such that the base-`g` expansion of `mα` contains `W` infinitely often.

Mahler's bound is `m ≤ g^(2k+1)`; Berend-Boshernitzan improved it to `2g^(k+1)` and showed one
cannot do better than `g^k - 1`.  (Reported in Waldschmidt, *Words and Transcendence*, §1, refs
[3, Theorem M], [50], [26].)

**Why this cannot exist on the normality side.**  Wall (1949): normality in base `g` is invariant
under `x ↦ (p/q)x + r` for rationals.  So "choose `m` making `mα` normal" is not a hard theorem,
it is a *non-statement*: `mα` is normal iff `α` is.  Mahler's theorem is only possible because
occurrence-of-a-block is **not** multiplication-invariant, and the `g^k - 1` lower bound is the
proof that it genuinely is not.  This is the cleanest single answer to "does disjunctive know more."

### 1.2  Furstenberg 1967: ×2 ×3 topological rigidity 🌀

> Every closed `×2`- and `×3`-invariant subset of `[0,1]` is finite or everything.  Hence for
> every irrational `x`, the orbit `{2^m 3^n x mod 1}` is **dense**.

The measure version, Furstenberg's `×p ×q` conjecture (every non-atomic ergodic jointly invariant
measure is Lebesgue), has been open since 1967; Rudolph (1990) and Johnson settled only the
positive-entropy case.  So the dense statement is a nearly-60-year-old theorem and the
equidistributed statement is a famous open problem.  This is the single sharpest illustration that
the disjunctive side is more tractable.

Note what it does **not** give: density of the single-base orbit `{bⁿx}`.  A `×b`-orbit closure can
be a proper subshift (any Cantor set of admissible words), so plenty of irrationals are
non-disjunctive in base `b`.

### 1.3  Genericity and descriptive complexity 📐

- Disjunctive in base `b` is `Π⁰₂`: `∀w ∃n (w occurs at n)`.  The set is **comeager and of full
  measure**.
- Normal in base `b` is `Π⁰₃`-complete (Ki-Linton 1994), full measure but **meager**.  Absolutely
  normal is `Π⁰₃`-complete too (Becher-Heiber-Slaman, settling a Kechris conjecture); normal in at
  least one base is `Σ⁰₄`-complete (Becher-Slaman).

So the disjunctive set is large in *both* senses and the normal set in only one.  That difference
is exactly the source of the cheap constructions in §3, and of Calude-Zamfirescu's slogan: *the
typical number is a lexicon*, i.e. most numbers obey no probability law at all.

### 1.4  Construction cost 💸

There is a paper titled *A Simple Construction of Absolutely Disjunctive Liouville Numbers*
(Calude-Staiger), and Hertling (1996) already had disjunctive Liouville numbers with Staiger
strengthening to all bases.  Compare the normality side: a *computable* absolutely normal number
(Becher-Figueira) is famously "ridiculously exponential," a polynomial-time one took until
Becher-Heiber-Slaman 2013, and a computable absolutely normal **Liouville** number until 2015.

## 2.  Where the outer ring buys nothing: algebraic numbers 🚫

For algebraic irrationals the two rings collapse into one open problem.

Waldschmidt's **Conjecture 1.1**: for `x` real irrational algebraic, `g ≥ 3`, and a digit `a`, the
digit `a` occurs at least once in the base-`g` expansion of `x`.  He notes that Conjecture 1.1 for
all `(g,a)` is equivalent to "every block occurs infinitely often in every base," by the
powers-of-`g` argument of §0.  **So absolute disjunctivity of algebraic irrationals *is*
Conjecture 1.1.**  And, his words: there is *no explicitly known* triple `(g, a, x)` with `g ≥ 3`
and `x` algebraic irrational for which one can claim that digit `a` occurs infinitely often.

Adamczewski-Rampersad (PAMS 2008) put it more bluntly: the only blocks known to occur infinitely
often in the binary expansion of an irrational are `0`, `1`, `01`, `10`, and that is just
non-eventual-periodicity.  For any other word `W` and any fixed algebraic irrational, it is open.
What they *can* prove is about **patterns** rather than blocks:

- every algebraic number has infinitely many occurrences of `7/3`-powers in its binary expansion;
- in ternary, infinitely many squares, or infinitely many occurrences of `010` or of `02120`.

So the `π` / `e` / `ln 2` markers sitting on the outermost ring in the landscape diagram are
correctly placed, and moving them inward is not easier than proving normality in any known sense.

## 3.  "Disjunctive but normal in no base" is trivial, and here is the cheapest witness ✅

Three levels, all easy:

1. **One explicit number, one base.**  `ψ₂ = Σ_{i≥3} i · 2^(-i!)` (Nandakumar-Vangapelli).  For any
   binary string `w`, the string `1w` is the binary representation of some integer `i`, which is
   planted verbatim at position `i!`, so `ψ₂` is disjunctive in base 2.  It is not normal because
   the density of ones tends to 0.  That is the whole proof.
2. **Every base at once, by category.**  Absolutely disjunctive is comeager; normal-in-base-`b` is
   *meager*, so abnormal-in-base-`b` is comeager for each `b`; a countable intersection of comeager
   sets is comeager.  Hence `{absolutely disjunctive} ∩ {absolutely abnormal}` is **comeager**, in
   particular nonempty and uncountable.  This is essentially Calude-Zamfirescu.
3. **Computably.**  Nested intervals alternating two requirement families over all bases: "paste
   block `W` into the base-`b` expansion" and "run `0^N` in the base-`b` expansion."  Both moves are
   just descending into a `b`-adic subinterval, so the construction is effective.

Worth recording: **Martin's absolutely abnormal number is not a candidate for absolute
non-disjunctivity.**  His `α = Π_{j≥2}(1 - 1/d_j)` with `d_j = j^(d_{j-1}/(j-1))` is abnormal in
base `j` because the partial products are `j`-adic fractions, which forces a long run of the digit
`j - 1`.  That is a *frequency excess*, not a missing word.  Morally his `α` is probably absolutely
disjunctive.

## 4.  What is actually hanging out 🎯

### 4.1  Is `α_{2,3}` disjunctive in base 6?  (best tractability-per-context-we-own)

Bailey-Borwein (*Nonnormality of Stoneham constants*, Ramanujan J. 2012) prove `α_{b,c}` is not
`B`-normal for `B = b^p c^q r` when `D = c^(q/p) r^(1/p) / b^(c-1) < 1`, so `α_{2,3}` is not
6-normal.  **Their mechanism is an excess of long strings of zeros** (their proof ends by comparing
the observed rate of `M`-long zero runs against `1/B^M`), which is entirely compatible with every
block still occurring.  So their theorem says nothing about base-6 disjunctivity, and the question
appears untouched.

Why this is the right one to poke: we already own the `α_{2,3}` machinery in Lean, the base-2
normality proof is formalized, and disjunctivity in base 6 is a much weaker target than the
3-normality that Bailey-Borwein flag as open.  A **base-3 disjunctivity** statement may be
similarly reachable.  First move is cheap and empirical: compute a few million base-6 digits and
check block coverage against the expected coupon-collector curve, then look for a structural
argument from the `2^(3^n)` block structure.

### 4.2  Does there exist an irrational that is non-disjunctive in *every* base?

Equivalently: is every irrational disjunctive in some base?  The analogue of Martin's theorem, one
ring out.  Status after a literature sweep (2026-08-25): **not found either way**, and there are
two independent reasons to expect it is hard rather than overlooked.

- **Soft route, and the exact question to ask.**  `D = {x : disjunctive in ≥ 1 base}` is a countable
  union of `Π⁰₂` sets, so `Σ⁰₃`.  No rational is disjunctive, so "every irrational is disjunctive in
  some base" says exactly `D = ℝ ∖ ℚ`, a `Π⁰₂` set.  **Therefore a proof that `D` is
  `Σ⁰₃`-complete would settle the question negatively**, non-constructively producing an absolutely
  non-disjunctive irrational.  This is the precise analogue of Becher-Slaman's `Σ⁰₄`-completeness of
  "normal in at least one base."  I did not find this computed anywhere.
- **Hard route, and why the obvious attempts die.**  Non-disjunctive in base `b` means the
  `×b`-orbit closure is a proper subshift, so we are intersecting a proper `×2`-invariant closed set
  with a proper `×3`-invariant closed set, and so on for every multiplicative class.
  - *Furstenberg intersection* (conjecture, proved by Shmerkin and by Wu, 2019):
    `dim(A ∩ B) ≤ max(0, dim A + dim B - 1)` for multiplicatively independent invariant sets.  This
    kills only the low-dimension attempts.  Forbidding a word of length 100 costs almost no
    dimension, so the bound is toothless for long forbidden words, which is all we need.
  - *Host 1995* (Israel J. Math 91, 419-428): if `gcd(p,m) = 1` and `μ` is `T_p`-invariant, ergodic,
    with positive entropy, then `μ`-a.e. `x` is **normal in base `m`**.  So any positive-entropy
    measure supported on a base-2 forbidden-word set gives a.e. point normal, hence disjunctive, in
    base 3.  **Every measure-theoretic construction is therefore blocked**, and a witness must be a
    simultaneous exception to Host across all bases.
  - The structural reason underneath: you can freely choose the digits in **one** base, and the
    other bases are then determined and uncontrolled.  Missing a word is a tail condition on every
    digit forever, so it cannot be secured stage-by-stage the way a frequency anomaly can.

  Confidence it is genuinely open as stated: **75%**, with the residual being that it is folklore
  under vocabulary I did not hit.  ⚠️ Verify against a specialist before investing.

### 4.3  Named conditional axioms (the Hypothesis-A move, extended)

[`conditional-disjunctivity.md`](conditional-disjunctivity.md) names five axioms with elementary
implications to digit conclusions for specific constants: **Λ** (positive-measure ω-limit ⟹ ln 2
2-disjunctive, via a 0-1 law for closed forward-invariant sets), the **D_w** family (per-word orbit
accumulation ⟹ that word recurs in ln 2), **C** (carry rigidity ⟺ `11` recurs in √2), **T**
(lossless dyadic transfer ⟹ same), and **M** (invariant-set avoidance ⟹ quadratic irrationals
disjunctive; sharpens Mahler's 1984 Cantor-set question).  The §0 circle dictionary, Λ implication,
and full D_w conditional family are now formalized.  Novelty of all five is unswept.

### 4.4  Sharpen Mahler's `m`

`2g^(k+1)` (Berend-Boshernitzan) against the `g^k - 1` lower bound is a real gap, in an area that
is elementary and entirely unformalized.  Lower value than 4.1, but the cheapest to enter.

## 5.  Formal-side state

The 2026-08-25 pinned-mathlib and Lean Zulip sweeps found no prior
formalization of this corner.  This repo now supplies the first three rows and
the category-theoretic separation consequence; formalization novelty remains
hedged at that evidence tier.

| candidate | Lean state | tier |
|---|---|---|
| normal in `b` ⟹ disjunctive in `b` | **shipped:** `IsNormal.isDisjunctive` in `Disjunctive.lean`, extracting an occurrence from each positive limiting block frequency | low |
| absolutely disjunctive numbers are comeager (Calude-Zamfirescu) | **shipped:** `residual_absolutelyDisjunctive` in `DisjunctiveBaire.lean`; `isMeagre_setOf_isNormal` and `exists_absolutelyDisjunctive_forall_not_isNormal` in `NormalMeager.lean` formalize the stronger "lexicon with no statistics" conclusion | low |
| disjunctive in `b` ⟺ disjunctive in `bᵏ` | **shipped:** `isDisjunctive_pow_iff` in `Disjunctive.lean`, through the `OccursAt`/cylinder bridge and the §0 alignment word | low |
| Axiom Λ ⟹ `ln 2` is binary disjunctive | **shipped:** the circle ω-limit dictionary, Haar 0-1 law, `LnTwoHypothesisLambda`, and `isDisjunctive_log_two_of_hypothesisLambda` in `ConditionalDisjunctive.lean` | low-mid |
| Axiom D_w ⟹ `w` recurs arbitrarily late in binary `ln 2` | **shipped:** `LnTwoHypothesisD`, `frequently_occursAt_log_two_of_hypothesisD`, and the all-words disjunctivity assembly in `ConditionalDisjunctive.lean` | low-mid |
| Mahler 1973 / Berend-Boshernitzan | open; headline, elementary, no prior formalization found | mid |
| Furstenberg `×2 ×3` topological rigidity | open; famous, and the topological version is the tractable half | high |

The category proof is pure Baire theory.  `orbitLiftOpen` uses interiors of the
half-open digit cylinders, so b-adic double-expansion endpoints never enter.
The statements live on all of `ℝ`, since both `IsDisjunctive` and `IsNormal`
read only the fractional part.  The Λ proof instead uses the endpoint-identified
unit circle and mathlib's `AddCircle.ergodic_nsmul`.  Catalog rows for the last two open targets
live in the KB under `core/projects/formalization-targets/problems/`.

## References

- M. Waldschmidt, *Words and Transcendence*, arXiv:0908.4034 (Conjecture 1.1, Mahler's Theorem M,
  Berend-Boshernitzan)
- B. Adamczewski, N. Rampersad, *On patterns occurring in binary algebraic numbers*, PAMS 136 (2008)
  3105-3109
- D. H. Bailey, J. M. Borwein, *Nonnormality of Stoneham constants*, Ramanujan J. (2012)
- H. Furstenberg, *Disjointness in ergodic theory...*, Math. Systems Theory 1 (1967); survey:
  M. Tal, arXiv:2110.05989
- B. Host, *Nombres normaux, entropie, translations*, Israel J. Math. 91 (1995) 419-428
- P. Shmerkin (2019), M. Wu (2019), Furstenberg intersection conjecture
- C. S. Calude, T. Zamfirescu, *The typical number is a lexicon*, NZ J. Math 27 (1998) 7-13; *Most
  numbers obey no probability laws*, Publ. Math. Debrecen 54 Suppl. (1999) 619-623
- C. S. Calude, L. Staiger, *A simple construction of absolutely disjunctive Liouville numbers*,
  JALC; P. Hertling, *Disjunctive omega-words and real numbers*, J.UCS 2 (1996) 549-568
- G. Martin, *Absolutely abnormal numbers*, Amer. Math. Monthly 108 (2001), arXiv:math/0006089
- S. Nandakumar, S. K. Vangapelli, *Normality and finite-state dimension of Liouville numbers*,
  arXiv:1204.4104
- K. Ki, T. Linton (1994); V. Becher, T. Slaman, and Becher-Heiber-Slaman, complexity of normality
