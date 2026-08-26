# Conditional disjunctivity: named axioms in the Bailey-Crandall pattern 🪜

Companion to [`disjunctive-vs-normal.md`](disjunctive-vs-normal.md).  That document maps what is
known; this one names **new conditional targets**: axioms `A` with proved (or provable) implications
`A ⟹ (specific constant is disjunctive / has a recurring block) in a specific base`.  The precedent
is Bailey-Crandall's Hypothesis A, which converts "π is 16-normal" into one dynamical hypothesis
about an explicit orbit; this repo already holds the machine-checked ln 2 instance
(`isNormal_log_two_of_equidistributed`).  The move here is to extend that pattern *downward* along
the outer ring, where the hypotheses get weaker-looking and the implications stay elementary.

Provenance: distilled from a 2026-08-25 working session (Trevor + Claude); the axiom names are
local to this document.  ⚠️ **Novelty status of every axiom is "apparently unstated," pending a
literature sweep** (§7) - none of these has been checked against the Bailey-Crandall descendant
literature, Bugeaud-Kaneko, or the rigidity surveys.  Treat each as a candidate reformulation
until swept.

## 0.  The orbit dictionary (unconditional, formalizable now)

For x ∈ ℝ and the circle map T_b(y) = by mod 1:

- x is **disjunctive in base b** ⟺ the orbit `{bⁿx mod 1}` is **dense** in [0,1).  (Normal ⟺
  equidistributed is Wall's theorem, formalized in this repo; this is its topological twin.)
- Equivalently, every finite base-b word occurs (`OccursAt`); and for every `k ≥ 1`, x is
  disjunctive in base b ⟺ x is disjunctive in base bᵏ (`isDisjunctive_pow_iff`).
- Let **Ω(x)** be the ω-limit set of the orbit (all subsequential limits).  On the
  endpoint-identified circle, Ω is closed and T_b-forward-invariant, and orbit density is
  equivalent to **Ω(x) being the full circle**.  With the current ambient-ℝ representatives,
  a dense orbit has closure `[0,1]`, so `[0,1)` must not be used as the right-hand closed set.

Formalized in `Disjunctive.lean`: the interval, word-occurrence, and dense-orbit formulations,
plus positive base-power invariance.  `ConditionalDisjunctive.lean` supplies the endpoint-safe
`UnitAddCircle` orbit and ω-limit, proves it closed and forward-invariant, and proves
`IsDisjunctive b x ↔ circleOmegaLimit b x = Set.univ`.

## 1.  Axiom Λ (positive limit mass) - ln 2, dynamics-flavored

**Theorem (0-1 law for closed forward-invariant sets; formalized).**  On the endpoint-identified
unit circle, if K is closed, T_b K ⊆ K, b ≥ 2, and Haar measure λ(K) > 0, then K is the full circle.

*Elementary proof route.*  Take a Lebesgue density point of K along the b-adic filtration: a
generation-n b-adic interval I with λ(K ∩ I) ≥ (1-ε)·b⁻ⁿ.  T_bⁿ maps I affinely onto [0,1), so
λ(T_bⁿ(K ∩ I)) ≥ 1-ε, and forward invariance puts that image inside K.  Hence λ(K) = 1, and a
closed co-null set has empty open complement.  ∎

*Formal proof route.*  Mathlib already proves that `y ↦ b • y` is ergodic on `AddCircle 1`.
Ergodicity makes a measurable forward-invariant K almost empty or almost full.  Positive measure
rules out the first case, and a closed almost-full set is literally full because Haar measure is
positive on every nonempty open set.  This is theorem
`closed_forwardInvariant_eq_univ_of_volume_pos`.

**Corollary (ladder collapse; formalized).**  λ(Ω(x)) > 0 ⟺ Ω(x) is the full circle ⟺ x is
b-disjunctive (`circleOmegaLimit_volume_pos_iff_isDisjunctive`).

> **Axiom Λ.**  The ω-limit set of `{2ⁿ ln 2}` has positive Lebesgue measure.
>
> **Λ ⟹ ln 2 is 2-disjunctive.**  Formalized as `LnTwoHypothesisLambda` and
> `isDisjunctive_log_two_of_hypothesisLambda`.

Λ is *equivalent* to the conclusion, but the hypothesis reads far weaker: "the limit points are not
a null set" rather than "the orbit visits everything."  The 0-1 law is the entire content; its
ergodic proof is now machine-checked against the pinned mathlib.

## 2.  Axiom family D_w (per-word density) - ln 2, exponential-sums-flavored

The repo's ln 2 machinery tracks `{2ⁿ ln 2}` by the explicit rationals
xₙ = {Σ_{k≤n} 2^{n-k}/k}, i.e. the kicked orbit x₀ = 0, xₙ = {2xₙ₋₁ + 1/n}, with tracking error
εₙ = Σ_{k>n} 2^{n-k}/k ≤ 1/(n+1) → 0.

> **Axiom D_w** (one axiom per finite word w).  The sequence (xₙ) has an accumulation point in the
> open cylinder interval of w.
>
> **D_w ⟹ w occurs infinitely often in the binary expansion of ln 2.**

(Proof: pass to the subsequence, add the o(1) tracking error, land `{2ⁿ ln 2}` in the open cylinder
infinitely often; a cylinder visit at time n is an occurrence of w at offset n.)

Why this family earns its place: `∀w D_w` ⟺ disjunctivity, but each **single** D_w with |w| ≥ 2 is
already beyond current knowledge - per Adamczewski-Rampersad, no specific irrational has any known
recurring block beyond `0, 1, 01, 10` (see the companion doc §2).  Hypothesis A is here shattered
into countably many independent pellets, each a visits-to-one-interval question about an explicit
rational sequence with controlled denominators.  The Stoneham normality proof in this repo succeeds
on exactly such a question (with cleaner, pure-power denominators); the ln 2 orbit's harmonic
denominators are the wall, but density asks for far less than equidistribution.

## 3.  Axiom C (carry rigidity) - √2, additive-combinatorics-flavored

Setup.  T = √2 - 1, with binary ones-set N ⊆ ℕ.  From T² + 2T - 1 = 0, **T² = 1 - 2T**, and for
irrational y ∈ (0,1) the number 1 - y has exactly the complemented digits of y.  So the squaring
identity says: *the carry-propagated parity pattern of the multiset N + N must reproduce, position
by position, the bitwise complement of N - 1 (the ones-set shifted one place left)*.

> **Axiom C.**  There is no real y ∈ (1,2) with y² = 2 whose binary ones are eventually isolated
> (all gaps ≥ 2 beyond some point).  Combinatorial rendering: for every finite prefix p and every
> N ⊆ (|p|, ∞) with all gaps ≥ 2, the square of 1 + val(p) + Σ_{n∈N} 2⁻ⁿ is not 2.
>
> **C ⟺ the block `11` occurs infinitely often in binary √2.**

Equivalent rather than weaker - the value is the port into additive combinatorics, where the
toolbox differs.  Two structural facts locate the difficulty precisely:

- **Frobenius vanishing.**  In 𝔽₂[[t]] (carry-free binary) squaring is the Frobenius endomorphism:
  cross terms vanish in pairs and the constraint trivializes identically.  All content lives in
  carry propagation, and no structure theory of carries strong enough exists (the
  Kummer / Holte / Diaconis-Fulman carry literature is probabilistic and generic).
- **Counting saturation.**  Running the identity through counts alone: the complement side demands
  ≥ n/2 ones in T², the collision side supplies at most (#ones)² of them, giving #ones ≫ √n - which
  is exactly the Bailey-Borwein-Crandall-Pomerance (2004) bound, the state of the art.  Counting
  then goes silent: isolated ones permit density 1/2 (`0101…`), so the hypothesis constrains
  *arrangement*, which mass-based arguments cannot see.

Bonus structure: for each fixed corruption depth M, the M-instance of C is refutable from computed
digits of √2 (an isolated-ones tail from position M plus y² within 2⁻ᵈ of 2 forces agreement with
√2's own digits to depth ≈ d, which empirically contain `11` immediately).  So C is a ∀-statement
over a computationally checkable family - the same logical shape as Collatz verification.

Class remark: x ↦ 1 - x complements bits and preserves algebraic degree, so at the class level
"`11` recurs in every algebraic irrational" and "`00` recurs in every algebraic irrational" are one
question.  √k analogues of C exist with an extra small-multiplier transducer.

## 4.  Axiom T (lossless dyadic transfer) - √2, harmonic-analysis-flavored

The identity self-couples dyadic windows.  Split the expansion at depth m: prefix P = digits in
[1, m], window W = digits in (m, 2m].  For a target column c ∈ (m, 2m], window-window pairs would
need two indices > m summing to ≤ 2m - impossible.  So restricted to those columns the identity
reads

    autocorr(P) + P ⊛ W = complement pattern on (m, 2m] + carry inflow from depth > 2m,

and the inflow is worth O(log m) bits at the boundary (column masses are ≤ m).  ⚠️ This derivation
is a session sketch; the carry bookkeeping wants one careful pass before anything rests on it.
Given the prefix, the next window solves a *linear* convolution-with-carries system - the precise
sense in which the first half forces the second.

> **Axiom T.**  There exist c > 0 and m₀ such that for all m ≥ m₀: if `11` occurs ≥ cm times in
> [1, m], then `11` occurs ≥ cm times in (m, 2m].
>
> **T + a computed base case ⟹ `11` occurs with positive density in binary √2** (in particular,
> infinitely often).

The word "lossless" is the entire difficulty: a per-doubling loss factor makes the per-window count
c·m·2⁻ᵏ·2ᵏ marginal at best.  And the transfer cannot be soft linear algebra - over 𝔽₂,
1/(1 + t + t² + …) = 1 + t, so deconvolution by a rich mask can be sparse; any proof must use the
fact that prefix, window, and target pattern are pieces of one sequence.  Discrete twin: the
Graham-Pollak recursion (our Erdős #482 formalization) emits √2's bits one per step from an integer
state; "when can that recursion emit two consecutive 1s, in terms of its state" is the same
question in bit-emitting-machine form.

## 5.  Axiom M (invariant-set avoidance) - quadratic irrationals, rigidity-flavored

> **Axiom M_b.**  No quadratic irrational lies in a closed T_b-forward-invariant subset of [0,1)
> of Hausdorff dimension < 1.
>
> **M_b ⟹ every quadratic irrational is b-disjunctive.**

*Proof.*  If x is not b-disjunctive, its orbit closure (which contains x) misses an open cylinder,
hence lies in the realization set of a missing-word subshift, whose dimension is
(topological entropy)/log b < 1 (standard for graph-directed self-similar sets).  ∎

M₃ restricted to the digit-1-free subshift is the quadratic case of Mahler's 1984 question
(are there algebraic irrationals in the middle-thirds Cantor set?), so M is its natural
sharpening.  The pointwise wall, stated once: the 2019 intersection theorems (Wu, Shmerkin)
*provably shrink* the fractal cage for a number non-disjunctive in two multiplicatively independent
bases, but a dimension bound can never exclude a single point - which is why M must be an axiom
here rather than a corollary.  (See the companion doc §4.2 for the Host-1995 measure-side block.)

## 6.  The block-frontier context (why these cells)

For *any* irrational, cheap combinatorics gives: at least 4 of the 8 length-3 blocks recur (tail
Morse-Hedlund), plus four forced disjunctions from extending the free blocks `01`/`10` - e.g.
`010 ∨ 011` recurs, `100 ∨ 101` recurs.  Every single 3-block is individually avoidable by some
irrational, so any specific-block theorem must break an extension tie using the number's
arithmetic - and no tie has ever been broken, for any constant.  The frontier is still inside
length 2 (`00`, `11` both open), which is why C and T aim at `11` and why the pattern-side route is
closed: Adamczewski-Rampersad already sit at the sharp binary repetition threshold 7/3, where the
avoiding class flips from polynomial to exponential and complexity arguments go silent.

## 7.  Discipline: claim status ledger

- **Novelty**: unswept, all five.  Owed before any outward use: Bailey-Crandall descendants
  (Λ, D_w), Bugeaud-Kaneko and the digit-expansion literature (C, T), rigidity surveys and the
  Mahler-problem literature (M).  "Apparently unstated" is the ceiling until then.
- **Proof status**: the circle ω-limit dictionary, 0-1 law, and Λ implication are formalized in
  `ConditionalDisjunctive.lean`.  D_w bridge = routine on top
  of the existing tracking lemma, unformalized.  §4 dyadic coupling = sketch, carry bookkeeping
  unchecked.  M's implication = complete modulo the standard SFT-dimension lemma, which is the
  real formalization cost.  Everything else in §0 is textbook.
- **Lean surface**:

| item | shape | tier |
|---|---|---|
| `OccursAt` + word/dense-orbit formulations + positive base-power invariance | **formalized** in `Disjunctive.lean` | done |
| `omegaLimit`: closed, forward-invariant, dense ⟺ full | **formalized** in `ConditionalDisjunctive.lean` | done |
| 0-1 law `measure_pos → omegaLimit = univ` | **formalized** via additive-circle ergodicity | done |
| Axiom Λ named + `isDisjunctive_log_two_of_...` assembly | **formalized** | done |
| D_w bridge from `lnTwoOrbit` tracking | conditional family | low-mid |
| M_b implication (needs dim(SFT) < 1) | fractal dimension | high |

## References (delta over the companion doc)

- D. H. Bailey, R. E. Crandall, *On the random character of fundamental constant expansions*,
  Exp. Math. 10 (2001).  (Hypothesis A - the pattern this doc extends.)
- D. H. Bailey, J. M. Borwein, R. E. Crandall, C. Pomerance, *On the binary expansions of
  algebraic numbers*, J. Théor. Nombres Bordeaux 16 (2004).  (The counting saturation point.)
- K. Mahler, *Some suggestions for further research*, Bull. Austral. Math. Soc. 29 (1984).
  (The Cantor-set question behind Axiom M.)
- P. Diaconis, J. Fulman, carries-as-cocycles line of work.  (State of carry theory.)
- R. L. Graham, H. O. Pollak (1970), via our Erdős #482 formalization.  (The bit-emitting
  recursion for √2.)
