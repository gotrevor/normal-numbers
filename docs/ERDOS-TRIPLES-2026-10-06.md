# Erdős #406 from gap-two triples (`/create`, 2026-10-06)

Lean record: `src/NormalNumbers/ErdosTriples.lean` (statements, proofs, confidences) and three Maze
rows ("Archimedean-only mechanisms for Erdős #406", "Exceptional set via all exponent tuples",
"Erdős #406 via gap-two triples").  Scripts and their known-answer suite:
`experiments/erdos-triples/` (`./test_triple.py`).

## Mechanisms tried, in order

1. **Head + tail counting** (leading digits from the rotation by `log₃ 2`, trailing digits from
   `2ⁿ mod 3ᵏ`).  Each side alone reproduces Narkiewicz's `N^{log₃ 2}`, and splitting `log₃ N`
   digits between them gives the same exponent: a split method can only count, and the count is
   fractal on both sides.  The archimedean half also dies outright against Lagarias's real
   sibling (Thm 1.2: uncountably many real `λ` with infinitely many `⌊λ2ⁿ⌋` omitting 2), so any
   proof must use the 3-adic coherence of `2ⁿ`.
2. **Purely 3-adic (Lagarias's exceptional set).**  Erdős #406 is `1 ∉ E(ℤ₃)`.  ABL bound
   `dim E(ℤ₃)` by the supremum over *all* exponent tuples of `dim C(1, 2^m₁, …)`, which stalls at
   `log₃ φ` because `4 = 1 + 3` makes small-gap tuples golden-mean-like.
3. **Ask what the bad tuples have that an infinite orbit can avoid: small gaps.**  An infinite
   exponent set has triples with both gaps large, so it suffices that
   `C(1, 4ᵃ, 4ᵃ⁺ᵇ) = {0}` for large `a, b`.  Each instance is a finite carry automaton,
   decided exactly (reachable cycle ⇔ nonzero point).

## Data

* Pairs: `dim C(1, 4ᵃ)` for `a = 1..11`: 0.438, 0.256, 0.278, 0.307, 0.215, 0.244, 0.267,
  0.2619, 0.2597, 0.2623, 0.2627, settling on `log₃(4/3) = 2 log₃ 2 − 1`, the independent value.
  Odd powers give `{0}` (`2^odd ≡ 2 mod 3`).
* Triples, `a < c ≤ 40`: nonzero only when `a = 1` or `c − a = 1`.
* Triples, `a, b ≥ 2`, `a + b ≤ 160`: all 12 403 trivial; largest reachable automaton 388 states.
* 3-adic imitators `a = 1 + 3ʲ` and `b = 1 + 3ʲ` (`j ≤ 5`): all trivial, at most 44 states.
* Gap one is genuinely nonzero even for large `a`: `C(1, 4⁸, 4⁹) ∋ 282864854542`.

## What is new, honestly

* The reduction `GapTwoTriples ⇒ E(ℤ₃) = {0} ⇒ Erdős #406` is elementary (pass to a subsequence).
  The point is that ABL's framework takes the supremum over all tuples and so cannot reach 0,
  while the gap-restricted family appears to be identically `{0}`.  ABL I §1.1: "we do not know
  whether E(ℤ₃) = {0} or not".  Novelty estimate ~60% for the framing, the computation new.
* Side finding: ABL II §7 says it is not known whether `s₃(2ⁿ) → ∞` (intermittency).  Stewart's
  1980 argument applied to `2N = 3N − N` (signed digits `nᵢ₋₁ − nᵢ`) appears to give it;
  recorded as `IntermittencyTendsToInfinity`, 85%, not traced to a published statement.

## The wall

Each instance is decided by `4ᵃ, 4ᵃ⁺ᵇ mod 3ᴰ`, `D` the extinction depth.  For `a = 1 + 3ᴰ t` the
automaton copies the golden-mean one for `D` levels before the third constraint bites, and
there are infinitely many such imitators.  A proof needs a uniform extinction bound for carry
automata whose multipliers are 3-adically near 4.  No mechanism yet.
