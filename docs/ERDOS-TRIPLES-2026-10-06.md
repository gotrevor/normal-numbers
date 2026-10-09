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

## 2026-10-07: the port to zeroless 2ⁿ (base 10) is dead

Lean: `src/NormalNumbers/ZerolessTuples.lean`; probe + tests: `experiments/zeroless-tuples/` (`./test_tuple10.py`, 16 known-answer tests).

- **Ambient.**  For `n ≥ d`, `2ⁿ mod 10ᵈ` lies in the ideal `2ᵈ | r` (10-adically `{0} × ℤ₅`).  Each level-`d` residue has five lifts with forced digit parity, so the zeroless set grows `4, 18, 81, 364, …` (≈ 4.5ᵈ; matches OEIS A181610, the zero-free count in the cycle of `2ⁿ mod 10ᵈ`).  Not a finite carry automaton: survival has no cycle certificate, only death is finitely certified.
- **Kill 1, supercritical.**  Each translate costs 0.9 against 5 lifts: extinction needs `k ≥ 16` translates (`5·0.9¹⁶ < 1`), not the 22 in my earlier note (that used ambient 10, ignoring the forced 2-adic part).  Measured: pairs grow ≈4.05, triples ≈3.65, 15 critical, 16 die by depth ≤ 13 in all random samples.  `survives10_four_sixteen_thirty`: gaps (2,2) alive at depth 30 (witness digits in {1,2}); base 3 killed the same triple at depth 1.
- **Kill 2, truncation (proved).**  Base 3 had the full 3-adic expansion of `2^n₁`; base 10 only has `len(2^n₁)` digits, and gaps with `φ(5ᵈ) | g` act as the identity mod `10ᵈ`.  `not_tupleDeathAtLength k`: false for every tuple size and gap floor.
- **Residual.**  What tuples cannot see is `NestedZerolessChain`: a zeroless 10-adic integer with infinitely many power-of-two truncations (exponents forced 5-adically super-convergent, `φ(5^len) | n' − n`).  Heuristic count is summable (95% none).  Nearest prior art: Wu, arXiv:1902.11198 (greedy 10-adic power of 2 preserving trailing digits, for sparsity, not zerolessness).
- **What would replace it:** a mechanism using that the exponent is *small* (`n ≈ 3.32·len`) against the cycle length `4·5^(len−1)`: every unit mod `5ᴸ` is some `2ᵐ`, so the 5-adic side alone carries no information; the coupling of exponent size to digit length is the whole problem.

## 2026-10-08: lane 2 (the imitators): exponent-class certificates

Lean: `src/NormalNumbers/ErdosTripleClasses.lean`; probes + tests: `experiments/erdos-triples/{classtree.py,test_classtree.py,cycletype.py}`.

- **Probe that died first (cyclic vs integer split).**  The carry automaton is finite, so a nonzero point forces an eventually periodic one: either an integer (the zero state's 0-loop) or a ×3-periodic tail (a cycle with a digit-1 edge, equivalently a periodic point of the circle Cantor set K with 4ᵃθ, 4ᵃ⁺ᵇθ ∈ K).  Every nonzero triple found (`a = 1` rows and gap-1 rows) has cyclic points; only some have integer points.  No cleaner sub-conjecture.
- **Class certificates (proved).**  `Survives [4ᵃ, 4ᵃ⁺ᵇ] d` reads `4ᵃ mod 3^(d+1)`, i.e. `a mod 3ᵈ` (`four_pow_three_pow`).  `tripleTrivial_of_class`: one dead residue class ⇒ infinitely many trivial triples.  `tripleTrivial_of_mod_nine`: **all `(a, b)` with `a, b, a+b ∉ {0, ±1} (mod 9)` are trivial**.  Alive classes: 7/9, 49/81, 367/729 (Lean), then 2749, 20761, 158269, 1214503 (25.4% at depth 7).
- **Exact count.**  Alive (class, point) pairs at depth d number exactly 8ᵈ (α ↦ 4^α x is a bijection onto units ≡ 1 mod 3), so alive classes ≤ 8ᵈ (`AliveClassBound`, stated, 99%) and nontrivial pairs in `[0,X)²` are `O(X^{log₃ 8})`: density zero.  Two-variable form of Lagarias Thm 1.4; not new.
- **Kill (route "certify everything off the danger lines").**  The bad exponent set is `B∞ = {(log₄(y/x), log₄(z/y)) : x, y, z ∈ Σ*}`, a closed fractal of dimension ≤ log₃ 8, not a union of lines.  `x = 1, y = 10 = (101)₃, z = 28 = (1001)₃` gives `(log₄ 10, log₄ 2.8) ∈ B∞` with no difference in {0, ±1}; `survives_offLine_eight` realizes it with the integer pair (1227, 6261) at depth 8.  It is ≡ 0 mod 9 in `α+β`, consistent with the mod-9 theorem.
- **Where the wall now sits.**  `GapTwoTriples` ⇔ integer pairs with `a, b ≥ 2` avoid the fractal `B∞`.  The imitators are integer pairs 3-adically close to integer-adjacent points of `B∞` (the `a = 1` and `b = 1` rows), and they die at a depth that grows with the closeness.  This is a Diophantine membership question of the "is 1 in the Cantor set" type.  Class certificates prove a density tending to 1 and nothing uniform.
