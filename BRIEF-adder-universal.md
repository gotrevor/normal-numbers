# BRIEF follow-on: universalize the six-fold disjunction 🌍

**Operator-authorized 2026-08-29 (Trevor, attended session): "Seems like it's worth
generalizing this."**  Do this AFTER the kernel-tier certificate swap (or record the
swap as the remainder if it walls).

## The theorem to add

`adder_sixfold_disjunction_universal`: for ALL `X Y : ℝ` with `¬(∃ p : ℚ, (p:ℝ) = X) ∨
¬(∃ q : ℚ, (q:ℝ) = Y)` — i.e. **not both rational** — at least one of:
`00` occurs i.o. in X, `001` in Y, `11` in X+Y, `001` in X+2Y, `010` in 2X+Y,
`000` in X+3Y (binary, `OccursAt`, same i.o. form as the main theorem).

Restate the existing `adder_sixfold_disjunction` as a corollary (instantiate
X = log 2, Y = log 3, `irrational_log_two`, `Real.log_mul`-rewrites already in place).

## Route (small endgame refactor; modules 1-4 + certificate untouched)

The descent already yields eventual periodicity of the JOINT input stream, so BOTH
digit streams are eventually periodic.  Replace the single-stream
`irrational_log_two` contradiction with: X eventually-periodic-digits ⟹ X rational,
same for Y (the existing digits⟹rational lemma, applied twice), contradicting
"not both rational".  Nothing about ln 2 / ln 3 enters the automaton, carries, or
shadowing — they are generic in `X Y : ℝ` already; check module signatures and
generalize any that pinned the constants.

Keep both theorems; re-`#print axioms` both (universal version should carry exactly
the same axioms as the main one).  Note the (π, e) instance in the docstring as an
example, no extra theorem needed.
