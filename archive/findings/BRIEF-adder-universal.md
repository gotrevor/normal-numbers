# BRIEF follow-on: universalize the six-fold disjunction 🌍

## RESULT (2026-08-30, autonomous lap)

**PROVED.**  `NormalNumbers.Adder.adder_sixfold_disjunction_universal`
(`src/NormalNumbers/AdderMain.lean`): for all `X Y : ℝ` with
`¬(∃ p : ℚ, (p:ℝ) = X) ∨ ¬(∃ q : ℚ, (q:ℝ) = Y)` (not both rational),
`00` occurs i.o. in X ∨ `001` in Y ∨ `11` in X+Y ∨ `001` in X+2Y ∨
`010` in 2X+Y ∨ `000` in X+3Y.  The frozen ln-instance
`adder_sixfold_disjunction` is restated as a corollary at
`(ln 2, ln 3)` (statement byte-identical; `Real.log_mul`/`log_pow`
rewrites + `irrational_log_two`).

* **Axiom audit (real `#print axioms`, both theorems):**
  `[propext, Classical.choice, Quot.sound]` — trust triple exactly
  (kernel-tier certificate `main_cert_ok_kernel`).
* **Route as briefed:** modules 1–4 + certificate untouched (they were
  already generic in `X Y`).  Endgame: `no_occurrence_contradiction`
  generalized to `no_occurrence_contradiction_universal` taking
  `Irrational X ∨ Irrational Y` — the joint input digit `σ = dX + 2·dY`
  is eventually periodic by descent, and since `dX, dY ≤ 1`, periodicity
  of `σ` splits into periodicity of BOTH coordinates (`omega`), so both
  X and Y would be rational.  The one-sided engine is kept as an
  `Or.inl` instance (toy pipeline unchanged).
* (π, e) instance noted in the universal theorem docstring, no extra
  theorem.

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
