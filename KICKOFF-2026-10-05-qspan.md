# KICKOFF 2026-10-05: what the digits of a rational combination can look like

Branch `proof/qspan`, worktree `~/src/nn-qspan`.  Target file `src/NormalNumbers/QSpanCriterion.lean`.

## Origin

Trevor asked whether `√2`, `√3` or some `c₁√2 + c₂√3` must be normal.  That is open
(`QSpan.qSpanNormal_sqrt_two_sqrt_three`, Borel-hard).  Ren's tool for it: a rational
combination's digits are a bounded-carry function of the pair's joint digits, so normality of
any combination costs joint entropy (`QSpan.span_dimension_budget`).  This campaign proves the
structural picture and finds out whether entropy is the only obstruction.  It is not.

## Frozen headlines (statements byte-identical; proofs are the campaign)

1. `span_jointDim_budget`: normal combination ⇒ `1/2 ≤ fsDim (digitPair …)`.  Then prove
   `QSpan.span_dimension_budget` (in `QSpanNormal.lean`) from it plus a subadditivity leaf
   (joint lower dim ≤ lower dim of `x` + upper dim of `y`).
2. `isNormal_span_of_jointNormal`: jointly normal pair ⇒ every nonzero combination normal.
3. `ae_isNormal_combo_iff` and `ae_not_isNormal_combo_of_not`: the Fourier-zero criterion and its
   0–1 companion for independent i.i.d. digits.  This is the headline.
4. `ae_not_qSpanNormal_fiveDigits` and `ae_jointDim_fiveDigits`: digits `{0,…,4}`, entropy above
   budget, no normal combination (witness frequency `h = 5^N`).

## Mechanism notes

- Wall (`isNormal_rat_mul_add`) removes the divisor `q`: work with integer `(a, c)` throughout.
  ⚠️ Ren's first probe read "(4x+5y)/7 looks normal" from frequencies `h ≤ 125`; the defect sits
  at `h = 175 = 7·25`.  Any frequency claim about `/q` must include multiples of `q`.
- Stationary law: `bⁿ z mod 1` is a continuous-a.e. function of the future digit pairs plus the
  carry from `a⌊bⁿx⌋ + c⌊bⁿy⌋`, which is irrelevant mod 1 for integer `(a, c)`.  So the law is
  that of `a X + c Y mod 1` with `X, Y` independent self-similar; coefficients are the product
  `∏_{i≥1} φ_X(a h/bⁱ) φ_Y(c h/bⁱ)`.
- Genericity: Birkhoff on the Bernoulli digit shift (ergodic); `frac(bⁿ z)` is a function of the
  shifted point.  The repo's Weyl/visit machinery (`RealDefs`, `Bridge`) connects equidistribution
  to `IsNormal`.
- Probe: `experiments/qspan_digit_probe.py` (`./qspan_digit_probe.py test` runs the suite;
  `nu_hat` is the exact product, `empirical_hat` the measured coefficient).

## Rules

- Commit a compiling state with named `sorry` leaves early in each lap.
- If a frozen statement is false, prove the refutation, add a Maze row, and record the fix in a
  new statement beside it; never edit the frozen one.  That is progress.
- Build scoped modules (`lake build NormalNumbers.QSpanCriterion`); the root build only at the end.
- Done when `QSpanCriterion.lean` is sorry-free and `#print axioms` on items 1–4 shows no
  `sorryAx`.
