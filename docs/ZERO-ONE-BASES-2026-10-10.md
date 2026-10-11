# What the base-3 restriction buys (2026-10-10)

Review challenge: the pair conjecture (4, 5) discards base 3.  What does base 3 give?

Probe `experiments/zero-one-bases/width.py` (exact top-down tree over base-4 digits), lengths 200–1399:

| bases | survival per base-4 digit | random model | deepest survival | max width (L ≤ 400) |
|---|---|---|---|---|
| 4, 5 | 0.889 | 0.908 | 57 | 6 |
| 3, 4, 5 | 0.558 | 0.545 | 10 | 2 |

- The exact trees die at the random-model rate, so base 3 makes the problem robustly subcritical (exponent −0.438 vs −0.069).
- Base 3 does **not** help the Shmerkin–Wu step: tree width (the integer covering number) is O(1) for both.  The `n^ε` loss is in the proof.  Conjecture `FourFiveBoundedPerLength` (85%) needs no base 3.
- What base 3 adds is a **second slope coordinate**: a length L has a solution only if `(L log₃ 4, L log₅ 4) mod 1` lies in a target of measure ≈ 0.545^d at depth d.  Exploiting that needs the length orbit to equidistribute in 𝕋², i.e. `JointSlopeIndependence` (1, log₃ 4, log₅ 4 linearly independent over ℚ), a Schanuel-type statement we can't prove.  Burrell–Yu assume Schanuel for their digit-special result.
- Bug fixed same day: the first `BurrellYuFourFive` transcription was false at n = 0 (it counted 0 and bounded by C·0^ε).  Now `1 ≤ n`; the unrestricted form and its refutation are kept in `ZeroOneBasesReview.lean`.

# Literature check: `JointSlopeIndependence` (2026-10-10)

`JointSlopeIndependence` (1, log₃ 4, log₅ 4 independent over ℚ) is an instance of the **four exponentials conjecture**, which is open, and is proved as `fourExponentials_jointSlopeIndependence` (`ZeroOneBasesSlopes.lean`, axiom-clean).

- A relation `p + q log₃ 4 + r log₅ 4 = 0` is the homogeneous quadratic `p log 3 log 5 + q log 4 log 5 + r log 3 log 4 = 0`.  Baker's theorem covers linear forms in logarithms, so it does not reach this.
- With `r ≠ 0`, take `x = (1, r log₅ 4)` and `y = (log 3, log 5)`.  The four exponentials are 3, 5, `3^{-p} 4^{-q}` and `4^r`, all rational, which is what four exponentials forbids.  The `r = 0` case is unique factorization.
- The six exponentials theorem needs a third independent `y`, and one relation does not supply it.
- Even granting it, equidistribution alone says nothing about targets that shrink like `0.545^d`.  The base-3 lever sits behind an open transcendence conjecture *and* a missing shrinking-target count.  Maze row: "82000 via the base-3 slope coordinate" (wall).
