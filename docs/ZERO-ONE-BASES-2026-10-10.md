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
