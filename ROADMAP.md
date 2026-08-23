# Roadmap

The programme, in dependency order.  Status keys: ✅ done · 🔨 in progress · ⬜ queued.

## Phase 1 — foundations (✅ complete, 2026-08-22, all axiom-clean)

- ✅ Definitions (`SeqDefs.lean`, `RealDefs.lean`): sequence normality (aligned
  with OldMathematician/ChampernowneNormality), digit map, real normality,
  equidistribution, the ×b orbit.
- ✅ **Bridge** (`Bridge.lean`): `digitOf_realOfDigits` + `isNormal_realOfDigits`.
- ✅ Counting/visit algebra (`Counting.lean`, `Visits.lean`): occurrences as
  index sets, boundary-window comparison, frequency transfer, cell sums.
- ✅ Digit↔interval toolkit (`DigitInterval.lean`): floor recursion,
  `blockNatVal`, `digits_prefix_iff`, shift lemma `digitOf_orbit`.
- ✅ **B-adic sandwich** (`Sandwich.lean`): `equidistributed_of_badic`.
- ✅ **Wall's theorem** (`Wall.lean`): `isNormal_iff_equidistributed_orbit`.
  Per the 2026-08-22 literature sweep, apparently the first formalization of
  Wall's theorem (and of interval equidistribution) in any proof assistant.

## Phase 2 — the two headline artifacts

- ✅ **Bailey–Crandall reduction** (`LnTwo.lean`):
  `isNormal_log_two_of_equidistributed : Equidistributed lnTwoOrbit →
  IsNormal 2 (Real.log 2)` — sorry-free, axiom-clean.  The open conjecture
  "ln 2 is normal in base 2" is now one machine-checked hypothesis about the
  explicit orbit `x₀ = 0, xₙ = 2xₙ₋₁ + 1/n mod 1`.
- 🔨 **Stoneham's theorem** (`Stoneham.lean`), unconditional.  Plan v2 (the
  hot-spot route): `StonehamArith.lean` ✅ (2 is a primitive root mod 3^M);
  remaining queue = window state recurrence/seed/approx, unit counting,
  one-sided segment bound, hot-spot lemma (pin statement against
  Bailey–Misiurewicz 2006), assembly.  No Erdős–Turán, no character sums:
  a partial cycle is a subset of a full cycle, and the hot-spot lemma only
  needs upper visit bounds.

## Moonshot map (from the 2026-08-22 literature sweep)

Bailey–Crandall 2002 Thm 4.8 / Cor 4.9 covers `Σ 1/(cⁿ·b^(dⁿ))` for coprime
`b,c` with `d > √c` (so `Σ 1/(3ⁿ·2^(4ⁿ))` is NOT new).  Genuinely open
neighbors: `Σ 1/(9ⁿ·2^(2ⁿ))` (`d < √c`, incomplete-exponential-sum wall),
`Σ 1/(3ⁿ·2^(n²))` (polynomial exponents; also not covered by their
nonnormality theorem), and their Artin-prime conjecture `Σ 1/(p·2^p)`.
Realistic new-math play: formalize the Stoneham mechanism *parametrically*
and squeeze the hypotheses (e.g. Thm 4.8's monotonicity condition (ii)).

## Phase 3 — outward

- 🔨 PR to OldMathematician/ChampernowneNormality: **done and staged** —
  branch `real-number` on `gotrevor/ChampernowneNormality`
  (`champernowne_real_normal`, axiom-clean on their v4.32.0-rc1 toolchain).
  **Trevor opens the PR**; Zulip note drafted in `drafts/`.
- ⬜ formal-conjectures touchpoint: their `IsNormalInBase` is *simple*
  normality despite the name — worth an upstream flag/fix.
- ⬜ Comparator harness (`Challenge.lean`/`Solution.lean`, `enable_nanoda: true`)
  for Wall + the ln 2 reduction; then public + Zulip announcement
  (**Trevor posts**).
- ⬜ Long game: normality definitions + Wall toward mathlib.

## References

- D. G. Champernowne, *The construction of decimals normal in the scale of ten*,
  J. London Math. Soc. 8 (1933) 254–260.
- D. D. Wall, *Normal numbers*, PhD thesis, UC Berkeley, 1949.
- D. H. Bailey, R. E. Crandall, *On the random character of fundamental constant
  expansions*, Exp. Math. 10 (2001) 175–190.  (Hypothesis A; the ln 2 orbit.)
- D. H. Bailey, R. E. Crandall, *Random generators and normal numbers*,
  Exp. Math. 11 (2002) 527–546.  (Stoneham normality, dynamical proof.)
- R. Stoneham, *On absolute (j, ε)-normality in the rational fractions with
  applications to normal numbers*, Acta Arith. 22 (1973) 277–286.
- D. H. Bailey, J. M. Borwein, *Nonnormality of Stoneham constants*,
  Ramanujan J. 29 (2012) 409–422.  (α₂,₃ not 6-normal.)
