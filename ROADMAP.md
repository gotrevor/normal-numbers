# Roadmap

The programme, in dependency order.  Status keys: ✅ done · 🔨 in progress · ⬜ queued.

## Phase 1 — foundations

- ✅ Definitions (`SeqDefs.lean`, `RealDefs.lean`): sequence normality (aligned
  with OldMathematician/ChampernowneNormality), digit map, real normality,
  equidistribution, the ×b orbit.
- 🔨 **Bridge** (`Bridge.lean`): `digitOf_realOfDigits` — the digit map inverts
  `realOfDigits` on proper digit sequences; corollary `isNormal_realOfDigits`.
  This is the lemma that upgrades sequence-normality theorems to real numbers.
- ⬜ **Wall's theorem** (`Wall.lean`): normal ⟺ orbit equidistributed.
  Route: blocks ↔ visits to b-adic intervals (exact correspondence), then
  approximate arbitrary `[a,c)` by b-adic intervals from inside and outside.

## Phase 2 — the two headline artifacts

- ⬜ **Bailey–Crandall reduction** (`LnTwo.lean`): `Equidistributed lnTwoOrbit →
  IsNormal 2 (Real.log 2)`.  Route: (i) `Real.log 2 = Σ 1/(n·2ⁿ)` (mathlib has
  the Mercator series; check exact form), (ii) `orbit 2 (log 2) n − lnTwoOrbit n
  → 0` (tail bound `O(1/n)`), (iii) equidistribution is stable under `o(1)`
  perturbation, (iv) Wall.
- ⬜ **Stoneham's theorem** (`Stoneham.lean`), unconditional.  Route
  (Bailey–Crandall 2002): between kicks at times `3ⁿ` the orbit is exact
  doubling of a rational with known denominator; count visits via the explicit
  rational orbit; discrepancy sums geometrically.  Expect this to need a
  self-contained discrepancy lemma (do NOT reach for Erdős–Turán unless forced).

## Phase 3 — outward

- ⬜ PR to OldMathematician/ChampernowneNormality: real-number corollary via the
  Bridge (self-contained port; their repo, their defs, Apache 2.0 both ways).
  Staged on a fork; **Trevor opens the PR**.
- ⬜ Comparator harness (`Challenge.lean`/`Solution.lean`, `enable_nanoda: true`)
  once Phase-1 theorems land; then public + Zulip announcement (**Trevor posts**).
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
