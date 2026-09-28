# HANDOFF twopoint lap 4 — **the averaged Kátai criterion overstates the literature**

This is the run's most consequential finding.  It is not about the ratified leaf's truth; it is
about whether the leaf, even if proved, closes C1 by the route that motivates it.

## What was found

Carrying out the Cauchy–Schwarz in the Kátai/BSZ argument *with constants* gives

    ‖E_{n<N} f(n)a(n)‖²  ≲  1/L(w)  +  pairSum(a,w,N) / L(w)²,      L(w) = Σ_{p≤w} 1/p,

where `pairSum = Σ_{p≠q≤w} ‖E_m a(pm) conj a(qm)‖`.  Derivation in the file header of
`src/NormalNumbers/TwoPointKataiSharp.lean`: Turán–Kubilius, then multiplicativity, then
Cauchy–Schwarz **in `m`** — whose *diagonal* `p = q` term is `Σ_{p≤w} N/p = N·L(w)`, which is
what forces the `L(w)²` denominator.

Because `pairSum = π(w)²·pairAvg`, the hypothesis the proof actually consumes is

    pairAvg a w N  ≪  L(w)²/π(w)²  ≍  (log log w)² / (w/log w)² ,

**not** `pairAvg → 0`.  The repo's `KataiOrthogonalityAvg` / `PairMeanAvgZero` quantify
`∀ε, ∀ᶠw, ∀ᶠN, pairAvg < ε` — `ε` chosen *before* `w` — so the `π(w)²` factor can never be
absorbed.  BSZ's qualitative statement survives only because there `w` is fixed and each of the
finitely many pairs is assumed to decorrelate individually, making `pairSum → 0` for that `w`.

**So the averaging over multipliers is not free.**  What is free is exactly `pairSum ≪ L(w)²`.

## Formalized this lap (`TwoPointKataiSharp.lean`, all `#print axioms` clean, no `sorry`)
- `kataiPrimeRecip`, `pairSum`, `pairAvg_eq_pairSum_div`.
- **`tendsto_kataiPrimeRecip`** — Mertens divergence `Σ_{p≤w} 1/p → ∞`, in kernel, from
  mathlib's `not_summable_one_div_on_primes`.  The only analytic input the wiring needs.
- **`KataiQuantSharp`** — the inequality with its true constants; `PairSumSmallGrowing`;
  `tendsto_fullMean_of_kataiQuantSharp` — the swing re-run honestly.
- **`avgShape_hubTable_pairSum_atTop`** — the gap, as a theorem.  `hubTable` (every pair through
  the prime `2` fully correlated, all others zero) satisfies the `AvgShape` quantifier order
  *exactly* — its average is `≍ 2/π(w) → 0` — while its pair **sum** tends to **infinity**.
  Hence `AvgShape` does not supply what the Cauchy–Schwarz consumes.

## Standing of the ratified headline
`twoPointWeightedAvg_all` is untouched, unweakened, and still the bet's target.  What lap 4
shows is that `conjC1_of_delange_kataiAvg_twoPointWeightedAvg` rests on `KataiOrthogonalityAvg`,
whose citation as "known" is **not supported by the BSZ/Kátai proof**.  Lap 3's
`conjC1_of_delange_kataiQuant_twoPointSlowGrowing` inherits the same defect (`KataiQuant` has the
same dropped `π(w)²`); `KataiQuantSharp` is the honest replacement, and it is the one to cite.
I did not edit `PairDecoupleAvg.lean` or any ratified statement (kickoff rules); the correction
lives entirely in new files.

## Confidence
- `twoPointWeightedAvg_all` TRUE: **88%** (unchanged).
- `twoPointWeightedAvg_all` SUFFICES for C1 via a correctly-cited Kátai step: **25%** — this is
  the number lap 4 moved, sharply down from an implicit 100%.
- PROVABLE with known techniques: **15%** (down from 25%: the honest target is now
  `pairSum ≪ L(w)²`, i.e. the average must beat `(log log w)²/π(w)²`, which is far past MRT).

## Next (lap 5)
1. Make the gap quantitative: prove `Tendsto (fun w => π(w)/(log log w)²) atTop atTop` from a
   Chebyshev-level lower bound on `π(w)` (cheap route: `w ≤ 2^{π(w)}·√w`, so `π(w) ≥ ½log₂ w`),
   and conclude that the `hubTable` witness actually violates `pairSum ≪ L(w)²` — upgrading
   lap 4's "sum → ∞" to "sum ≫ L(w)²".
2. State, in a new file, the honest leaf
   `TwoPointPairSumSmall b t : pairSum(…) ≪ L(w)²` and re-wire C1 onto it via `KataiQuantSharp`,
   so the development's cited hypotheses match the literature exactly.
