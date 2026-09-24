# Handoff — PairDecouple, the PROOF direction, lap 9 (review lap)

**Branch** `wip/pd-prove` · tree clean, NOT pushed
**Build**: full `lake build` green, **9191 jobs**.
**Objective**: `KICKOFF-2026-09-24-pd-prove.md` + its Ren ADDENDUM (supersedes `DIRECTION.md`).
**Binding route**: `DIRECTION.md` → CURRENT DIRECTIVE (re-set this lap).

## The result

**The crux is now an EQUIVALENCE, not a reduction.**

```
shiftCorrSmall_iff_multiElliott :  ShiftCorrSmall b p q t  ↔  MultiElliott b p q t   (2 ≤ b)
```

`MultiElliott` is Elliott's conjecture for `4K(R)` linear forms with `K(R) → ∞`, for the
non-pretentious multiplicative functions `ζ_k^ω`, `ζ_k = e(t/b^{k+1})`.  One form:
Selberg–Delange.  Two forms: Tao, *Forum of Mathematics Pi* **4** (2016), in logarithmic
average.  `K → ∞`: **open, even logarithmically.**

Because it is an equivalence, `multiElliott_all` is exactly what the swing is missing; there is
no cheaper route through this leaf.  That is the kickoff's item 3, machine-checked.

## The chain

```
ConjC1            ⟸ Kátai + Delange + PairDecouple      SwingC1Decouple.lean  (pre-existing)
ConjC1            ⟸ Kátai + Delange + MultiElliott      conjC1_of_delange_katai_multiElliott ★
PairDecorr        ⟸ MultiElliott, NO prime cut          pairDecorr_of_multiElliott ★
pairDecouple_all  ⟸ largeDecay_all ⟸ shiftCorr_all ⟺ multiElliott_all   ← THE ONE OPEN LEAF
```
★ = new this lap, trust-triple clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

## New file `src/NormalNumbers/PairDecoupleElliott.lean` (sorry-free)

| declaration | content |
|---|---|
| `norm_phase_sub_one_le'`, `norm_phase_sub_phase_le` | `‖e(u) − 1‖ ≤ 4π\|u\|`, no smallness hypothesis |
| `tsum_digit_shift` | the digits beyond `K` are EXACTLY `b^{−K}·omegaTail b (N+K)` |
| `abs_pairTail_sub_digitTrunc_le_omegaTail` / `_le_crude` | the truncation error, closed form and uniform on `[0,M]` |
| `shiftPairDiff_eq_pairTail` | **the cut `P` cancels out of the shifted difference** |
| `AdmissibleTrunc`, `admissibleTrunc_id` | `K R = R` is an admissible depth |
| `MultiElliottAt`, `MultiElliott` | the named open hypothesis (existential in `K`, i.e. as weak as possible) |
| `abs_shiftCorr_sub_trunc_le`, `tendsto_truncErr` | the two-sided comparison |
| `shiftCorrSmall_of_multiElliott`, `multiElliottAt_of_shiftCorrSmall`, `shiftCorrSmall_iff_multiElliott` | the equivalence |

`PairDecoupleProve.lean` additionally carries `conjC1_of_delange_katai_multiElliott`,
`pairShiftCorr_of_shiftCorrSmall`, `pairDecorr_of_multiElliott`, `primesLe_zero`,
`primorialLe_zero`.

## `src/` open `sorry`s: 5

| where | status |
|---|---|
| `PairDecoupleProve.multiElliott_all` | **the campaign leaf** — an open conjecture, named and documented |
| `SwingC1.lean:920` `hDepthAll`, `:2201` `hAutoCorrAll` | pre-existing, designated open |
| `PrimeLambertOscillation`, `MahlerDriftOne` | pre-existing off-campaign, designated open |

Zero `axiom` declarations anywhere in `src/`.

## What was REFUTED / recorded (do not re-attempt)

1. Mass route (`TopMassVanishing`), lap 1.  2. Iterating the split, lap 3 — no `L¹` route closes
this crux.  3. **New this lap:** a FIXED truncation depth `K` cannot work under any splitting of
the prime range (the two requirements `y ≲ log R` for CRT and `y = R^{1−o(1)}` for small
discarded mass are disjoint).  4. **New this lap:** Fourier duality on the class decomposition
returns `PairDecouple` itself — circular.  5. **New this lap:** the Gaussian/CLT hope is the same
independence-over-primes model already in the repo and adds nothing.

## NEXT (start here)

1. **Sharpen the truncation depth** to `K(R) ≍ log_b log log R` by replacing `omegaTail_le_log`
   with the Mertens mean `Σ_{m≤X} ω(m) ≤ X(log log X + C)` in
   `abs_pairTail_sub_digitTrunc_le_crude`.  Check `HANDOFF-2026-09-16-mertensAP.md` and
   `G4Mertens.lean` (`sum_primesBelow_inv_mul_sub_one_le`) for reusable pieces.  This makes
   `MultiElliott` a `log log log R`-point statement and is the precondition for any partial
   literature input.
2. **Harvest `wip/pd-refute`'s band engine** (`git show wip/pd-refute:src/NormalNumbers/PairDecoupleBand.lean`,
   `PairDecoupleLower.lean`, `PairDecoupleAttacks.lean`): bounded prime bands decouple EXACTLY
   there.  Combine with the digit truncation so the `K` retained digits need only their
   LARGE-prime part `ω_{>y}(·)` — a strictly weaker correlation.  State and prove that leaf.
3. **Hunt for a reduction to `K = 1`** (the two-point case Tao 2016 settles logarithmically).
   Blocked at present by `E|pairTail − digitTrunc_1| ≍ b^{−1}√(log log R) → ∞`; any device that
   makes the tail digits *structured* rather than *small* is a genuine attempt.

## Confidence

**That `PairDecouple` is TRUE: 88%.**  (Ren's prior 70%; pd-prove 85% at lap 8; `wip/pd-refute`
93% after its band theorem and its failed counterexample hunt.  This lap's equivalence is
route-neutral — it sharpens WHAT must be proved, not whether it is true.)

## Standing constraints (unchanged)

* Do not edit `SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other
  KICKOFFs.  New work goes in `src/NormalNumbers/PairDecouple*.lean`.
* Never use `axiom`; named hypotheses (or a documented `sorry` on a conjecture) are the device.
* Never delete, rename or weaken `pairDecouple_all`.
* `PENDING_WORK.md` carries the full per-lap record, including every refutation above.
