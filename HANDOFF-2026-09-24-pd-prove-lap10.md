# Handoff — PairDecouple, the PROOF direction, laps 9–10

**Branch** `wip/pd-prove` · **HEAD** `b1ea68a` · tree clean, NOT pushed
**Build**: full `lake build` green, **9191 jobs** (pre-commit hook verified on every commit).
**Objective**: `KICKOFF-2026-09-24-pd-prove.md` + its Ren ADDENDUM.
**Binding route**: `DIRECTION.md` → CURRENT DIRECTIVE (set by the lap-9 review; still current).

## Where this stands in one line

The crux of the ratified target is now **proved equivalent** to a single named open conjecture,
and that conjecture has been sharpened twice — to logarithmic truncation depth, and to one
variable with no progression.  `pairDecouple_all` is untouched in statement and still carries
exactly one `sorry`.

## The three nested conditional theorems (all trust-triple clean)

```
conjC1_of_delange_katai_decouple        : Kátai → Delange → PairDecouple      → ConjC1  (pre-existing)
conjC1_of_delange_katai_multiElliott    : Kátai → Delange → MultiElliott      → ConjC1  (lap 9) ★
conjC1_of_delange_katai_pairMultiElliott: Kátai → Delange → PairMultiElliott  → ConjC1  (lap 10) ★★
```

`pairMultiElliott_of_multiElliott` proves ★★'s hypothesis is weaker than ★'s.  `Kátai`
(`KataiOrthogonality`) and `Delange` (`DelangeMean`) are KNOWN theorems carried as named
hypotheses — each a mathlib-scale formalization of its own, deliberately not attacked here.

## The equivalences (this is what makes the reduction honest)

```
shiftCorrSmall_iff_multiElliott    : ShiftCorrSmall b p q t ↔ MultiElliott b p q t      (2 ≤ b)
pairShiftCorr_iff_pairMultiElliott : PairShiftCorr  b p q t ↔ PairMultiElliott b p q t  (2 ≤ b)
```

Both directions, so nothing is given away: the leaf IS the conjecture.

## The conjecture

`PairMultiElliott b p q t := ∃ K, AdmissibleTrunc b K ∧ ∀ j ≠ j',`
`  (1/R)‖Σ_{i<R} e(t·(digitTrunc_{K R}(i+j) − digitTrunc_{K R}(i+j')))‖ → 0`.

Through `phase_digitTrunc` this is Elliott's conjecture for `4K(R)` linear forms
`p(i+j)+1+k`, `q(i+j)+1+k`, `p(i+j')+1+k`, `q(i+j')+1+k` (`k < K(R)`) and the non-pretentious
multiplicative functions `ζ_k^ω`, `ζ_k = e(t/b^{k+1})`.
ONE form: Selberg–Delange.  TWO forms: Tao, *Forum of Mathematics Pi* **4** (2016), in
logarithmic average.  `K → ∞`: **open, even logarithmically.**

`AdmissibleTrunc b K := (log₂(R+1) + log₂(K R + 1) + 1)/b^{K R} → 0`, so `K(R) ≍ log_b log R`
qualifies.

## New this run

`src/NormalNumbers/PairDecoupleElliott.lean` (new, sorry-free, every declaration
`#print axioms` = `[propext, Classical.choice, Quot.sound]`):

| declaration | content |
|---|---|
| `norm_phase_sub_one_le'`, `norm_phase_sub_phase_le` | `‖e(u) − 1‖ ≤ 4π\|u\|`, no smallness hypothesis |
| `tsum_digit_shift` | the digits beyond `K` are EXACTLY `b^{−K}·omegaTail b (N+K)` |
| `abs_pairTail_sub_digitTrunc_le_omegaTail` / `_le_crude` / `_le_log` | the truncation error; the `_le_log` form is what buys `K ≍ log_b log R` |
| `natLog_two_mul_le` | `log₂(a·c) ≤ log₂ a + log₂ c + 1` (how the progression's constants stay additive) |
| `shiftPairDiff_eq_pairTail` | **the cut `P` cancels out of the shifted difference** — `P` survives only in the modulus |
| `AdmissibleTrunc`, `admissibleTrunc_id`, `truncNum`, `truncErr`, `tendsto_truncErr` | the depth bookkeeping |
| `MultiElliottAt`, `MultiElliott`, `PairMultiElliott` | the named leaves |
| `abs_shiftCorr_sub_trunc_le` | the two-sided comparison (both equivalences come from it) |
| `primesLe_zero`, `primorialLe_zero`, `largeProg_zero` | the `P = 0` collapse |

`src/NormalNumbers/PairDecoupleProve.lean`: the single `sorry` is now `multiElliott_all`,
documented with the state of the art; plus `conjC1_of_delange_katai_multiElliott`,
`conjC1_of_delange_katai_pairMultiElliott`, `pairDecorr_of_multiElliott`,
`pairDecorr_of_pairMultiElliott`, `pairShiftCorr_of_shiftCorrSmall`.

## `src/` open `sorry`s: 5 (unchanged count; nothing relocated)

| where | status |
|---|---|
| `PairDecoupleProve.multiElliott_all` | **the campaign leaf** — an open conjecture, named and documented |
| `SwingC1.lean:920` `hDepthAll`, `:2201` `hAutoCorrAll` | pre-existing, designated open |
| `PrimeLambertOscillation`, `MahlerDriftOne` | pre-existing off-campaign, designated open |

Zero `axiom` declarations anywhere in `src/`.

## REFUTED / recorded — do not re-attempt

1. Mass route (`TopMassVanishing`), lap 1.  2. Iterating the split, lap 3 — no `L¹` route closes
this crux.  3. A FIXED truncation depth `K` cannot work under any splitting of the prime range
(CRT wants `y ≲ log R`, small discarded mass wants `y = R^{1−o(1)}`; disjoint).  4. Fourier
duality on the class decomposition returns `PairDecouple` itself — circular.  5. The Gaussian/CLT
hope is the same independence-over-primes model already in the repo and adds nothing.
Full detail in `PENDING_WORK.md`, laps 1–10.

## NEXT (start here — matches `DIRECTION.md` → CURRENT DIRECTIVE)

1. **Mertens depth refinement.**  Replace `omegaTail_le_log` in
   `abs_pairTail_sub_digitTrunc_le_log` by the MEAN bound `Σ_{m≤X} ω(m) ≤ X(log log X + C)`.
   This needs restructuring `abs_norm_sum_phase_sub_le` to accept a per-`i` bound summed over
   `i < R` instead of a uniform `E` (the generalization
   `|‖Σ e(tX)‖ − ‖Σ e(tY)‖| ≤ 4π|t| Σ_i |X i − Y i|` is a two-line change), plus
   `Σ_{i<R} ω(a i + d) ≪ R(log log R + log a)`.  Reusable: `G4Mertens.lean`
   (`sum_primesBelow_inv_mul_sub_one_le`), `HANDOFF-2026-09-16-mertensAP.md`.  Payoff: `K(R) ≍
   log_b log log R`, i.e. the conjecture becomes a `log log log R`-point statement.
2. **Harvest `wip/pd-refute`'s band engine** — `git show wip/pd-refute:src/NormalNumbers/PairDecoupleBand.lean`
   (also `PairDecoupleLower.lean`, `PairDecoupleAttacks.lean`).  Bounded prime bands decouple
   EXACTLY there (`classDeviation ≤ 4(R mod M)/R`, `0` when `M ∣ R`).  Read it first, then decide
   whether the `K` retained digits can be cut down to their LARGE-prime part `ω_{>y}(·)`, and
   name that leaf.  ⚠️ Lap 10's analysis says this is NOT automatic: the band theorem is about the
   periodic factor alone, and decoupling it from the rest is class-independence again.  Settle
   that question against the actual Lean statements before building on it.
3. **Hunt for `K = 1`** — the only route that closes the whole thing against a published
   theorem.  Blocked by `E|pairTail − digitTrunc_1| ≍ b^{−1}√(log log R) → ∞`.  What would work:
   a device that makes the tail digits *structured* rather than *small*.  One unexplored lead:
   `pairTail = digitTrunc_K + b^{−K}·pairTail_{K,K}` where `pairTail_{a,a'}(n) :=
   omegaTail(pn+a) − omegaTail(qn+a')` — the tail is **the same object at frequency `t/b^K`**.
   A bootstrapping inequality on `A(s) := limsup_R sup_{a,a'} |E_{n<R} e(s·pairTail_{a,a'}(n))|`
   is the shape to look for.  Not yet attempted.

## Confidence

**That `PairDecouple` is TRUE: 88%.**  (Ren 70% → pd-prove 85% at lap 8 → `wip/pd-refute` 93%
after its band theorem and failed counterexample hunt.)  Laps 9–10 are route-neutral on truth:
they sharpen WHAT must be proved.

## Standing constraints (unchanged)

* Do not edit `SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other
  KICKOFFs.  New work goes in `src/NormalNumbers/PairDecouple*.lean`.
* Never use `axiom`; named hypotheses (or a documented `sorry` on a conjecture) are the device.
* Never delete, rename or weaken `pairDecouple_all`.
* `DIRECTION.md` → CURRENT DIRECTIVE outranks this file; only altitude laps may edit it.
