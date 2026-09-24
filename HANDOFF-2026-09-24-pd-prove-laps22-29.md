# Handoff — PairDecouple, the PROOF direction, laps 22–29

**Branch** `wip/pd-prove` · **HEAD** `1ed8186` · tree clean, NOT pushed
**Build**: full `lake build` green, **9197 jobs** (pre-commit hook verified on every commit).
**Objective**: `KICKOFF-2026-09-24-pd-prove.md` + its Ren ADDENDUM.
**Binding route**: `DIRECTION.md` → CURRENT DIRECTIVE.  Items 1 and 2 were DONE before this run;
**item 3 (`K = 1`) is now done** — and in a way that supersedes item 1.

## Where this stands in one line

The crux is still one open statement, but it has changed CLASS twice: it is no longer a
`2K`-point correlation with `K → ∞`, it is a **weighted TWO-point correlation at fixed depth**
(laps 24–25, 29), and it need only hold **on average over the prime multipliers** (laps 22–23, 28).
`pairDecouple_all` is untouched and still carries exactly one `sorry`.

## New files this run (all sorry-free, all `#print axioms` = `[propext, Classical.choice, Quot.sound]`)

| file | content |
|---|---|
| `PairDecoupleAvg.lean` | the true (averaged) Kátai/BSZ criterion; only large multipliers matter; vdC averaged over multipliers |
| `PairDecoupleOneDigit.lean` | the EXACT one-digit and `K`-fold peel; the crux at fixed depth |
| `PairDecoupleTwoPoint.lean` | the split into Tao 2016 + a decoupling; the averaged two-point leaf |
| `PairDecoupleFirstOrder.lean` | leaf (D) at first order: no single prime obstructs |
| `PairDecoupleShiftPeel.lean` | the same peel on the RATIFIED target's own leaf |

### Laps 22–23 — the averaged criterion (kickoff item 2, never previously attempted)

`KataiOrthogonality` as the chain used it demands decorrelation for EVERY pair of distinct
primes.  BSZ/Kátai only need an average over `p, q ≤ w`.  `KataiOrthogonalityAvg`,
`kataiOrthogonality_of_avg` (certificate: nothing assumed is strengthened),
`pairMeanAvgZero_of_large_pairs` (**only large primes matter**),
`pairDecorrAvgSum_le_vdC` (van der Corput averaged over multipliers, Cauchy–Schwarz inside the
square root), `PairShiftCorrAvg`, `conjC1_of_delange_kataiAvg_pairShiftCorrAvg`.

### Laps 24–25, 29 — `K = 1`, EXACTLY (directive item 3)

The recorded block on `K = 1` was `E|pairTail − digitTrunc₁| ≍ b^{−1}√(log log R) → ∞`.  That
belongs to *approximating*.  The carry recursion gives an exact peel:

`pairTail = digitTrunc_K + b^{−K}(θ_{pn+K} − θ_{qn+K})`  (`pairTail_eq_digitTrunc_add`)

so `phase_pairTail_factor`: the pair phase is EXACTLY the `2K`-point root-of-unity product times
one **unit-modulus** weight, at every `K`.  Hence `pairDecorr_iff_multiElliottWeighted` — an
equivalence at every fixed `K`, **with no admissibility hypothesis** — and
`multiElliottWeighted_depth_indep`.  Lap 29 repeats all of this on the shifted object
(`shiftCorrSmall_iff_shiftTwoPointWeighted`, `pairDecouple_all_of_shiftTwoPointWeighted`), so the
RATIFIED target too is reachable at depth `1`.

⚠️ **Directive item 1 is therefore superseded, not merely improved.**  `AdmissibleTrunc` and the
`log_b log log R` depth existed only to make the discarded digits *small*; nothing needs that now.

### Lap 26, 28 — the split, and the sharpest leaf

`TwoPointElliott` (unweighted; = Tao, *Forum Math. Pi* **4** (2016) in log average) +
`WeightDecouple` ⟹ the crux.  ⚠️ honest correction: `weightDecouple_of_twoPointWeighted` shows
the two are *equivalent* given `TwoPointElliott`, so that split's value is its model × defect
SHAPE, not a weakening.

The two reductions compose (`pairDecorrAvg_iff_twoPointWeightedAvg`).  **Sharpest statement the
development reaches** (`conjC1_of_delange_kataiAvg_twoPointWeightedAvg`):

> `ConjC1` ⟸ Delange + averaged Kátai/BSZ + : for `b ≥ 3`, `b ∤ m`, `t = m/b`, `ζ = e(t/b)`, the
> mean over ordered pairs of distinct primes `p, q ≤ w` of
> `‖E_{n<N} ζ^{ω(pn+1)} conj ζ^{ω(qn+1)} · e((t/b)(θ_{pn+1} − θ_{qn+1}))‖`
> is `< ε` for all large `w` and then all large `N`.

### Lap 27 — leaf (D) at first order

`abs_sum_pairPeriodicTerm_le`: `|Σ_{n<R}(θ^{(r)}_{pn} − θ^{(r)}_{qn})| ≤ 1/(b−1)` for every prime
`r ∤ pq`, **uniformly in `r` AND `R`** — no sieve, no cut.  Ren's worry and leaf (D) both live in
the primes `r ≍ N`; this closes the SINGLE-prime horn (all primes contribute `O(1/log R)`).
Whatever obstructs leaf (D) is genuinely multilinear.

## REFUTED this run — do not re-attempt

**The term-by-term product expansion of leaf (D).**  Expanding `∏_r(μ_r + ψ_r)` over subsets:
every term with `d_S ≤ R` has exact period mean `0`, but any term-by-term ℓ¹ bound costs
`Σ_S ∏_{r∈S}(C/r) = ∏_{r≤X}(1+C/r) ≈ (log X)^C` against a model gain of only `(log X)^{−c}`,
`c < C` always.  It must lose: the full product has modulus `1` pointwise, so all cancellation is
*between* terms.  Lap 27 is the `|S| = 1` case (useful); the `|S| = 2` analogue is true by the same
CRT count but useless against `≍ (R/log R)²` pairs.

**Already-existing machinery not to re-derive** (I rediscovered it the hard way): the exact CRT
form `θ_N = Σ_r b^{N mod r}/(b^r − 1)` is `omegaTail_eq_tsum_primePeriodic`; the pair local
factors, `norm_pairLocalFactor_le` (`≤ 1 − c/r`) and `periodMean_pair_tendsto_zero` are all
already proved, sorry-free, in `SwingC1Periodic/Model/Pair.lean`.  The periodic MODEL term is
unconditional; the wall is leaf (D), period `exp(P)` vs range `R`.

## `src/` open `sorry`s: 5 (unchanged; nothing relocated)

`PairDecoupleProve.multiElliott_all`, `SwingC1.lean:920`, `:2201`, `PrimeLambertOscillation`,
`MahlerDriftOne`.  Zero `axiom` declarations in `src/`.

## NEXT

1. **Attack `TwoPointWeightedAvg` / `ShiftTwoPointWeighted b p q t 1` directly.**  It is now a
   two-point correlation with a bounded weight, averaged over multipliers — the closest target in
   this development to Matomäki–Radziwiłł–Tao (averaged Chowla, ANT 9 (2015)) and to Tao 2016.
2. **The only known method for the residual obstruction is the entropy-decrement argument**
   (Tao 2016).  Formalising the STATEMENT of its input (a two-point correlation in *logarithmic*
   average) and checking what would be needed to pass from logarithmic to natural density in this
   chain is the cheapest concrete next step.  Note `ConjC1` is a natural-density statement, so a
   logarithmic-average input needs a bridge — identify precisely where.
3. Untouched: whether the `u ≠ v` freedom in `shiftPairTail b p q u v` buys anything (the peel
   advances `u, v` together; nothing forces that).

## Confidence

**That `PairDecouple` is TRUE: 90%** (was 88%).  Raised by lap 27: the first-order term of every
large prime is unconditionally harmless, which was the one place a counterexample could have
lived cheaply.

## Standing constraints (unchanged)

* Do not edit `SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other
  KICKOFFs.  New work goes in `src/NormalNumbers/PairDecouple*.lean`.
* Never use `axiom`; named hypotheses (or a documented `sorry` on a conjecture) are the device.
* Never delete, rename or weaken `pairDecouple_all`.
* `DIRECTION.md` → CURRENT DIRECTIVE outranks this file; only altitude laps may edit it.
