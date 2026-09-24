# Handoff — PairDecouple, the PROOF direction, laps 11–21

**Branch** `wip/pd-prove` · **HEAD** `ee3caf9` · tree clean, NOT pushed
**Build**: full `lake build` green, **9192 jobs** (pre-commit hook verified on every commit).
**Objective**: `KICKOFF-2026-09-24-pd-prove.md` + its Ren ADDENDUM.
**Binding route**: `DIRECTION.md` → CURRENT DIRECTIVE (lap-9 review).  Items 1 and 2 are now
DONE; item 3 is untouched and is the natural next target.

## Where this stands in one line

The crux is still one named open conjecture, but it has been sharpened twice more: the
truncation depth is now `log_b log log R` (was `log_b log R`), and **every prime `≤ P` cancels
identically out of the leaf**, so the leaf is a LARGE-PRIME correlation in `O(log log log R)`
linear forms.  `pairDecouple_all` is untouched and still carries exactly one `sorry`.

## New this run — `src/NormalNumbers/PairDecoupleMertens.lean` (new, sorry-free)

Every declaration `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

### Directive item 1 — the depth (laps 11–17)

| declaration | content |
|---|---|
| `card_filter_dvd_le` | a prime coprime to the modulus meets `≤ R/p + 1` terms of `a i + e` |
| `card_filter_dvd_le_coprime` | the same for any modulus `d` coprime to `a` (pairs `pp'`) |
| `card_filter_dvd_ge` | `≥ ⌊R/d⌋` — the solutions are exactly ONE class mod `d` |
| `card_largePrimeFactors_le` | `y^card ≤ ∏ large prime factors ≤ m` |
| `sum_omegaNat_AP_le` | `Σ_{i<R} ω(ai+e) ≤ R Σ_{p≤y}1/p + π(y) + R ω(a) + R log_y(aR+e)` |
| `sum_inv_primesBelow_le_logLog` | `Σ_{p≤R} 1/p ≤ 4 log log₂R + 5` (from `G4.sum_inv_primes_Ioc_le`) |
| `sum_omegaTail_AP_le`, `_le'` | the same for the CARRY; `'` discharges `log_R` under `a+e+2 ≤ R` |
| `abs_norm_sum_phase_sub_le_sum` | the per-`i` phase comparison |
| `sum_abs_trunc_le_logLog` | the four progressions of the truncation error |
| `abs_shiftCorr_sub_trunc_le_logLog` | correlation-level bound, numerator `O(log log R)` |
| `depthLL`, `tendsto_meanTruncErr_depthLL` | explicit depth `≍ log_b log log R`; error → 0 |
| `eventually_depthLL_add_le` | the depth is sublinear |
| `tendsto_shiftCorr_sub_trunc_depthLL` | **capstone**: truncation asymptotically exact |
| `shiftCorrSmall_iff_multiElliottLL` | **the leaf at the sharpened depth, as an equivalence** |
| `PairMultiElliottLL`, `pairMultiElliottLL_of_multiElliottLL` | the minimal (`P=0`) form |

⚠️ `depthLL` does NOT satisfy `PairDecoupleElliott.AdmissibleTrunc` (which wants `b^K ≫ log R`).
That is the whole point; the new equivalence is proved from the capstone, not by instantiation.

### Directive item 2 — the small primes (lap 18)

`shiftDigitTrunc_eq_above`: `shiftDigitTrunc … = shiftDigitTruncAbove P …`, i.e. every prime
`≤ P` cancels IDENTICALLY.  Mechanism: `omegaBelow y m = #{r ≤ y : r ∣ m}` is exactly periodic
with period `∏_{r≤y} r` (`omegaBelow_eq_of_dvd_sub`), and the two shifted arguments differ by
`p·Q·(j−j')` with `Q = primorialLe P`.  Hence `shiftCorrSmall_iff_multiElliottLLAbove`.

This is stronger than the band route the directive pointed at, and lap 10's warning does not
apply: in the SHIFTED difference the periodic factor is not decoupled, it is EQUAL at both
shifts and cancels outright.  No estimate is spent — it is an equality.

### The variance (laps 19–21)

`turan_AP` — **Turán's inequality along an arithmetic progression**:
`Σ_{i<R}(ω_G(ai+e) − S)² ≤ R·S + π² + π + 2Sπ`, `G` = primes `≤ y` coprime to `a`.
`turan_AP_quarter` — the same at `y = R^{1/4}`, where the errors are `O(√R(1+S)) = o(R log log R)`.
So along the progression `ω` sticks to `log log R` within `O(√(log log R))`.  This PROVES the
swing's lap-33 variance finding, which had only been computed.

## `src/` open `sorry`s: 5 (unchanged; nothing relocated)

`PairDecoupleProve.multiElliott_all` (the campaign leaf), `SwingC1.lean:920`, `:2201`,
`PrimeLambertOscillation`, `MahlerDriftOne`.  Zero `axiom` declarations in `src/`.

## NEXT

1. **Directive item 3 — `K = 1` (Tao 2016).**  The only untouched directive item.  Turán now
   makes the obstruction precise and provable, not merely computed: the discarded tail has
   typical size `b^{-1}√(log log R)`, so no `L¹`/`L²` route reaches `K = 1`.  What is still
   unexplored is the *structured* alternative: the self-similarity
   `pairTail = digitTrunc_K + b^{−K}·pairTail_{K,K}` and a bootstrap on
   `A(s) := limsup_R sup_{a,a'} |E_{n<R} e(s·pairTail_{a,a'}(n))|`.  Note the dichotomy the
   variance exposes: a LARGE fluctuating tail would *help* (its phase averages out) — the
   difficulty is that proving that equidistribution is itself an Elliott-type statement.  Worth
   stating the dichotomy as a theorem before attacking either horn.
2. **Kátai/BSZ with large `p, q` only** (kickoff item 2, never tried): BSZ needs only
   sufficiently large primes; check whether the large-prime form of the leaf
   (`MultiElliottLLAbove`) is exactly what BSZ consumes.
3. Optional tidy: `sum_omegaNat_AP_le_logLog` and `turan_AP_quarter` could be merged into a
   single two-sided "concentration" statement for the carry.

## Confidence

**That `PairDecouple` is TRUE: 88%** (unchanged; laps 11–21 are route-neutral on truth — they
sharpen WHAT must be proved, twice).

## Standing constraints (unchanged)

* Do not edit `SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other
  KICKOFFs.  New work goes in `src/NormalNumbers/PairDecouple*.lean`.
* Never use `axiom`; named hypotheses (or a documented `sorry` on a conjecture) are the device.
* Never delete, rename or weaken `pairDecouple_all`.
* `DIRECTION.md` → CURRENT DIRECTIVE outranks this file; only altitude laps may edit it.
