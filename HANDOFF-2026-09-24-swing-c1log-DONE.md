# HANDOFF 2026-09-24 — swing at C1-log: target met, verdict recorded

Branch `wip/swing-c1log`.  `src/NormalNumbers/SwingC1Log.lean` **sorry-free**, axiom-clean
(`propext, Classical.choice, Quot.sound` only), `lake build` green.

## What landed

`src/NormalNumbers/SwingC1LogCarry.lean`
- `lambertVal_lt_one`, `fract_lambertVal` — `Σ w(m)/bᵐ ∈ [0,1)` for `w m ≤ m`, `b ≥ 3`.
- `digitOf_lambertVal` — **exact, modulus-free**: `d_n = w(n+1) + c_{n+1} − b·c_n`.
- `summable_carry_tail`, `le_carry`, `exists_card_primeFactors_ge`, `carry_unbounded`.
- `carry_correction_unbounded` — `ω(n+1) − d_n = b·c_n − c_{n+1}` takes arbitrarily large values.

`src/NormalNumbers/SwingC1LogAbel.lean`
- `tendsto_weighted_avg` (Toeplitz), `sum_div_succ_abel` (Abel), `tendsto_logAvg_of_tendsto_avg`.

`src/NormalNumbers/SwingC1Log.lean`
- `digitFreqLog`, `SimplyNormalLog`, `residueDigits`, `normalCastLaw_one`, `castFreqLog_one`.
- **`castLawLog_one_iff`** — the `L = 1` rung is exactly: `freq(d) = 1/b` for `0 < d < b−1` and
  `freq(0) + freq(b−1) = 2/b`.  I.e. log-simple-normality up to merging `0` with `b−1`.
- `castLawLog_of_castLaw` (item 1 of the kickoff, proved), `castLawLog_one_of_H`,
  `conjC1Log_of_conjC1`.

## The verdict (kickoff item 3)

`L = 1` needs `K`-point logarithmic correlations of `z^ω` (`z` a `b^K`-th root of unity) with
**`K` growing**, `K ≍ log log log X`, and uniformity beating `b^{−K}`.  The reason is in the
kernel: `c_N = ⌊Σ_k ω(N+k) b^{−k}⌋` truncated at depth `K` loses `≍ (log log X)·b^{−K}` on
average, and `carry_correction_unbounded` proves the correction is not bounded.

**Not covered by the published results.**  Tao (2016, two-point logarithmic Elliott) and
Tao–Teräväinen (2019, odd-order logarithmic Elliott) are FIXED-shift statements with no
uniformity in the number of shifts; and even at fixed `k`, even `k ≥ 4` is open.  Also, the rung
is not small: it is the simple-normality problem for `G4_b` in log density, one degree of freedom
short.

## Next (see PENDING_WORK.md)

Bounded surrogate weight `min(ω, M)`: the carry becomes bounded, the digit depends on `≤ K(M)`
shifts, and fixed-`K` log-Elliott DOES apply.  Formalize `castLawLog_of_boundedWeight` and probe
the digit-statistics distance from `G4_b` — that isolates exactly what the unboundedness of `ω`
costs.
