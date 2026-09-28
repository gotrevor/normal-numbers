# HANDOFF c3-mrt 2026-09-25 — lap 18 (REVIEW LAP)

**Branch** `wip/c3-mrt` · **HEAD** `ee66b76` · `lake build` green (9257 jobs) · working tree clean.
New module `C3MrtArchimedean.lean`, sorry-free, `[propext, Classical.choice, Quot.sound]`.
Prior state: `HANDOFF-c3mrt-2026-09-25-lap8.md` (laps 7–17).

## Review verdict

Direction **REDIRECTED** (the 2026-09-23 Theorem-C′ directive was complete).  `DIRECTION.md`'s
CURRENT DIRECTIVE now carries the C3/MRT moonshot; `PENDING_WORK.md` and `STATUS.md` refreshed.
Not crux-neglect: laps 7–17 were all on the `D = 2` rung, which IS the ratified success
criterion (the headline's own obligation, `QuantDepthElliott`, is out of reach — quantitative
Elliott at `≍ log log log N` points).

## The crux is untouched

`weylLambertTwist_holds` (`SwingC3Leaf.lean`) unchanged.  `conjC3_via_weylLambert` shows
`[propext, sorryAx, Classical.choice, Quot.sound]`; everything else in the chain is trust-triple.

## The lap's finding: the archimedean obligation's exact shape

Elliott's hypothesis is `(A:ℝ) ≤ pretentiousDistSqToTwist (ζ₀^Ω) χ t X` for `q ≤ A`,
`|t| ≤ A·X` — with `A` a **constant**, not `≫ log log X`.  `ζ^Ω` is constant `= z` on primes, so
(new, proved) with `mass X = ∑_{p≤X} 1/p` and `S = ∑_{p≤X} conj(χ(p)p^{it})/p`:

    pretentiousDistSqToTwist (ζ^Ω) χ t X  =  mass X − Re (z·S)   ≥   mass X − ‖S‖ .

**The `z` is gone from the bound.**  So the entire residual obligation is a bound on the
classical twisted prime sum, i.e. on `log|L(1 + 1/log X + it, χ)|`, and only a CONSTANT saving
is needed.  That fixes the split at `|t| ≈ T/log X` with `T = T(A)`:

* **Range 2, `|t| ≥ T/log X`** — needs `‖S‖ ≤ mass X − A`: the Vinogradov–Korobov log-derivative
  bound.  The dependency isolates the same input as
  `Erdos67b.PolynomialHeightPrimeCorrelationBound` ("expected proof: the log-derivative argument
  in the Vinogradov–Korobov zero-free region").  **Name it; do not chase it.**
* **Range 1, `|t| ≤ T/log X`** — elementary and ours.  This lap proved its key estimate.

## New, proved (`C3MrtArchimedean.lean`)

| name | content |
|---|---|
| `pretentiousDistSqToTwist_zOm_eq` / `_ge` | the bridge above |
| `resEps z = |arg z|/2` | the window half-width; `resEps_pos` is the ONLY use of `z ≠ 1` |
| `exists_int_arg_primePhase` | `arg(z·p^{−it}) = arg z − t log p − 2πm` for some `m : ℤ` |
| `two_resEps_le_abs_shift` | `2·resEps z ≤ |arg z − 2πm|` for EVERY `m` (equality at `m = 0`, `≥ π` otherwise) |
| `exists_window_of_resonant` | a resonant prime satisfies `‖ |arg z − 2πm| − |t| log p ‖ < resEps z` |
| **`window_mass_le`** | **primes confined to one resonance window carry reciprocal mass `≤ windowMassBound`, uniformly in `t`, `m`, `X`** |
| `reciprocalPrimeInterval_le_log_ratio` | interval Mertens in ratio form |

**Why `window_mass_le` works.**  The window in `log p` is `((γ−ε)/|t|, (γ+ε)/|t|)` with
`γ = |arg z − 2πm| ≥ 2ε`, so its endpoint **ratio** is `(γ+ε)/(γ−ε) ≤ 3` — *the `|t|
cancels*.  Its primes therefore lie in a fixed multiplicative range `(U, U³]`, which the
dependency's two-sided Mertens theorem bounds
(`Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le`, proved, error `mertensBound`).
The degenerate case `U < 4` is absorbed by the total mass below `64`.

## Refuted this lap — DO NOT RETRY

* **Extending the resonance count past `|t| ≳ (log X)^K`.**  The number of windows meeting
  `[2,X]` is `≍ |t| log X/2π`; the per-window Mertens error `2·mertensBound` alone then exceeds
  `log log X`.  Replacing it by a trivial/Brun–Titchmarsh count needs primes in intervals of
  length `p/|t|` — short-interval-hard, and genuinely so.
* **Hoping the crude `|ζ(1+it)| ≪ log t` suffices.**  At `|t| ≍ X` it gives
  `‖S‖ ≤ log log t + O(1) = log log X + O(1)`: exactly cancelling.  A saving factor `< 1` in the
  exponent (Vinogradov–Korobov) is not an artefact of the approach.
* Unchanged from earlier wraps: smooth/rough Kubilius split; self-similar recursion; growing `P`;
  direct use of `unitCircleLogElliott`.

## NEXT — resume here

1. **Range 1, assembly.**  With `|t| ≤ T/log X`: every `p ≤ X` has `|t| log p ≤ T`, so
   `exists_window_of_resonant` forces `γ_m < T + ε`, hence `|m| ≤ (T + ε + π)/2π =: M₀`, a
   CONSTANT.  Sum `window_mass_le` over `m ∈ Finset.Icc (−M₀) M₀`: resonance mass `≤`
   `(2M₀+1)·windowMassBound`, `X`-independent.  Subtract from the class-`1 (mod q)` Mertens
   lower bound (`G4MertensAP.mertensRate_residueClass`, already used by lap 17) and multiply by
   `1 − cos(resEps z)` (`one_sub_re_primePhase_ge`).  Yields `dist ≥ A` for `X ≥ X₀(A,q,z,T)`.
   *Watch*: `t = 0` is a separate (easier) branch — `window_mass_le` needs `t ≠ 0`; lap 17's
   `pretentiousDistSq_ge_class_sum` covers it.
2. **Range 2.**  `def TwistedPrimeSumSaving (A : ℕ) (T : ℝ) : Prop` — `∃ X₀, ∀ X ≥ X₀, q ≤ A, χ,
   t` with `T/log X ≤ |t| ≤ A·X`, `‖twistPrimeSum χ t X‖ ≤ primeReciprocals X − A`.  Then
   `nonPretentious_zOm : TwistedPrimeSumSaving A T → …` by `pretentiousDistSqToTwist_zOm_ge`.
3. **Feed `initial_segment_bound_of_elliott`**, then the tuple sum over coprime powerful pairs
   `d, e ≤ Y` (laps 8–13 supply weight transfer, truncation and the window stack).

## Confidence

* leaf TRUE ≈ 95% (unchanged).
* leaf PROVABLE in natural density with known techniques ≈ 15% (unchanged).
* **Range 1 closable in 1–2 laps: ≈ 80%.**  Everything it needs is now proved or in the repo.
* `D = 2` rung conditional on exactly two literature-proved inputs: ≈ 75%.
