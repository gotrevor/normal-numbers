# HANDOFF c3-mrt 2026-09-25 lap54 — the small primes cost only a period; gap 2 CLOSED

**New file** `src/NormalNumbers/C3MrtSmallPrimes.lean` (new chain tip:
`lake build NormalNumbers.C3MrtSmallPrimes`, 8985 jobs).  Sorry-free, 9 declarations, all
`[propext, Classical.choice, Quot.sound]`.  `lake build` green (9257).
Also this lap: `initial_segment_bound_of_kElliott_gen` in `C3MrtMultiRung.lean` — the
initial-segment bound for an ARBITRARY multiplicative unimodular family `g : Fin K → ℤ → ℂ`
(`KPointLogElliott` is itself stated for a free `g`, so the generalisation is free).

## What this lap proves

Lap 53 named three gaps between `rung_multi_correlation` and `weylLambertTwist_of_kfold_bound`
and closed the first (the additive twist).  **This lap closes the second.**

`ω = ω_{≤P} + ω_{>P}`, so for `ζ` on the unit circle
`ζ^{ω_{>P}(m)} = ζ^{ω(m)} · conj(ζ)^{ω_{≤P}(m)}` (`pow_omegaLarge_eq`), and `ω_{≤P}` is
`primorial P`-periodic in `m ≠ 0` (`omegaSmall_add_primorial`), because `p ∣ m` for a prime
`p ≤ P` is decided by `m mod primorial P`.  So the small-prime discrepancy is a **unimodular
`primorial P`-periodic weight — structurally identical to the twist**.  Both are stripped at once
by one residue-class decomposition modulo `M = Q · primorial P`, an `N`-independent modulus:

* `periodic_mul`, `periodic_eq_mod`, `norm_sum_periodic_le` — the general device: a unimodular
  `M`-periodic weight `w` is constant on classes mod `M`, so
  `‖∑_{n<N} w n · F n‖ ≤ ∑_{r<M} ‖∑_{n≡r} F n‖`.  (This *subsumes* lap 53's
  `norm_sum_twist_le`, which is the case `w = e(jn/Q)`.)
* `smallWeight`, `norm_smallWeight_le_one`, `smallWeight_periodic` — twist × small-prime
  correction, as one weight of period `Q · primorial P`.
* **`norm_depthAvg_le_omega_progressions`** — the payload:

      ‖depthAvg b P Q j h D N‖ ≤ (∑_{r<M} ‖∑_{m : Mm+r<N} ∏_{i<D} ζ_i^{ω(Mm+r+i+1)}‖)/N ,
      M = Q · primorial P .

  The inner sums are FULL-`ω` correlations at `D` consecutive shifts along the progressions
  `M·X + (r+i+1)` — exactly what `rung_multi_correlation` bounds.

## The ledger after this lap

**Neither the additive twist nor the small primes need any analytic input.**  Exactly ONE
structural gap now separates the `K`-fold assembly from the crux:

> **log-average → natural-average.**  `rung_multi_correlation` bounds
> `∑_{n<N} (n+1)^{-1} ∏ z_i^{ω(n+i+1)}` by `C + ε log N`; `depthAvg` is the natural average
> `(1/N)∑_{n<N}`.  Checked this lap and REFUTED as bookkeeping: log control gives
> `S(N) = o(log N)`, and the natural average over a window `(X, AX]` needs the *difference*
> `S(AX) − S(X)` to be `o(1)`, which `o(log N)` does not supply.  Partial summation over a
> window converts window-uniform log bounds of size `δ` into natural bounds `O(δ)`, but here
> `δ ≍ ε log X`, not `o(1)`.  **This is precisely the log-Chowla ⇏ Chowla barrier**, i.e. a
> named open problem in its own right — not a defect of the assembly.

Plus the quantitative decay class of lap 40 (`η N ≤ exp(−C(log log log N)⁴)`).

## NEXT

State the barrier as a named `Prop` in the ledger — `LogToNaturalTransfer` for the `ω`-correlation
family along progressions — and prove `WeylLambertTwist b` from
`KPointLogElliott` + `TwistedPrimeSumSavingAllLevels` + `LogToNaturalTransfer` + the lap-40 rate.
That is the equivalence statement the campaign is aiming at: `ConjC3` ⟸ (published Tao–Teräväinen)
+ (VK) + (log→natural, the named open barrier).  Note the rate obligation and the transfer
obligation interact — `weylLambertTwist_of_kfold_bound` wants an explicit `η N`, while
`rung_multi_correlation` is ε-for-every-ε; a quantitative `KPointLogElliott` is needed to produce
`η`, so the transfer Prop should be stated *quantitatively* (with a rate `η`) from the start.
