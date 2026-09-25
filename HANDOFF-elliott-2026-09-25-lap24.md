# HANDOFF elliott 2026-09-25 laps 16–24 — the crux route is re-founded and fully stocked

Branch `wip/elliott-port`, HEAD `a8d1c69`.  Working tree clean.
`lake build NormalNumbers.ElliottDilatedPairing` green, 9540 jobs (pre-commit `lake build`, 9257).
Never `lake exe cache get`.  Never edit / vendor `.lake/packages/lean-proofs-latest/`.

## Headline

`NormalNumbers.ElliottGeneral.nonasymptoticLogElliott : Erdos67b.NonasymptoticLogElliott`
(Tao 2016, Thm 1.3).  Open leaves in `src/` (unchanged in count this session):

| leaf | file:line | state |
|---|---|---|
| `dilatedSliceCMLogElliottGe` | `ElliottDilatedSlice.lean:220` | **superseded** — the slice route is refuted (below); the replacement route's ingredients are all proved, only the final assembly is missing |
| `nonasymptotic_of_affineCM` | `ElliottLadder.lean:297` | untouched; route in its docstring |

## What these nine laps did

### The slice route is REFUTED (lap 16) — do not re-derive

Reducing the crux to the multiples-of-`a` slice fails, for a concrete reason: centring the graph
edge on `f₁` requires translating by `p·c₁`, which turns `a ∣ m` into `a ∣ n − p·c₁`, a condition
depending on `p mod a`.  It does **not** factor out of the prime sum, so the indicator cannot ride
through the Fourier layer as a fixed periodic block factor.

### The replacement: the common dilation is a spectator

The graph step `n ↦ q·n` sends `(a n + c₁, a n + c₂)` to `q·(a n + c₁, a n + c₂)` — **both shifts
dilate with `q`**, exactly as `h ↦ q h` does in the proved pure-shift rung.  No divisibility side
condition, no arithmetic progression.  In block coordinates the dilation shows up as an index
dilated by `a`, and that is the only place it appears.

### Every layer of the dilated argument is now a proved, axiom-clean statement in `src/`

New files: `ElliottAffineGraph.lean`, `ElliottDilatedPairing.lean` (both zero sorry; every theorem
`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

| layer | lemma |
|---|---|
| edge → correlation (log mean), `a` absent from the errors | `ElliottAffineGraph.norm_logProb_affineTwistedObservable_sub_correlation_le` |
| block edge = affine observable | `dilatedPairShiftEdge_affineBlock` |
| edge sum = sum along the progression `r, r+a, …`, `r = s mod a` | `sum_dilatedPairShiftEdge_eq_progression` |
| edge sum = sum of observables (`pairTwistedSum_sequenceBlock` analogue) | `sum_dilatedPairShiftEdge_affineBlock` |
| dilated orthogonality (the one new Fourier lemma) | `sum_dilatedBlockPairing_mul_phase` |
| single frequency in `q` | `phase_pair_single_frequency`, `phase_mul_phase_eq_single_frequency` |
| exact Fourier identity for the mean | `dilatedPairTwistedMean_eq_fourier` |
| multiplier = the proved one, re-twisted | `dilatedTwistedMultiplier_eq`, **`dilatedTwistedMultiplier_eq_twisted`** |
| fourth moment / sup / Markov | `sum_fourth_dilatedTwistedMultiplier_le`, `norm_dilatedTwistedMultiplier_le`, `card_dilatedLargeFrequencies_le` |
| aliased Parseval | `phase_add_modulus`, `blockFourier_add_modulus`, `sum_range_shift_of_periodic`, `sum_norm_sq_blockFourier_shift` |
| large-frequency bound | `norm_dilatedPairTwistedMean_le_largeFrequencies` |
| logarithmic-average layer | `norm_logProb_dilatedPairTwistedMean_le_of_fourier_first_moment` |

**The two structural facts that make it work.**

1. Writing `T = α·D`, the residue-class restriction `α ∣ m − s` costs exactly one extra frequency
   variable `u < α`, which shifts only the *first* block's frequency by `u·D`; and with `s = q c₁`,
   `σ = q(c₂−c₁)` the two phases collapse to `phase T (t(c₂−c₁) − uDc₁) q`, a **single** frequency
   in the prime `q`.
2. `dilatedTwistedMultiplier_eq_twisted`: the alias variable `u` only re-twists the per-prime weight
   by a unimodular constant, leaving the shift `h` and frequency `t` where the proved arithmetic
   bounds live.  So **the dilated graph needs no new arithmetic at all** — the additive-energy
   input is reused unchanged, `α = a` (a constant) times.

## NEXT (lap 25 onwards)

1. **Assembly, upper half.**  Port
   `ElliottTwistedGraph.exists_pairTwistedPrimeGraphMean_small_of_fourier_first_moment` to the
   dilated mean.  The dependency's parameter choreography (`cutoff = η/64`, `N = C/cutoff⁴`,
   `ζ = η/(1024(N+1))`, budget `cutoff + 16ζN ≤ η/32`) carries over with `N ↦ α·N` — from
   `sum_fourth_dilatedTwistedMultiplier_le` + `card_dilatedLargeFrequencies_le` — and `α = a` is a
   constant fixed before `ζ`, so `ζ` absorbs it.  Needs `exists_eventually_twistedPrimeGraphMultiplier_bounds`
   applied per alias (it is already stated for an arbitrary `1`-bounded `w`, so this is free).
2. **Assembly, lower half.**  The lower bound (`exists_logProb_dyadic_pairTwistedMean_lower` in
   `ElliottTwistedGraphCorrelation.lean`) needs the dilated edge estimate
   `norm_logProb_affineTwistedObservable_sub_correlation_le` in place of
   `norm_logProb_pairTwistedDivisible_sub_correlation_le`, plus `sum_dilatedPairShiftEdge_affineBlock`
   to identify the CRT value.  Carry the hypothesis `⌊q c₁ / a⌋ ≤ n + 1` (free: `n ≥ L ≫ P|c₁|`).
3. Then `DilatedCMLogElliott` follows by the same contradiction as `shiftCMLogElliott`, and
   `ElliottDilatedSlice.dilatedSliceCMLogElliottGe` becomes dead weight — leave the file, retarget
   `dilatedCMLogElliott` at the new route.
4. **Parallel leaf:** `nonasymptotic_of_affineCM` (route in its docstring in `ElliottLadder.lean`).

## Notes for the next session

* `DIRECTION.md` still mandates the slice route (it was written before lap 16).  Lap 16 answered its
  own decisive question — "do `q ∣ n` and `a ∣ n` compose?" — in the negative *for the translated
  observable*, and found the better route it anticipates.  An altitude lap should refresh it; do not
  edit it from a proof lap.
* Caveat carried in `sum_dilatedPairShiftEdge_affineBlock`: block positions below `q c₁` are
  `a k + (q c₁ mod a)` with a smaller quotient, so the observable index is `n+1+j−⌊q c₁/a⌋` and the
  hypothesis `⌊q c₁/a⌋ ≤ n+1` must be carried.
