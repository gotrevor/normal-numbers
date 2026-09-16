# HANDOFF 2026-09-16 — G5/Ω: §4D is closed in closed form

Branch `wip/g5-prime-subset`, `lake build` green (9056 jobs), `src/` carries exactly the two
pre-expedition forbidden-drift `sorry`s (`phaseOscillation`, `exists_prime_nonresidue`); zero
`axiom`s.  Everything added this session prints `[propext, Classical.choice, Quot.sound]`.

## What landed: `src/NormalNumbers/G4OmegaJunk.lean` (new)

All three `PropD` inputs of `gridFrameW_cardFactors_propD` now have closed forms, and
`gridFrameW_cardFactors_propD_of_bounds` packages them:

1. **`junkAvgΩ_le`** — the valuation junk.  Route: junk ≥ 0, so the block average splits through
   the ℓ¹ row budget *after* averaging in `n`: `sampleAvg_abs_blockSum_le_of_shift` (generic in
   the weight; uses the new `blockSum_eq_sum_rowCoeff`), fed by `sum_junk_one_le`
   (= `G4WeightJunk.sum_junk_le` at `c ≡ 1`, shift capped by `ρmax`).
   Result: `junkAvgΩ ≤ (junkShiftBound P₀ X ρmax / |P|) · rowL1 bb K`.
2. **`bigAvgΩ_le'`** — `bigAvgΩ = bigAvg` by `rfl`; the `ω` estimate verbatim.
3. **`farAvgΩ_le`** — the real work.  See the two findings below.

## Two findings worth keeping

* **Ω's far tail cannot reuse the `ω` proof.**  The `ω` far bound rests on `2^ω(m) ≤ d(m)`
  (`sum_omegaR_add_le`), and that inequality *reverses* for `Ω` (`d(m) ≤ 2^{Ω(m)}`).  The
  pointwise fallback `Ω(m) ≤ log₂ m` costs a `log X`, which the schedule cannot pay
  (`farC_leE` budgets only `log P₀ + m + 10`, i.e. log·log-size).  The working route is the §4D
  split itself: `Ω = ω + frozenExcess + junk`, `frozenExcess ≤ Ω(P₀)` (`frozenExcess_one_le`),
  junk by `sum_junk_one_le`.  That is `sum_cardFactors_shiftG_le`, the AP-mean of `Ω` at layer `j`.
* **Ω's far tail needs base `≥ 3`, strictly more than the `ω` route's `bb ≥ 2`.**  The junk bound
  at layer `j` grows: `junkShiftBound P₀ X (j·Dm) ≤ junkA + junkB·2^j`
  (`junkShiftBound_layer_le`, from `X + jDm ≤ (X+Dm)·j` and `(j+1)² ≤ 4·2^j`), so the far series
  `∑ 2^j bb^{-j}` converges exactly when `bb > 2` (`hasSum_farJunkBound`).  This is consistent
  with — and does not worsen — the headline's `b ≥ 3`.  The junk far term carries a
  `√X·log X / |P| ≈ P₀/√X` factor, which the free cutoff `e` can make as small as needed.

## Resume here

1. **Schedule wiring for `Ω`.**  Feed `gridFrameW_cardFactors_propD_of_bounds` from the `HypE`
   parameter layer: `hbig` is the existing `ω` discharge verbatim; `hjunk` and `hfar` are new
   and need `junkShiftBound / |P|`, `junkA / |P|`, `junkB` bounded in the schedule parameters
   (`∑_{p∣P₀} 1/(p−1) ≤ 2(log ω(P₀)+2)`, `|P| ≥ X/(2P₀)`, `Nat.sqrt X · log₂ X / X` small).
   No new *analytic* input — all of it is size arithmetic in `K, e, P₀, X`.
2. Then `isDisjunctive_Omega` through `isDisjunctive_of_framesW`, and finally
   `∑_n Ω(n)/bⁿ = ∑_{p,a≥1} 1/(b^{p^a}−1)`.
