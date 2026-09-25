# HANDOFF elliott 2026-09-25 laps 25–26 — the dilated upper bound is assembled; the lower half is started

Branch `wip/elliott-port`.  `lake build` green.
Never `lake exe cache get`.  Never edit / vendor `.lake/packages/lean-proofs-latest/`.

## Headline

`NormalNumbers.ElliottGeneral.nonasymptoticLogElliott : Erdos67b.NonasymptoticLogElliott`
(Tao 2016, Thm 1.3).  Open leaves in `src/` unchanged: `dilatedSliceCMLogElliottGe`
(`ElliottDilatedSlice.lean:220`, superseded/refuted route) and `nonasymptotic_of_affineCM`
(`ElliottLadder.lean:297`).

## Lap 25 — `ElliottDilatedUpper.lean` (new, zero sorry, trust triple)

NEXT item 1 of lap 24 is **done**.

* `exists_eventually_scaledTwistedMultiplier_bounds` — the dependency's fourth-moment and supremum
  bounds at the *factorable* modulus `T = a·(4hH+1)` (the dilated orthogonality needs `T = α·D`
  with `α = a`).  The fourth-moment input is stated for an arbitrary modulus `> 4Ph`, so scaling by
  the fixed `a` only multiplies `C` by `a`; the supremum bound never sees `T`.
* `exists_dilatedPairTwistedMean_small_of_fourier_first_moment` — the dilated analogue of
  `ElliottTwistedGraph.exists_pairTwistedPrimeGraphMean_small_of_fourier_first_moment`.

**The alias factor cancels exactly.**  The large-frequency prefactor is `H·M/(T·α)` and the
frequency count is `α` times the undilated one, so the budget `cutoff + 16ζN ≤ η/32` is the
dependency's verbatim with no `α` in it.  The only trace of the dilation is inside `C`.

## Lap 26 — `ElliottDilatedLower.lean` (new, zero sorry, trust triple)

The one piece of the lower-bound port the dependency does not supply: its graph never moves the
base point *backwards*, but the dilated block bookkeeping produces edges at
`n + 1 + j − ⌊q c₁ / a⌋`.

* `norm_logProbExpectation_backtranslate_sub_le` — backward translation costs what forward does;
  obtained from `Erdos67b.norm_logProbExpectation_translate_sub_le` applied to `fun n ↦ F (n - d)`.
* `norm_logProb_affineTwistedObservable_shift_sub_correlation_le` — **each edge at the dilated
  index still has mean `C/q`**, with the dependency's errors plus `2d/(L·M)`.  Hypothesis `d ≤ L`,
  free since `d ≤ q c₁ / a ≤ P|c₁| ≪ L`.

## Lap 27 — `ElliottGenericGraphCRT.lean` (new, zero sorry, trust triple)

Route (b) of the decision below, taken and **landed for the CRT rung**: the whole CRT /
concentration layer is now proved over an **arbitrary edge family** `E : ℕ → Fin H → ℂ` with
`‖E p j‖ ≤ B²`.  Reading `ElliottTwistedGraphCRT` shows the edge enters in exactly two places (the
coordinate norm bound, and the total `∑_j` in the mean), so the generalisation is free.

* `genCoordinate`, `genObservable`, `genSum`, `genMeanCRT`; `norm_gen*_le`,
  `sum_genCoordinate`, `crtComplexMean_genObservable`.
* `gen_tail_card_mul_exp_le`, `exists_gen_exponential_tail` — the Hoeffding tail with the
  dependency's own constant `c = ρ²/(64R²)`.
* **Anchors `genCoordinate_pairShiftEdge`, `genSum_pairShiftEdge`, `genMeanCRT_pairShiftEdge` are
  `rfl`**: the proved pure-shift layer is literally the instance
  `E p j = pairShiftEdge b c (p*h) j`.  Nothing in `src/` was edited.

**And the prime-dependent residue shift turns out to be free.**  The dilated layer needs the
condition `z + (j+1) − d_p = 0` with `d_p = ⌊p c₁/a⌋`; that is the standard condition evaluated at
`z − d_p`, and `z ↦ z − d_p` is a bijection of `ZMod p`.  So the shift is applied to the residue
variable by the *caller* and never enters the layer.  Genericity in the edge was the only
generalisation needed — this is the lap's main structural finding.

## NEXT (lap 28 onwards)

1. **The generic decoupling layer.**  Repeat lap 27 one rung up: `ElliottTwistedGraphDecoupling`
   (`pairTwistedDiscrepancy`, `exists_logProb_pairTwisted_small_tail`,
   `exists_logProb_pairTwisted_decoupling`) over `genSum`/`genMeanCRT`.  The entropy layer only
   ever uses the discrepancy's boundedness (`norm_genSum_le` + `norm_genMeanCRT_le`, both proved)
   and `exists_gen_exponential_tail` (proved).  The one real design point: the edge family must be
   read off the finite-alphabet block, i.e. `E` becomes `(Fin H → α) → ℕ → Fin H → ℂ`.
2. Then instantiate at `E p j = dilatedPairShiftEdge (affineBlock f₁) (affineBlock f₂) a (p c₁) (p h) j`
   with residue variable `z − ⌊p c₁/a⌋`, and combine with
   `sum_dilatedPairShiftEdge_affineBlock` + lap 26's edge-mean estimate.

OLD PLAN (superseded by lap 27, kept for the reasoning):
   **The dilated CRT / decoupling layer.**  The remaining lower-bound chain is
   `ElliottTwistedGraphCRT` → `Decoupling` → `Correlation`, all written for `pairShiftEdge`.
   The dilated coordinate is `∑_j if z + (j+1-d_q) = 0 then w q · dilatedPairShiftEdge … j`:
   the residue condition is *translated by `d_q = ⌊q c₁/a⌋`*, which is a bijection of `ZMod q`
   and so disturbs neither the CRT factorisation nor the entropy/rare-event argument.  Two options,
   decide at the start of the lap:
   (a) port the three files with the shifted coordinate (mechanical, ~3 laps);
   (b) **generalise the proved stack once over an arbitrary bounded edge family `E : ℕ → Fin H → ℂ`
       and residue shift**, making both the pure-shift and dilated cases instances (one refactor,
       higher leverage, touches proved `src/` files only).
   (b) looks better: the entropy layer only ever uses boundedness of the edge.
2. Then `DilatedCMLogElliott` by the same contradiction as `shiftCMLogElliott`.
3. **Parallel leaf:** `nonasymptotic_of_affineCM` (route in its docstring in `ElliottLadder.lean`).

## Note

`DIRECTION.md` still mandates the slice route (written before lap 16, which refuted it and
answered the directive's own decisive question — "do `q ∣ n` and `a ∣ n` compose?" — in the
negative for the translated observable).  The dilated route is the replacement and stays inside the
directive's objective, scope and forbidden-drift list.  An altitude lap should refresh it; do not
edit it from a proof lap.
