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

## NEXT (lap 27 onwards)

1. **The dilated CRT / decoupling layer.**  The remaining lower-bound chain is
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
