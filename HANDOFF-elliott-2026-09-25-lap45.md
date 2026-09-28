# HANDOFF elliott 2026-09-25 laps 40–45 — the dilated crux closed except the mirror leaf

Branch `wip/elliott-port`, HEAD `8560428`.  Working tree clean.
`lake build` green (9562 jobs).  Never `lake exe cache get`.  Never edit `.lake/packages/lean-proofs-latest/`.

`DIRECTION.md` CURRENT DIRECTIVE still governs (laps 36+ mandate: live dilated route, close the
crux, then Hall for leaf 2).  This lap executed items 2 of that directive nearly to completion.

## What landed (all zero sorry, all `#print axioms` = trust triple)

1. **`src/NormalNumbers/ElliottGenericGraphBounded.lean`** (step iii(b)).
   Generic edge perturbation chain (`norm_genCoordinate_sub_le` … `norm_genDiscrepancyAt_sub_le`,
   edge-difference bound `η` as a parameter) plus
   `exists_logProb_bounded_dilated_decoupling`: the finite-alphabet restriction removed from the
   `a`-dilated graph, over `α = (Fin a → ↥net)²`, approximant chosen componentwise, using lap 39's
   `ungroupBlock_finiteSequenceBlock_groupSeq`.  Budget `ζ = ε/(32 D)`, `D = 1/δ+1`.
2. **`src/NormalNumbers/ElliottDilatedSelect.lean`** (step iii(c)).
   * `exists_uniform_dilated_window_error` — the dependency's finite-threshold argument with the
     extra dilated base-point term `2(cH)/(LM)`.
   * `exists_logProb_dilatedMean_correlation_close` — the entropy-selected dilated mean.
     New bookkeeping: `L₀ ≥ c₁H` over the finitely many scales.
   * `exists_logProb_dyadic_dilatedMean_lower` — large affine correlation ⇒ dilated mean
     `≥ ηH/(32a log H)` on `dyadicPrimes (H/(4h+4))` (the upper bound's own block; the side
     condition `4a + 4Ph ≤ H` comes from `4P ≥ 4a`, valid as `H = a m`, `m ≥ H₀ ≥ 4h+4`).
   * `exists_affineLogCorrelation_small_of_fourier_first_moments` — **the dilated criterion**:
     collision of that lower bound with `ElliottDilatedUpper` run at tolerance `η/(2a)`.
3. **`src/NormalNumbers/ElliottDilatedFourier.lean`**.
   `affineBlock_eq_finiteSequenceBlock`, `norm_blockFourier_affineBlock`,
   `MRTNonpretentious_of_le` (free passage `(A,X) → (A',X')` when `A' ≤ A`, `X ≤ X'`,
   `A'X' ≤ AX`), and `logProb_fourier_firstMoment_affineBlock_of_MRT` (`≤ 4aδH`, via
   `n⁻¹ ≤ 2a·(a(n+1)-1)⁻¹` on the strictly monotone base-point image).
4. **`ElliottDilatedRung.dilatedNatShiftCMLogElliott` — LEAF 1 OF THE CRUX PROVED.**
   `shiftCMLogElliott`'s choreography with MRT at `X' = aX + a`, `W' = min (2W) X'`,
   `A' = A/(2a)`, trimming parameter `max L₀ 2`.  Also `elliottLogCorrelation_eq_window_sum`.

## Open `sorry`s in scope (2)

| # | obligation | file:line |
|---|---|---|
| 1 | `dilatedNatShiftCMLogElliottMirror` | `ElliottDilatedRung.lean:532` |
| 2 | `nonasymptotic_of_affineCM` (leaf 2/3, Hall) | `ElliottLadder.lean:295` |

## NEXT (lap 46)

1. **The mirror leaf.**  `DilatedNatShiftCMLogElliottMirror` is the same statement with
   `MRTNonpretentious f₂` instead of `f₁`.  The whole new stack is symmetric except that
   `ElliottDilatedUpper.exists_dilatedPairTwistedMean_small_of_fourier_first_moment` consumes the
   Fourier moments of the **first** block.  Two candidate routes, in order:
   (a) run the chain with the blocks exchanged — needs a mirrored upper bound, i.e. the analogue of
       `ElliottTwistedGraphMirror` for the dilated mean (that file is the template);
   (b) cheaper: see whether conjugating/reflecting the window (`n ↦ ` the other form) maps the
       mirror statement to the proved one — check `elliottLogCorrelation_swap` (already proved in
       `ElliottDilatedRung`) against the pair `(c₁, c₁+h)`: swapping puts the non-pretentious
       function at the *larger* shift, which is exactly what the mirror asserts, so the remaining
       question is whether the dilated upper bound can be fed the second block's moments
       (it constrains `F₁` only because of Parseval on `F₂` — the roles are interchangeable in
       `norm_logProb_dilatedPairTwistedMean_le_of_fourier_first_moment`; inspect it first).
2. Then **leaf 2**, `nonasymptotic_of_affineCM`: Hall's inequality (decomposition in
   `PENDING_WORK.md` Finding 2 — Case A's thin-window sub-regime is the only hard part; Shiu is
   NOT needed).
