# HANDOFF elliott 2026-09-25 lap 36 (REVIEW LAP) — the headline is repointed onto the live route

Branch `wip/elliott-port`.  `lake build NormalNumbers.ElliottGeneral` green, **9557 jobs**.
Never `lake exe cache get`.  Never edit / vendor `.lake/packages/lean-proofs-latest/`.

## What the review found

`DIRECTION.md`'s CURRENT DIRECTIVE was **stale**: it still mandated the dilation-slice route, which
lap 16 refuted.  Worse, `ElliottGeneral.nonasymptoticLogElliott` still *depended* on that route's
`sorry` (`ElliottDilatedSlice.dilatedSliceCMLogElliottGe`), so the eleven laps of proved
`a`-dilated graph stack (laps 25–35) carried **zero headline weight** — orphaned scaffolding.
That is the defect this lap fixed, and the directive now mandates wiring before proving.

Laps 25–35 themselves were healthy: each closed a *different* named rung, and lap 33 found and
removed a real obstruction.  No repetition, no crux-neglect.  Direction KEPT, route CORRECTED.

## What landed (all green, no previously-proved statement edited)

**`src/NormalNumbers/ElliottDilatedRung.lean`** (new).  The crux rung on the live route:

* `norm_window_translate_sub_le` — translating the harmonic window index by `k` costs `3k`
  (telescoping weight discrepancy `≤ k` + two boundary blocks `≤ k` each).  **Proved.**
* `pairObservable_translate` — translating the index by `k` translates **both** shifts by `a·k`.
  Exact, no error.  **Proved.**
* `elliottLogCorrelation_swap` — symmetry under `(f₁,c₁) ↔ (f₂,c₂)`.  **Proved.**
* `norm_elliottLogCorrelation_le_translate` — the translation estimate for the common-dilation
  correlation.  **Proved.**
* `DilatedNatShiftCMLogElliott` / `...Mirror` — the crux at **natural** shifts `c₁`, `c₁+h`
  (`h ≥ 1`), non-pretentious on the smaller / larger shift respectively.  This is *exactly* the
  signature the dilated graph stack produces (compare
  `ElliottDilatedCorrelation.norm_logProb_dilatedGraph_sub_correlation_le`, whose correlation is
  `affineLogCorrelation L U f₁ f₂ a c₁ (c₁+h)`).
* `dilatedCM_of_natShift` — **PROVED**: arbitrary integer shifts are free.  Take
  `k = |c₁| + |c₂|`; since `a ≥ 1`, `a k ≥ k`, so both translated shifts `c₁ + a k`, `c₂ + a k`
  are `≥ 0`; the cost `3k` is absorbed by `Erdos67b.elliottExists_finalThreshold` into
  `(ε/2) log W`, and the sign of `c₂ - c₁` picks the orientation.
* `dilatedCMLogElliott : DilatedCMLogElliott` — from the two leaves.

**Rewiring.**  `ElliottGeneral` now imports `ElliottDilatedRung` and uses its
`dilatedCMLogElliott`.  `ElliottDilatedSlice`'s dead `sorry` stub (and its two consumers) is
retired — everything *proved* there (`elliottLogCorrelation_eq_slice`, `dilatedCM_of_slice`,
`sliceCM_one`, `dilatedSlice_of_ge`) stays, with a section explaining why the route is retired.
`ElliottLadder`'s closing docstring updated to point at the live route.

## Open `sorry`s in scope (3; was 2 — this is decomposition, not regression)

| # | obligation | file:line |
|---|---|---|
| 1 | `dilatedNatShiftCMLogElliott` | `ElliottDilatedRung.lean:303` |
| 2 | `dilatedNatShiftCMLogElliottMirror` | `ElliottDilatedRung.lean:311` |
| 3 | `nonasymptotic_of_affineCM` | `ElliottLadder.lean:295` |

`#print axioms`: headline = `[propext, sorryAx, Classical.choice, Quot.sound]`; every dilated rung
(`ElliottDilatedUpper`, `ElliottGenericGraph*`, `ElliottDilatedBridge`,
`ElliottDilatedCorrelation`), `affineCM_of_dilatedCM`, `shiftCMLogElliott`, `twoShiftCMLogElliott`
and the dependency's `unitCircleLogElliott` = trust triple.

## NEXT (lap 37 onwards) — see DIRECTION.md CURRENT DIRECTIVE

1. **Close leaf 1.**  Three steps, all with their inputs already proved:
   (i) trade the CRT sum for the mean — `ElliottGenericGraph.exists_logProb_gen_decoupling` with
   `Δ m = crtShift H (fun p ↦ p*c₁/a)`, then `genMeanCRT = dilatedPairTwistedMean` by
   `ElliottDilatedBridge.genMeanCRT_dilatedEdgeReindexed`;
   (ii) a lower bound on `ElliottDilatedCorrelation.dilatedCorrelationWeight` — function-free
   counting: for `p` dyadic in `(P, 2P]` with `2 p h < H` the count is `≥ H/(2a)`, so the weight is
   `≫ (H/a) ∑_{p∈s} 1/p`;
   (iii) the entropy-selected dyadic scale and the contradiction against
   `ElliottDilatedUpper.exists_dilatedPairTwistedMean_small_of_fourier_first_moment` — the
   `ElliottTwistedGraphCriterion` collision verbatim — then the MRT parameter choreography of
   `ElliottTwistedGraph.shiftCMLogElliott`.
2. **Leaf 2 (mirror)** should be the same file with the two blocks exchanged, as
   `ElliottTwistedGraphMirror` is to `ElliottTwistedGraph`.
3. **Leaf 3** is decomposed for the first time in `PENDING_WORK.md`: the hard core is **Hall's
   inequality** for nonneg 1-bounded multiplicative functions; Shiu is **not** needed (the affine
   modulus is fixed before `ε`, so bounding the AP sum by the full sum is free); and the
   sign-definite-truncation shortcut is **refuted** (`μ ⋆ h` alternates with `(-1)^{ω(d)}`).
