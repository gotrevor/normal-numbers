# HANDOFF elliott 2026-09-25 laps 36–39 — headline rewired; three of the crux's four assembly steps done

Branch `wip/elliott-port`, HEAD `ece6b76`.  Working tree clean.
`lake build NormalNumbers.ElliottGeneral` green, **9560 jobs**.
Never `lake exe cache get`.  Never edit / vendor `.lake/packages/lean-proofs-latest/`.

Read `DIRECTION.md` CURRENT DIRECTIVE first — it was rewritten by the lap-36 review and OUTRANKS
this file.  Detail lives in `PENDING_WORK.md` (top section).

## Lap 36 (review) — the defect found and fixed

`ElliottGeneral.nonasymptoticLogElliott` still depended on the `sorry` of the **refuted**
dilation-slice route, so laps 25–35's proved `a`-dilated graph stack carried **zero headline
weight**.  Fixed:

* new `src/NormalNumbers/ElliottDilatedRung.lean` — `dilatedCM_of_natShift` **proved**: arbitrary
  integer shifts are free over the natural-shift rungs (translate the window index by
  `k = |c₁| + |c₂|`; since `a ≥ 1`, `a k ≥ k` makes both shifts `≥ 0`; cost `3k`, absorbed by
  `Erdos67b.elliottExists_finalThreshold`).  Supporting: `norm_window_translate_sub_le`,
  `pairObservable_translate`, `elliottLogCorrelation_swap`,
  `norm_elliottLogCorrelation_le_translate`.
* `ElliottGeneral` repointed; the dead slice `sorry` retired (all *proved* slice content kept).
* Docs: `DIRECTION.md` CURRENT DIRECTIVE rewritten, `STATUS.md` refreshed, `PENDING_WORK.md` given
  a first real decomposition of leaf 3.

## Laps 37–39 — three of the four crux assembly steps

All new files zero sorry, `#print axioms` = trust triple.  No previously-proved file edited (only
`ElliottDilatedRung`'s import line, to keep each new file in the headline's build closure).

* **Step (ii)** — `ElliottDilatedWeight.lean`.
  `exists_dyadic_dilatedCorrelationWeight_lower`: `(H:ℝ)/(16 a log P) ≤ dilatedCorrelationWeight H a
  c₁ h (dyadicPrimes P)` under `2P ≤ H`, `4a + 4Ph ≤ H`.  Function-free counting
  (`card_dilatedProgression_lower`: `H/(2a)` active positions, halved again by the floor).  The
  dilation costs exactly `4a` against the dependency's `H/2`.
* **Step (i)** — `ElliottDilatedMean.lean`.
  `norm_logProb_dilatedMean_sub_correlation_le`: given a decoupling bound `e` on
  `genDiscrepancyAt` at the residue `n − crtShift H (·*c₁/a)`, the **mean** is
  `dilatedCorrelationWeight • affineLogCorrelation` up to `e` + the lap-35 transfer error.  Stated
  on `dilatedPairTwistedMean`, i.e. on **literally** the object the dilated upper bound constrains
  (join: `ElliottDilatedBridge.genMeanCRT_dilatedEdgeReindexed`).  Both halves of the crux are now
  inequalities about the same quantity.
* **Step (iii)(a)** — `ElliottDilatedGrouped.lean`.
  `ungroupBlock (finiteSequenceBlock (groupSeq a f) m n) = affineBlock f a n (a*m)` — lap 28's
  prediction in the kernel (`groupSeq a f k i = f (a k + i)`, `ungroupBlock b j = b (j/a) (j%a)`;
  the verification is `a(n + j/a + 1) + j%a = a(n+1) + j`), with **no** positivity hypothesis on
  `a`.  Plus `norm_dilatedEdgeReindexed_sub_le` (perturbation, constant `2Bζ` — the dependency's),
  `norm_ungroupBlock_sub_le`, `norm_blockExtend_sub_le`, `norm_groupSeq_le`.

## Open `sorry`s in scope (3)

| # | obligation | file:line |
|---|---|---|
| 1 | `dilatedNatShiftCMLogElliott` | `ElliottDilatedRung.lean:303` |
| 2 | `dilatedNatShiftCMLogElliottMirror` | `ElliottDilatedRung.lean:311` |
| 3 | `nonasymptotic_of_affineCM` | `ElliottLadder.lean:295` |

## NEXT (lap 40)

1. **Step (iii)(b): remove the finite-alphabet restriction** — the dilated
   `ElliottTwistedGraphBounded.exists_logProb_bounded_pairTwisted_decoupling`.  Alphabet
   `α = (Fin a → ↥net) × (Fin a → ↥net)` from `Erdos67b.exists_finite_unitDisk_approximation`
   (finite: `Fin a → finite`), decodes `dᵢ : α → Fin a → ℂ`, edge builder
   `mkE m b p j = dilatedEdgeReindexed (ungroupBlock (d₁ ∘ b)) (ungroupBlock (d₂ ∘ b)) a c₁ h p j`,
   approximant `A : ℕ → α` chosen componentwise over `Fin a`.  Budget `ζ = ε/(32 D)`, `D = 1/δ + 1`
   — the pure-shift one, because `norm_dilatedEdgeReindexed_sub_le` has the same constant.
   Needs generic `norm_genSum_sub_le` / `norm_genMeanCRT_sub_le` / `norm_genDiscrepancyAt_sub_le`:
   the `ElliottTwistedGraphBounded` lemmas with `pairShiftEdge` replaced by an arbitrary edge
   family.
2. **Step (iii)(c): the entropy-selected scale** — feed the above to
   `ElliottGenericGraph.exists_logProb_gen_decoupling` at `Δ m = crtShift (a*m) (·*c₁/a)`, giving
   `e = ε (a m)/log(a m)` for `norm_logProb_dilatedMean_sub_correlation_le`; then
   `ElliottDilatedWeight`'s dyadic bound and the contradiction against
   `ElliottDilatedUpper.exists_dilatedPairTwistedMean_small_of_fourier_first_moment`
   (the `ElliottTwistedGraphCriterion` collision verbatim), then the MRT choreography of
   `ElliottTwistedGraph.shiftCMLogElliott`.
3. **Leaf 2 (mirror)**: same, blocks exchanged, as `ElliottTwistedGraphMirror` is to
   `ElliottTwistedGraph`.
4. **Leaf 3** when the crux closes: Hall's inequality first (decomposition in `PENDING_WORK.md`).
