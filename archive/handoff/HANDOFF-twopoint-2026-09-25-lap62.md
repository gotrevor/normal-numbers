# HANDOFF twopoint — lap 62, 2026-09-25: **RUNG 0 LANDED — `WeylTailAlmostAll → IsRichSubpoly`**

Branch `wip/twopoint-avg`.  Full `lake build` green (**9300 jobs**).  Tree clean at commit.
Every new declaration `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).
**No `sorry` introduced.**  New file only: `src/NormalNumbers/TwoPointC3Scales.lean`
(imported from `src/NormalNumbers.lean`); no frozen file touched.

## The advance on the crux

`DIRECTION.md`'s mandated rung 0 — the 🔴→🟠 re-plumb — is **done, as a theorem**:

    isRichSubpoly_of_weylTailAlmostAll :
      2 ≤ b → WeylTailAlmostAll b → IsRichSubpoly b (primeLambertAtBase b)

where

* `WeylTailAlong l b` — the C3 crux `WeylTailHypothesis` with `atTop` replaced by an arbitrary
  scale filter `l`.
* `ScalesDense ε S` — `∀ᶠ M, ∃ N ∈ S, M^{1-ε} ≤ N ≤ M`: the shape an exceptional set of small
  logarithmic density leaves behind (a gap fully inside `E` has log-length `≤ ε log M`).
* `WeylTailAlmostAll b := ∀ ε>0, ∃ S, ScalesDense ε S ∧ WeylTailAlong (atTop ⊓ 𝓟 S) b` — what
  Pilatte 2025 / TT2025 Thm 3.1 actually supplies.  `weylTailAlmostAll_of_weylTailHypothesis`
  proves it is genuinely weaker (the `S = univ` case).
* `IsRichSubpoly b x` — every admissible word occurs at `≥ c·N^{1-ε}` positions below `N`, every
  `ε>0`.  Pinned strictly between the two known rungs: `isRichSubpoly_of_isRich` (below `IsRich`)
  and `isDisjunctive_of_isRichSubpoly` (above disjunctivity).

**So the honest ledger entry for the C3 leaf is no longer "🔴 open": conditional on the 2026
literature statement (bad scales allowed), `G4_b` is subpolynomially rich, machine-checked.**

### The two pieces of real content

1. **The absorption lemma** `lower_of_monotone_of_scalesDense`: a *monotone* count large on a
   dense set of scales is large at every large scale, `C M ≥ C N ≥ c·N ≥ c·M^{1-ε}`.  This is the
   structural asymmetry the lap-61 reflection identified: `IsRich`'s count is monotone, so it
   absorbs `E`; `ConjC1`'s `CastLaw` is a two-sided density limit and does not.
   `ScalesDense.inter_Ici` lets the "eventually" from `atTop ⊓ 𝓟 S` be re-absorbed into `S`.
2. **The whole C3 route re-run along a filter.**  `wgood_all`/`wgood_real` (`SwingC3Weyl.lean`)
   are `atTop`-specific *only* because their proof goes through `Metric.tendsto_atTop`; the
   approximation half of the `ε/2+ε/2` split is a uniform-in-`N` bound (`norm_wMean_le`).  Filter-
   relative copies `WGoodAt`, `wgoodAt_fourier/_span/_all/_real` are now in the new file, and the
   counting core (`density_lower_of_decoupleR_at`) and covering argument
   (`occCount_lower_of_rotationRouteCAt`) follow verbatim, since every other input of
   `density_lower_of_decoupleR` is `∀ N` pointwise.  Chain:
   `WeylTailAlong l → TailLargeDecoupleCAt l → RotationRouteCAt l → occCount ≥ c·N on l`.
   Also new: `occCount` + `monotone_occCount` (the count as a first-class monotone object).

## NEXT SESSION

1. **Rung 2 — machine-check the wall** (unchanged, next in `DIRECTION.md`): `(1/N)∑_{n<N} tailLarge P b n → ∞`.
   Refutes every fixed-depth truncation.  Reuse `TwoPointMertensLower.mertens_lower`.
2. **The adjacent unconditional item `SwingC3Signed.lean`'s docstring names**:
   `∏_{P<p≤K} ‖primeFactor b p h‖ → 0`, via the one-term lower bound
   `Sig_p ≥ ‖1 − e(h·b^{p-1}/(b^p−1))‖²` into the proved `norm_primeFactor_sq_le`, then
   `mertens_lower`.
3. **Optional hardening of rung 0**: replace `ScalesDense`'s `∀ε` by a logarithmic-density
   hypothesis on the complement and *derive* `ScalesDense` from it — that would make the input
   literally TT2025's "log density of `E` ≪ L^{-c}" rather than its consequence.
4. Rung 3 (the pin to `ShiftElliott`) and TT2025 §5.2's alternating-sum/Gowers trick.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3% (untouched, as ratified).
- `WeylTailHypothesis` (every scale) TRUE 97%; provable with known techniques 8%.
- `WeylTailAlmostAll` provable from the 2026 literature: **70%** (unchanged; it is now a *stated
  Lean predicate* whose consequence is a theorem, which is the lap's advance).
- `IsRichSubpoly` reachable: 55% → **95% conditional on `WeylTailAlmostAll`** — that implication is
  no longer a plan, it is in the kernel.
