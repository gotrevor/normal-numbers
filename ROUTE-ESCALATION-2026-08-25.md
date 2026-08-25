# ROUTE ESCALATION — B6 pivots from the schedule to the MEASURE route

**Date:** 2026-08-25 (review lap #2).  **Trigger fired:** the mandated single-stream crux
`variance_blockCount_psi_pushed` is **provably FALSE** (`OBSTRUCTION-2026-08-25-variance-psi-pushed-FALSE.md`).
The 2026-08-24 review (`HANDOFF-2026-08-24-B6-review-crux.md:43`) pre-registered this exact
contingency: "if [the schedule primitive is] not [provable], escalate toward escape #3
(natural-extension / measure argument) — write `ROUTE-ESCALATION-2026-08-25.md`."  Both schedule
sub-routes are now dead (two-stream = super-exp blocks `OBSTRUCTION-2026-08-24`; single-stream
passive-Chebyshev = false crux, today).  So: **take escape #3.**

## The stated theorem is trivially true a.e. — prove it by a measure argument

The frozen headline is bare EXISTENCE:
```
exists_cfNormal_and_affine_cfNormal {q} (hq : 0 < q) (r) : ∃ x, IsCFNormal x ∧ IsCFNormal (affineMap q r x)
```
No explicit/constructive witness is demanded by the statement (the schedule's explicit witness was
the aspirational BONUS; per the attack map §4, "a.e. x works; the existence statement is trivial,
the witness is not").  Sketch (all Birkhoff-FREE, uses the already-proven full-measure variance
bound `variance_blockCount_le`, `CFBlockFreq.lean:401`):

1. **`ae_isCFNormal` (THE new core lemma):** `∀ᵐ y ∂gaussMeasure, IsCFNormal y` — equivalently
   `{y : IsCFNormal y}` is co-null in `(0,1)`.  Route (classic L² → a.e., no ergodic theorem):
   - For a FIXED `v` (digits ≥1): `variance_blockCount_le` + Chebyshev ⇒
     `γ{|blockCount(cfCyl v) p ·/p − γv| ≥ δ} ≤ (8|v|+80)γv/(δ²p)`.  Along `p = k²` this is summable
     in `k`, so by Borel–Cantelli (`MeasureTheory.measure_limsup_...`) a.e. `blockCount_{k²}/k² → γv`;
     fill gaps by monotonicity of `p ↦ blockCount(cfCyl v) p x` and `(k+1)²/k² → 1` (squeeze).
     ⇒ a.e. `blockCount(cfCyl v) p ·/p → γv`.
   - Intersect over the COUNTABLE set of valid finite words `v` (co-null ∩ co-null = co-null) and
     over the a.e. condition `∀ j, gaussMap^[j] y ∈ Ioo 0 1` (rationals/pre-periodic are null) ⇒
     a.e. `y` satisfies the hypotheses of `isCFNormal_of_orbit_freq` (`CFOrbitFreq.lean:34`) ⇒
     `IsCFNormal y`.
2. **`ae_isCFNormal_affine`:** `∀ᵐ x, IsCFNormal (affineMap q r x)`.  `{x : IsCFNormal(ψx)} =
   ψ⁻¹{y : IsCFNormal y}`; its complement is `ψ⁻¹(null)`.  `ψ` affine ⇒
   `volume(ψ⁻¹ S) = |1/q|·volume S` (`volume_preimage_affineMap`, `CFAffine.lean:94`, PROVED), so
   ψ⁻¹ maps volume-null → volume-null; `gaussMeasure ≈ volume` on `(0,1)` (bounded density both ways)
   ⇒ ψ⁻¹ maps γ-null → γ-null.  Hence co-null.
3. **Intersect + nonempty:** on the feasible interval `I = (0,1) ∩ ψ⁻¹(0,1)` (nonempty, positive
   measure when `-q<r<1`), both a.e. sets are co-null, so `{IsCFNormal} ∩ {IsCFNormal∘ψ} ∩ I` is
   co-null in a positive-measure set ⇒ **nonempty**.  Pick the witness; done.  The general-`r`
   reduction (integer shift, `isCFNormal_add_nat`) already in `exists_cfNormal_and_affine_cfNormal`
   handles `r ∉ (-q,1)`, so only the feasible case needs the witness — exactly where
   `exists_interleaved_affine_witness` currently plugs in.

**The whole B6 obligation collapses to ONE real lemma: `ae_isCFNormal` (a.e. CF-normality).**  Even
the COMBINED existence (abs-normal ∧ CF-normal ∧ Khinchin ∧ ψ-CF-normal in one `x`) is a.e.-true
(four co-null sets intersect), but that is not what the headline asks; keep scope to the stated theorem.

## What this retires / keeps

- RETIRE (off the headline path, keep in `src` marked REFUTED, do NOT grind): the whole
  `variance_blockCount_psi_pushed` → `psi_pushed_chebyshev_brick` → `_poly` chain, the two-stream
  `schedA_block_linear`, and the interleaved-schedule crux `exists_interleaved_affine_witness`.
  Nothing is deleted; the explicit-witness construction stays on disk as an (obstructed) alternate.
- KEEP + REUSE: `variance_blockCount_le` (the engine), `isCFNormal_of_orbit_freq` /
  `isCFNormal_of_irrational_orbit_freq` (orbit ⇒ digit-window), `volume_preimage_affineMap`,
  the feasibility/interval + integer-shift reduction already inside the headline.
- The B5′ headlines are untouched and stay trust-triple.

## Risk

Low-conceptual, moderate-formalization.  `ae_isCFNormal` is classical; the only mathlib friction is
the L²→a.e. subsequence packaging (Borel–Cantelli + monotone squeeze) and the γ≈volume null-set
transfer.  No forbidden import (Birkhoff/CLT not needed).  P(closes B6 cleanly) high.
