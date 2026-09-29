/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Transfer
import NormalNumbers.VandeheyS7Golden

/-!
# S7-L: the tail chain, end to end, from a hypothesis about `‖q φ x‖`

Laps 31–36 reduced the crux's tail cell to a counting statement and corrected its form.  This
module closes the loop: it removes the `Int.fract` from the hypothesis, so that the §7 chain for
the **frozen targets** runs from a statement about the raw quantity `‖q φ x‖` (resp. `‖q (x+φ)‖`),
with no reference to the orbit, the Gauss map, or the expansion of the image.

* `goodDenCountPrim_fract` — the primitive good-denominator count does not see `Int.fract`:
  `‖q · fract r‖ = ‖q r‖` and the numerator shifts by the integer `q⌊r⌋`, which does not change
  its coprimality with `q`.
* `tailFreq_mul_phi_of_goodDenBound`, `tailFreq_add_phi_of_goodDenBound` — for a CF-normal `x`,
  the frequency of digits `≥ T` in the expansion of `φ x` (resp. `x + φ`) is `≤ DΛ/T + ε`,
  given `GoodDenBoundPrim (φ x) D` (resp. `GoodDenBoundPrim (x + φ) D`) and a Lévy bound.

Combined with `VandeheyS7Golden`, the §7 route now reads: **frozen target ⇐ `GaussACRigidity` +
`OrbitCellBound`, whose tail cell ⇐ a bound on `#{q ≤ Q : ‖q φ x‖ ≤ 2/(Tq), gcd = 1}`** — and the
target sets in that last statement are independent of `x`.

## Guard rule

Content locator: `goodDenCountPrim_fract` at `r ∈ [0,1)` is the identity.  Degenerate case: the
irrationality side conditions come from `VandeheyS7Golden`'s leg 1, so the chain is not vacuous —
`affineImageIrrational_goldenRatio` supplies exactly the `Irrational (φ x)` that the tail theorem
needs.
-/

namespace NormalNumbers.VandeheyS7

open Filter NormalNumbers

/-! ## Removing `Int.fract` from the hypothesis -/

lemma round_mul_fract (q : ℕ) (r : ℝ) :
    round ((q : ℝ) * Int.fract r) = round ((q : ℝ) * r) - (q : ℤ) * ⌊r⌋ := by
  have hid : (q : ℝ) * Int.fract r = (q : ℝ) * r + (-((q : ℤ) * ⌊r⌋) : ℤ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [hid, round_add_intCast]
  ring

lemma coprime_shift {m : ℤ} {q : ℕ} (k : ℤ) (h : Nat.Coprime m.natAbs q) :
    Nat.Coprime (m - (q : ℤ) * k).natAbs q := by
  have hInt : IsCoprime m (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using h
  have hshift : IsCoprime (m - (q : ℤ) * k) (q : ℤ) := by
    refine IsCoprime.of_add_mul_left_left (z := k) ?_
    simpa using hInt
  rw [Int.isCoprime_iff_gcd_eq_one] at hshift
  simpa [Int.gcd, Int.natAbs_natCast] using hshift

lemma coprime_shift_iff {m : ℤ} {q : ℕ} (k : ℤ) :
    Nat.Coprime (m - (q : ℤ) * k).natAbs q ↔ Nat.Coprime m.natAbs q := by
  refine ⟨fun h => ?_, fun h => coprime_shift k h⟩
  have h2 := coprime_shift (m := m - (q : ℤ) * k) (q := q) (-k) h
  have hid : m - (q : ℤ) * k - (q : ℤ) * (-k) = m := by ring
  rwa [hid] at h2

/-- The primitive good-denominator count is insensitive to `Int.fract`. -/
theorem goodDenCountPrim_fract (r : ℝ) (T Q : ℕ) :
    goodDenCountPrim (Int.fract r) T Q = goodDenCountPrim r T Q := by
  rw [goodDenCountPrim, goodDenCountPrim]
  congr 1
  apply Finset.filter_congr
  intro q _
  have hnear : nearInt ((q : ℝ) * Int.fract r) = nearInt ((q : ℝ) * r) := nearInt_mul_fract q r
  have hcop : Nat.Coprime (round ((q : ℝ) * Int.fract r)).natAbs q
      ↔ Nat.Coprime (round ((q : ℝ) * r)).natAbs q := by
    rw [round_mul_fract]
    exact coprime_shift_iff _
  rw [hnear, hcop]

/-- Consequently the Diophantine hypothesis may be stated for the raw multiplier. -/
theorem goodDenBoundPrim_fract_iff (r : ℝ) (D : ℝ) :
    GoodDenBoundPrim (Int.fract r) D ↔ GoodDenBoundPrim r D := by
  unfold GoodDenBoundPrim
  constructor
  · intro h T hT
    filter_upwards [h T hT] with Q hQ
    rwa [goodDenCountPrim_fract] at hQ
  · intro h T hT
    filter_upwards [h T hT] with Q hQ
    rwa [goodDenCountPrim_fract]

/-! ## The frozen targets -/

/-- **The tail chain for `φ x`, end to end.**  For a CF-normal `x`, a bound on the number of
primitive `T`-good denominators of `φ x` — a statement about the `x`-independent sets
`{u : ‖q φ u‖ ≤ 2/(Tq)}` — plus any Lévy bound gives the `O(1/T)` tail frequency the crux
demands. -/
theorem tailFreq_mul_phi_of_goodDenBound {x : ℝ} (hx : IsCFNormal (Int.fract x)) {D Λ : ℝ}
    (hD : 0 ≤ D) (hgd : GoodDenBoundPrim (Real.goldenRatio * x) D)
    (hL : LevyBound (Int.fract (Real.goldenRatio * x)) Λ) {T : ℕ} (hT : 1 ≤ T)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      blockCount (cellSet [] T) p (Int.fract (Real.goldenRatio * x)) / p ≤ (D / T) * Λ + ε := by
  have hirr : Irrational (Real.goldenRatio * x) := by
    have := affineImageIrrational_goldenRatio x hx
    simpa using this
  obtain ⟨hfirr, hmem⟩ := irrational_fract_mem hirr
  exact tailFreq_le_of_goodDenBoundPrim hfirr hmem hD
    ((goodDenBoundPrim_fract_iff _ _).2 hgd) hL hT hε

/-- **The tail chain for `x + φ`, end to end.** -/
theorem tailFreq_add_phi_of_goodDenBound {x : ℝ} (hx : IsCFNormal (Int.fract x)) {D Λ : ℝ}
    (hD : 0 ≤ D) (hgd : GoodDenBoundPrim (x + Real.goldenRatio) D)
    (hL : LevyBound (Int.fract (x + Real.goldenRatio)) Λ) {T : ℕ} (hT : 1 ≤ T)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      blockCount (cellSet [] T) p (Int.fract (x + Real.goldenRatio)) / p ≤ (D / T) * Λ + ε := by
  have hirr : Irrational (x + Real.goldenRatio) := by
    have := affineImageIrrational_add_goldenRatio x hx
    simpa using this
  obtain ⟨hfirr, hmem⟩ := irrational_fract_mem hirr
  exact tailFreq_le_of_goodDenBoundPrim hfirr hmem hD
    ((goodDenBoundPrim_fract_iff _ _).2 hgd) hL hT hε

section Audit

#print axioms goodDenCountPrim_fract
#print axioms goodDenBoundPrim_fract_iff
#print axioms tailFreq_mul_phi_of_goodDenBound
#print axioms tailFreq_add_phi_of_goodDenBound

end Audit

end NormalNumbers.VandeheyS7
