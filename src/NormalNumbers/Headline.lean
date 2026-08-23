/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs
import NormalNumbers.CFDigitLaw

/-!
# B5′ headline statement surface (judge-frozen)

The exported destination of expedition B5′ (`KHINCHIN.md`), frozen by the
judge (`JUDGE.md`, 2026-08-23) so the campaign proves toward a statement it
does not own.  Two tiers, both stated in **witness-existence form** — the
construction (`xstar`, its schedule, and any future digit-cap re-plumbing
for the Khinchin graft) is deliberately NOT named here, so W6's capped
rebuild discharges the same frozen statements:

* `exists_absolutely_normal_cf_normal` — **Tier 1 = the Becher–Yuhjtman
  theorem** (IMRN 2019, arXiv:1704.03622, minus the efficiency claim):
  a real that is absolutely normal AND CF-normal.  Apparently the first
  formalization of this theorem in any prover (landscape survey
  2026-08-23, `KHINCHIN.md`).
* `exists_absolutely_normal_cf_normal_khinchin` — **Tier 2 = the
  expedition headline**: additionally Khinchin-typical.  The conjunction
  is apparently new even on paper (`KHINCHIN.md` "Apparent literature
  gap").

Definitions frozen with them: `IsAbsolutelyNormal` (Track A's full
`IsNormal` in every base `b ≥ 2` — NOT mere simple normality; the Pillai
powers-equivalence, or direct block frequencies, is part of the Tier-1
obligation), `IsCFNormal` (every genuine CF pattern occurs with
window-frequency `γ(I_v)`, the B–Y §2.2 form), `khinchinK₀` (Khinchin's
constant as the tprod), `KhinchinTypical` (geometric mean of the CF digits
→ `K₀`).

Hand-checked anchors (frozen with the statements): overlapping window
counting (`countOccurrences [1,1] [1,1,1] = 2`); the `K₀` factor at digit
`a = 1` is `(4/3)^{log₂ 1} = 1` and at `a = 2` is `(9/8)^{log₂ 2} = 9/8` —
these pin the tprod's index alignment (index `k` ↦ digit `k+1`).
-/

namespace NormalNumbers

open MeasureTheory

/-! ## Anchors (kernel-checked) -/

example : countOccurrences [1] [1, 2, 1] = 2 := by decide
example : countOccurrences [1, 1] [1, 1, 1] = 2 := by decide
example : (1 + 1 / (1 * 3) : ℝ) ^ Real.logb 2 1 = 1 := by
  rw [Real.logb_one, Real.rpow_zero]
example : (1 + 1 / (2 * 4) : ℝ) ^ Real.logb 2 2 = 9 / 8 := by
  rw [Real.logb_self_eq_one (by norm_num), Real.rpow_one]
  norm_num

/-! ## The frozen definitions -/

/-- Absolutely normal: (fully) normal in every integer base `b ≥ 2`
(Track A's `IsNormal` — all blocks, correct frequencies; NOT merely
simple normality). -/
def IsAbsolutelyNormal (x : ℝ) : Prop := ∀ b : ℕ, 2 ≤ b → IsNormal b x

/-- CF-normal (B–Y §2.2 window-frequency form): every genuine finite CF
pattern `v` occurs among the windows of the length-`p` CF-digit prefix of
`x` with frequency tending to `γ(I_v)`. -/
def IsCFNormal (x : ℝ) : Prop :=
  ∀ v : List ℕ, v ≠ [] → (∀ a ∈ v, 1 ≤ a) →
    Filter.Tendsto
      (fun p => (countOccurrences v ((List.range p).map (cfDigit x)) : ℝ) / p)
      Filter.atTop (nhds ((gaussMeasure (cfCylinder v)).toReal))

/-- **Khinchin's constant** `K₀ = ∏_{a≥1} (1 + 1/(a(a+2)))^{log₂ a}
≈ 2.685…`, as a `tprod` over `k : ℕ` with digit value `a = k + 1`
(anchors above pin the alignment). -/
noncomputable def khinchinK₀ : ℝ :=
  ∏' k : ℕ, (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) ^ Real.logb 2 ((k : ℝ) + 1)

/-- Khinchin-typical: the geometric mean of the CF digits tends to `K₀`. -/
def KhinchinTypical (x : ℝ) : Prop :=
  Filter.Tendsto
    (fun n => (∏ i ∈ Finset.range n, (cfDigit x i : ℝ)) ^ (1 / (n : ℝ)))
    Filter.atTop (nhds khinchinK₀)

/-! ## The frozen headline statements -/

/-- **Tier 1 — the Becher–Yuhjtman theorem** (IMRN 2019, minus
efficiency): there is a real number that is absolutely normal and
CF-normal.  Witness: `xstar` (its machinery lives in the `CF*`/`TBrick*`
modules; this statement deliberately does not name it). -/
theorem exists_absolutely_normal_cf_normal :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ IsCFNormal x := by
  sorry

/-- **Tier 2 — the expedition headline** (the conjunction apparently new
even on paper): there is a real number that is absolutely normal,
CF-normal, and Khinchin-typical. -/
theorem exists_absolutely_normal_cf_normal_khinchin :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ IsCFNormal x ∧ KhinchinTypical x := by
  sorry

end NormalNumbers
