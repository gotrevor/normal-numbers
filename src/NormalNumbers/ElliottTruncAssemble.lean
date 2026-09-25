import NormalNumbers.ElliottTruncScale
import NormalNumbers.ElliottScaleWindow
import NormalNumbers.ElliottMertensIterate

/-!
# The truncation, assembled into the two real-valued statements the dichotomy consumes

Leaf 2, Case B.  `ElliottTruncScale` supplies the `ℕ`-level facts about `truncRatio`; this module
turns them into the two `ℝ`-level statements used by `ElliottLeafTwo.nonasymptotic_of_affineCM`:

* `discarded_mass_bound` — the harmonic mass thrown away is `≤ 1 + 2 log 2 + (log W)/2^j`.
* `X_le_thinScale_pow` — `X ≤ (thinScale a₁ b₁ X W'')^(2^(j+2))`, i.e. the truncated thin scale is
  a **fixed** power of `X`, which is exactly the hypothesis of
  `ElliottMertensIterate.reciprocalPrimeInterval_iter`.

Plus `primeDefect_thinScale_eq` (the dichotomy may equivalently be stated at `thinScale`, since
`primeDefect` at `0` and at `1` are both the empty sum) and `pretHyp_mono` (the non-pretentiousness
hypothesis of `NonasymptoticLogElliott` is monotone downwards in `A`, which is what lets Case B run
at `A'' = min A W''`).
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottTruncAssemble

open Erdos67b NormalNumbers.ElliottIterSqrt NormalNumbers.ElliottTruncScale
open NormalNumbers.ElliottScaleWindow NormalNumbers.ElliottCaseA
open NormalNumbers.ElliottEulerBound

noncomputable section

theorem log_iterSqrt_le {j W : ℕ} (hW : 1 ≤ W) :
    Real.log ((iterSqrt j W : ℕ) : ℝ) ≤ Real.log (W : ℝ) / (2 ^ j : ℕ) := by
  have hZ1 : 1 ≤ iterSqrt j W := one_le_iterSqrt hW
  have hZR : (1 : ℝ) ≤ ((iterSqrt j W : ℕ) : ℝ) := by exact_mod_cast hZ1
  have hpow : ((iterSqrt j W : ℕ) : ℝ) ^ (2 ^ j : ℕ) ≤ (W : ℝ) := by
    have := iterSqrt_pow_le j W
    have h2 : (((iterSqrt j W) ^ (2 ^ j) : ℕ) : ℝ) ≤ ((W : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h2
    exact h2
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog
  have hden : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ hden]
  push_cast at hlog ⊢
  linarith

/-- **The discarded mass.** -/
theorem discarded_mass_bound {j X W : ℕ} (hW : 4 ≤ W) (hWX : W ≤ X) (hj : 1 ≤ j) :
    ∑ m ∈ Finset.Icc (X / W + 1) (X / truncRatio j X W), (m : ℝ)⁻¹
      ≤ 1 + 2 * Real.log 2 + Real.log (W : ℝ) / (2 ^ j : ℕ) := by
  classical
  set W'' : ℕ := truncRatio j X W with hW''
  set Z : ℕ := truncScale j W with hZ
  have ha : 1 ≤ X / W + 1 := Nat.le_add_left 1 _
  have hmass := NormalNumbers.ElliottWindowTruncate.discarded_mass_le
    (a := X / W + 1) (N := X / W'') ha
  have haR : (0 : ℝ) ≤ Real.log ((X / W + 1 : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast (Nat.le_add_left 1 (X / W))
  have hZ2 : 2 ≤ Z := two_le_truncScale j W
  have hlog2Z : Real.log (((2 * Z : ℕ)) : ℝ) ≤ 2 * Real.log 2 + Real.log (W : ℝ) / (2 ^ j : ℕ) := by
    have h1 : Z ≤ 2 * iterSqrt j W := truncScale_le_two_mul (by omega)
    have h2 : (2 * Z : ℕ) ≤ 4 * iterSqrt j W := by omega
    have h2R : (((2 * Z : ℕ)) : ℝ) ≤ ((4 * iterSqrt j W : ℕ) : ℝ) := by exact_mod_cast h2
    have hpos : (0 : ℝ) < ((2 * Z : ℕ) : ℝ) := by
      have : (0 : ℕ) < 2 * Z := by omega
      exact_mod_cast this
    refine le_trans (Real.log_le_log hpos h2R) ?_
    have hZ1 : 1 ≤ iterSqrt j W := one_le_iterSqrt (by omega)
    have hsplit : ((4 * iterSqrt j W : ℕ) : ℝ) = 4 * ((iterSqrt j W : ℕ) : ℝ) := by push_cast; ring
    rw [hsplit, Real.log_mul (by norm_num) (by
      have : (1 : ℝ) ≤ ((iterSqrt j W : ℕ) : ℝ) := by exact_mod_cast hZ1
      linarith)]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have := log_iterSqrt_le (j := j) (W := W) (by omega)
    linarith
  -- the max is either the lower end (nothing discarded) or `< 2Z`
  have hmax : Real.log ((max (X / W + 1) (X / W'') : ℕ) : ℝ) - Real.log ((X / W + 1 : ℕ) : ℝ)
      ≤ 2 * Real.log 2 + Real.log (W : ℝ) / (2 ^ j : ℕ) := by
    rcases le_total (X / W'') (X / W + 1) with hle | hge
    · rw [max_eq_left hle]
      have hnn : (0 : ℝ) ≤ 2 * Real.log 2 + Real.log (W : ℝ) / (2 ^ j : ℕ) := by
        have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have h2 : (0 : ℝ) ≤ Real.log (W : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ W))
        positivity
      linarith
    · rw [max_eq_right hge]
      have hlt : X / W'' < 2 * Z := by
        rcases div_truncRatio_lt (j := j) (X := X) (W := W) hW hWX hj with hl | heq
        · exact hl
        · exfalso
          rw [hW''] at hge
          rw [heq] at hge
          omega
      have hmono : Real.log ((X / W'' : ℕ) : ℝ) ≤ Real.log (((2 * Z : ℕ)) : ℝ) := by
        rcases Nat.eq_zero_or_pos (X / W'') with h0 | hp
        · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
          have : (0:ℝ) ≤ Real.log ((2*Z : ℕ) : ℝ) := by
            refine Real.log_nonneg ?_
            exact_mod_cast (by omega : 1 ≤ 2 * Z)
          linarith
        · refine Real.log_le_log (by exact_mod_cast hp) ?_
          exact_mod_cast hlt.le
      linarith
  linarith

/-- **The truncated thin scale is a fixed power root of `X`.** -/
theorem X_le_thinScale_pow {a₁ : ℕ} (ha₁ : 0 < a₁) (b₁ : ℤ) {j X W : ℕ}
    (hW : 4 ≤ W) (hWX : W ≤ X) (hj : 1 ≤ j)
    (hbig : 2 * (b₁.natAbs + 1) ^ 2 ≤ iterSqrt j W) :
    X ≤ (thinScale a₁ b₁ X (truncRatio j X W)) ^ (2 ^ (j + 2)) := by
  set W'' : ℕ := truncRatio j X W with hW''
  set ν : ℕ := X / W'' + 1 with hν
  set b : ℕ := b₁.natAbs with hb
  set S : ℕ := thinScale a₁ b₁ X W'' with hS
  have hZν : iterSqrt j W + 1 ≤ ν := by
    have h1 : iterSqrt j W ≤ truncScale j W := le_max_right _ _
    have h2 : truncScale j W ≤ X / W'' := truncScale_le_div hW hWX hj
    omega
  have hνbig : 2 * (b + 1) ^ 2 + 1 ≤ ν := by omega
  -- `S ≥ ν − b` and `ν ≥ 2(b+1)²+1`, hence `ν ≤ 2S ≤ S²`
  have hP : ν ≤ a₁ * (X / W'' + 1) := by
    rw [hν]
    calc X / W'' + 1 = 1 * (X / W'' + 1) := by ring
      _ ≤ a₁ * (X / W'' + 1) := Nat.mul_le_mul_right _ ha₁
  have hSge : a₁ * (X / W'' + 1) - b ≤ S := by
    rw [hS, thinScale]; exact le_max_right _ _
  have hsq1 : b + 1 ≤ (b + 1) ^ 2 := by nlinarith [sq_nonneg b]
  have hlin : 2 ≤ S ∧ ν ≤ 2 * S := by
    constructor <;> omega
  have hνS : ν ≤ S ^ 2 := by
    have h2 : 2 * S ≤ S * S := by nlinarith [hlin.1]
    have := hlin.2
    calc ν ≤ 2 * S := this
      _ ≤ S * S := h2
      _ = S ^ 2 := by ring
  have hX := lt_pow_trunc_low (j := j) (X := X) (W := W) hW hWX hj
  rw [← hν] at hX
  calc X ≤ ν ^ (2 ^ (j + 1)) := hX.le
    _ ≤ (S ^ 2) ^ (2 ^ (j + 1)) := Nat.pow_le_pow_left hνS _
    _ = S ^ (2 ^ (j + 2)) := by
        rw [← pow_mul]
        congr 1
        rw [pow_succ]
        ring

/-- The dichotomy may equivalently be stated at `thinScale`: `primeDefect` at `0` and at `1` are
both empty sums. -/
theorem primeDefect_thinScale_eq (f : ArithmeticFunction ℝ) {a₁ : ℕ} (b₁ : ℤ) (X W : ℕ) :
    primeDefect f (thinScale a₁ b₁ X W)
      = primeDefect f (a₁ * (X / W + 1) - b₁.natAbs) := by
  rcases le_total (a₁ * (X / W + 1) - b₁.natAbs) 1 with h | h
  · have hz : thinScale a₁ b₁ X W = 1 := by rw [thinScale]; omega
    rw [hz]
    rcases Nat.eq_zero_or_pos (a₁ * (X / W + 1) - b₁.natAbs) with hv | hv
    · rw [hv, primeDefect, primeDefect]
      have e0 : Nat.primesLE 0 = (∅ : Finset ℕ) := by decide
      have e1 : Nat.primesLE 1 = (∅ : Finset ℕ) := by decide
      rw [e0, e1]
    · have : a₁ * (X / W + 1) - b₁.natAbs = 1 := by omega
      rw [this]
  · rw [thinScale, max_eq_right h]

end

end NormalNumbers.ElliottTruncAssemble
