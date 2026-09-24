import NormalNumbers.Stoneham
import NormalNumbers.AbelianNormal

/-!
# Failures of 2026-09-23, formalized

1. **α₂,₃ is not even simply normal in base 6** (so no abelian-normal "natural separation").
   In base 6 the term `1/(3ᵐ 2^{3ᵐ}) = 3^{3ᵐ−m}/6^{3ᵐ}` occupies positions `≈ [0.387·3ᵐ, 3ᵐ]`, and
   the next term starts near `1.161·3ᵐ`.  So the digits at positions `(3ᵐ, 1.1·3ᵐ]` are all `0`:
   below position `p`, the head `Σ_{k≤m}` times `6ᵖ` is an integer, and
   `6ᵖ · Σ_{k>m} < 1` because `1.1·log₂6 ≈ 2.84 < 3`.  Hence at `N ≈ 1.1·3ᵐ` the zero frequency
   is `≥ (1/6 + 0.1·5/6)/1.1 − o(1) ≈ 0.227`, not `1/6`.  Bailey–Borwein (2012) first proved
   base-6 non-normality; this is that mechanism, not a new result.  Probe:
   `probes/abelian_stoneham_and_times3.py`, which measures freq(0) = .3217 at N = 2·10⁵.
2. **×3 abelian lifting**, frozen but PARKED.  The hexSwap example (`AbelianBinaryExample.lean`)
   does not refute it: 3ξ is far from abelian-normal in the probe.  A dimension count suggests a
   single multiplier is too weak; the all-odd-multiplier version is plausible and may be classical.
-/

open Finset Filter Topology

namespace NormalNumbers.Failures

/-- **Forced zeros.**  For all large `m`, the base-6 digits of `α₂,₃` with index in
`[3ᵐ, 11·3ᵐ/10)` are `0` (index `i` is position `i + 1`). -/
theorem stoneham23_digit_six_eq_zero :
    ∃ M : ℕ, ∀ m ≥ M, ∀ i : ℕ, 3 ^ m ≤ i → i < 11 * 3 ^ m / 10 →
      digitOf 6 (Int.fract stoneham23) i = 0 := by
  sorry

/-- **α₂,₃ is not simply normal in base 6**: the frequency of the digit `0` does not tend to
`1/6`. -/
theorem not_simplyNormal_six_stoneham23 :
    ¬ Tendsto (fun n : ℕ =>
        (countOccurrences [0] ((List.range n).map (digitOf 6 (Int.fract stoneham23))) : ℝ) / n)
      atTop (𝓝 (1 / 6)) := by
  sorry

/-- Hence not normal in base 6 (Bailey–Borwein 2012). -/
theorem not_isNormal_six_stoneham23 : ¬ IsNormal 6 stoneham23 := by
  sorry

/-- **×3 abelian lifting (PARKED, ~20%).** -/
def TimesThreeLifting : Prop :=
  ∀ x : ℝ, Abelian.IsAbelianNormalTwo (digitOf 2 (Int.fract x)) →
    Abelian.IsAbelianNormalTwo (digitOf 2 (Int.fract (3 * x))) → IsNormal 2 x

/-- **Odd-multiplier abelian lifting (open, ~70%, literature check pending).** -/
def OddMultiplierLifting : Prop :=
  ∀ x : ℝ, (∀ q : ℕ, Odd q → Abelian.IsAbelianNormalTwo (digitOf 2 (Int.fract ((q : ℝ) * x)))) →
    IsNormal 2 x

theorem oddMultiplierLifting_of_timesThree (h : TimesThreeLifting) : OddMultiplierLifting := by
  sorry

end NormalNumbers.Failures
