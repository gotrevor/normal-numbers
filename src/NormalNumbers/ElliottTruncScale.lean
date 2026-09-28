import NormalNumbers.ElliottIterSqrt
import NormalNumbers.ElliottWindowTruncate
import NormalNumbers.ElliottCaseAThin

/-!
# The truncated window ratio, and the two estimates it is designed for

Leaf 2, Case B.  `truncRatio j X W = min W (X / Z')`, `Z' = max 2 (iterSqrt j W)`, is the window
ratio that repairs the dichotomy-scale obstruction.  Writing `ν = ⌊X/W''⌋ + 1` for the smallest
`n` left in the truncated window, the two facts are:

* `lt_pow_trunc_low` — `X < ν^(2^(j+1))`.  Proof: `X < W''·ν` because `ν` is one past `⌊X/W''⌋`,
  and `W'' ≤ W < (iterSqrt j W + 1)^(2^j) ≤ ν^(2^j)` because `iterSqrt j W + 1 ≤ Z' + 1 ≤ ν`.
  Multiplying, `X < ν^(2^j+1) ≤ ν^(2^(j+1))`.  **No case split on the shape of the window is
  needed** — whichever of `⌊X/W⌋` and `Z'` is the larger, `ν` dominates it.
* `discarded_mass_le_log` — the mass thrown away is `≤ 1 + 2 log 2 + (log W)/2^j`, because
  `⌊X/W''⌋ < 2Z'` and `Z' ≤ 2·iterSqrt j W` with `(iterSqrt j W)^(2^j) ≤ W`.

Together with `sqrt_le_truncRatio` (`√W ≤ W''`, so `log W'' ≥ (1/2) log W`) these are everything
Case B needs about the truncation.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottTruncScale

open Erdos67b NormalNumbers.ElliottIterSqrt

noncomputable section

/-- The truncation scale: a `2^j`-th root of `W`, clamped below at `2`. -/
def truncScale (j W : ℕ) : ℕ := max 2 (iterSqrt j W)

theorem two_le_truncScale (j W : ℕ) : 2 ≤ truncScale j W := le_max_left _ _

theorem truncScale_le_two_mul {j W : ℕ} (hW : 1 ≤ W) :
    truncScale j W ≤ 2 * iterSqrt j W := by
  have h1 : 1 ≤ iterSqrt j W := one_le_iterSqrt hW
  rw [truncScale]
  omega

/-- The truncated window ratio. -/
def truncRatio (j X W : ℕ) : ℕ := min W (X / truncScale j W)

theorem truncRatio_le (j X W : ℕ) : truncRatio j X W ≤ W := min_le_left _ _

/-- `√W ≤ W''`, for `j ≥ 1` and `W ≥ 4`: the truncation never shrinks the window ratio below the
square root, so `log W'' ≥ (1/2) log W`. -/
theorem sqrt_le_truncRatio {j X W : ℕ} (hj : 1 ≤ j) (hW : 4 ≤ W) (hWX : W ≤ X) :
    Nat.sqrt W ≤ truncRatio j X W := by
  have hZle : iterSqrt j W ≤ Nat.sqrt W := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [iterSqrt_succ]
    exact iterSqrt_le i (Nat.sqrt W)
  have hs2 : 2 ≤ Nat.sqrt W := by
    have : 2 * 2 ≤ W := by omega
    exact Nat.le_sqrt'.mpr this
  have hZ' : truncScale j W ≤ Nat.sqrt W := by
    rw [truncScale]; omega
  have hsq : Nat.sqrt W * Nat.sqrt W ≤ W := Nat.sqrt_le W
  have h1 : Nat.sqrt W ≤ X / truncScale j W := by
    refine (Nat.le_div_iff_mul_le (by have := two_le_truncScale j W; omega)).mpr ?_
    calc Nat.sqrt W * truncScale j W ≤ Nat.sqrt W * Nat.sqrt W :=
          Nat.mul_le_mul_left _ hZ'
      _ ≤ W := hsq
      _ ≤ X := hWX
  have h2 : Nat.sqrt W ≤ W := Nat.sqrt_le_self W
  rw [truncRatio]
  omega

theorem truncRatio_pos {j X W : ℕ} (hW : 4 ≤ W) (hWX : W ≤ X) (hj : 1 ≤ j) :
    0 < truncRatio j X W := by
  have h := sqrt_le_truncRatio hj hW hWX
  have : 2 ≤ Nat.sqrt W := Nat.le_sqrt'.mpr (by omega)
  omega

/-- `Z' ≤ ⌊X/W''⌋`: the truncation really does raise the bottom of the window to `Z'`. -/
theorem truncScale_le_div {j X W : ℕ} (hW : 4 ≤ W) (hWX : W ≤ X) (hj : 1 ≤ j) :
    truncScale j W ≤ X / truncRatio j X W := by
  have hpos : 0 < truncRatio j X W := truncRatio_pos hW hWX hj
  refine (Nat.le_div_iff_mul_le hpos).mpr ?_
  have hle : truncRatio j X W ≤ X / truncScale j W := min_le_right _ _
  have hZpos : 0 < truncScale j W := by have := two_le_truncScale j W; omega
  calc truncScale j W * truncRatio j X W
      ≤ truncScale j W * (X / truncScale j W) := Nat.mul_le_mul_left _ hle
    _ = (X / truncScale j W) * truncScale j W := Nat.mul_comm _ _
    _ ≤ X := Nat.div_mul_le_self _ _

/-- **The first designed estimate.**  `X < ν^(2^(j+1))`, `ν = ⌊X/W''⌋ + 1`. -/
theorem lt_pow_trunc_low {j X W : ℕ} (hW : 4 ≤ W) (hWX : W ≤ X) (hj : 1 ≤ j) :
    X < (X / truncRatio j X W + 1) ^ (2 ^ (j + 1)) := by
  set W'' : ℕ := truncRatio j X W with hW''
  set ν : ℕ := X / W'' + 1 with hν
  have hpos : 0 < W'' := truncRatio_pos hW hWX hj
  have hstep1 : X < W'' * ν := ElliottCaseAThin.lt_mul_div_add_one hpos
  have hZν : iterSqrt j W + 1 ≤ ν := by
    have h1 : iterSqrt j W ≤ truncScale j W := le_max_right _ _
    have h2 : truncScale j W ≤ X / W'' := truncScale_le_div hW hWX hj
    omega
  have hstep2 : W'' ≤ ν ^ (2 ^ j) := by
    have hWlt : W < (iterSqrt j W + 1) ^ (2 ^ j) := lt_iterSqrt_succ_pow j W
    have hmono : (iterSqrt j W + 1) ^ (2 ^ j) ≤ ν ^ (2 ^ j) := Nat.pow_le_pow_left hZν _
    have : W'' ≤ W := truncRatio_le j X W
    omega
  have hcomb : X < ν ^ (2 ^ j) * ν := by
    calc X < W'' * ν := hstep1
      _ ≤ ν ^ (2 ^ j) * ν := Nat.mul_le_mul_right _ hstep2
  have hexp : ν ^ (2 ^ j) * ν = ν ^ (2 ^ j + 1) := by rw [pow_succ]
  have hle : ν ^ (2 ^ j + 1) ≤ ν ^ (2 ^ (j + 1)) := by
    refine Nat.pow_le_pow_right (by omega) ?_
    have : (1 : ℕ) ≤ 2 ^ j := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  omega

/-- `⌊X/W''⌋ < 2Z'`. -/
theorem div_truncRatio_lt {j X W : ℕ} (hW : 4 ≤ W) (hWX : W ≤ X) (hj : 1 ≤ j) :
    X / truncRatio j X W < 2 * truncScale j W ∨ truncRatio j X W = W := by
  rcases eq_or_ne (truncRatio j X W) W with heq | hne
  · exact Or.inr heq
  · left
    have hmin : truncRatio j X W = X / truncScale j W := by
      rw [truncRatio] at hne ⊢
      rcases min_cases W (X / truncScale j W) with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hne
      · exact h
    have hZpos : 0 < truncScale j W := by have := two_le_truncScale j W; omega
    set q : ℕ := X / truncScale j W with hq
    have hqpos : 0 < q := by
      rw [← hmin] at *
      exact truncRatio_pos hW hWX hj
    have hXlt : X < (q + 1) * truncScale j W := by
      have h := ElliottCaseAThin.lt_mul_div_add_one (X := X) hZpos
      rw [← hq] at h
      calc X < truncScale j W * (q + 1) := h
        _ = (q + 1) * truncScale j W := Nat.mul_comm _ _
    rw [hmin]
    refine (Nat.div_lt_iff_lt_mul hqpos).mpr ?_
    calc X < (q + 1) * truncScale j W := hXlt
      _ = q * truncScale j W + truncScale j W := by ring
      _ ≤ q * truncScale j W + q * truncScale j W := by
          have : truncScale j W ≤ q * truncScale j W := Nat.le_mul_of_pos_left _ hqpos
          omega
      _ = 2 * truncScale j W * q := by ring

end

end NormalNumbers.ElliottTruncScale
