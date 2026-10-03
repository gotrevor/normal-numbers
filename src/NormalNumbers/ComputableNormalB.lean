/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ComputableNormal
import NormalNumbers.VisitDeviationB

/-!
# Polynomial decay + computable lower approximations ⇒ a computable coin sequence whose image
is normal in every base

All-bases version of `ComputableNormal.exists_computable_normal_of_digits`.  For `b` not a power
of `2`, `⌊G ω · bᵐ⌋` is not a function of a finite coin prefix, so the tests read a computable
**lower approximation** `A p ≤ G ω ≤ A p + 2^{-|p|}` (`p` a prefix of `ω`) through its exact
floors `Ψ b m p = ⌊A p · bᵐ⌋`.

Level `n` (`N = n^14`) tests every base `2 ≤ b ≤ n`:
* block tests `(ℓ, v)`, `1 ≤ ℓ`, `b^ℓ ≤ n`: approximate visit count `Vc` within `3N/(4n)` of
  `N b^{-ℓ}`;
* a top test: the approximate orbit points at indices `< N + n` fall in the top depth-`n` cell
  `[1 − b^{-n}, 1)` at most `N/(4n)` times.
A floor mismatch between `G ω` and `A p` at exponent `E` forces the approximate point at index
`E` into that top cell (`top_of_floor_ne`), so passing the top test bounds the error of every
block count by `N/(4n)` (`Vtrue_sub_Vc_le`).  Conversely an approximate top visit is a true visit
to `[0, b^{-n}) ∪ [1 − b^{-n}, 1)` (`orbit_mem_of_top`), which `visit_deviation_b` controls.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.ComputableNormalB

open Derandomize DecayAeNormal VisitDeviation VisitDeviationB ComputableNormal

/-! ## Orbit cells as floor residues, base `b` -/

/-- **Orbit block membership is a floor residue**, base `b`. -/
theorem orbit_mem_iff_b (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : 0 ≤ x) (k ℓ v : ℕ) :
    orbit b x k ∈ Set.Ico ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) ↔
      ⌊x * (b : ℝ) ^ (k + ℓ)⌋₊ % b ^ ℓ = v := by
  have hb0 : (0 : ℝ) < b := by positivity
  set y := x * (b : ℝ) ^ k with hydef
  have hy0 : 0 ≤ y := by positivity
  have horb : orbit b x k = Int.fract y := by simp [orbit, hydef]
  set f := Int.fract y
  have hf0 : 0 ≤ f := Int.fract_nonneg y
  have hf1 : f < 1 := Int.fract_lt_one y
  have hyf : y = (⌊y⌋₊ : ℝ) + f := by
    simp only [f, Int.fract]
    rw [← Int.natCast_floor_eq_floor hy0]; push_cast; ring
  have hP : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  set c := ⌊f * (b : ℝ) ^ ℓ⌋₊
  have hc : c < b ^ ℓ := by
    have : f * (b : ℝ) ^ ℓ < (b ^ ℓ : ℕ) := by push_cast; nlinarith
    exact (Nat.floor_lt (by positivity)).2 this
  have hfloor : ⌊x * (b : ℝ) ^ (k + ℓ)⌋₊ = ⌊y⌋₊ * b ^ ℓ + c := by
    have : x * (b : ℝ) ^ (k + ℓ) = f * (b : ℝ) ^ ℓ + ((⌊y⌋₊ * b ^ ℓ : ℕ) : ℝ) := by
      rw [pow_add, ← mul_assoc, ← hydef]
      conv_lhs => rw [hyf]
      push_cast; ring
    rw [this, Nat.floor_add_natCast (by positivity)]
    ring
  rw [hfloor, Nat.mul_add_mod_of_lt hc, horb]
  rw [Set.mem_Ico, div_le_iff₀ hP, lt_div_iff₀ hP, eq_comm]
  simp only [c]
  rw [eq_comm, Nat.floor_eq_iff (by positivity)]

/-- The top depth-`r` cell: `fract(y) ≥ 1 − b^{-r}` iff the depth-`r` digit block is all `b−1`. -/
theorem top_iff (b : ℕ) (hb : 2 ≤ b) (a : ℝ) (ha : 0 ≤ a) (E r : ℕ) :
    1 - 1 / (b : ℝ) ^ r ≤ Int.fract (a * (b : ℝ) ^ E) ↔
      ⌊a * (b : ℝ) ^ (E + r)⌋₊ % b ^ r = b ^ r - 1 := by
  have hb1 : 1 ≤ b ^ r := Nat.one_le_pow _ _ (by omega)
  rw [← orbit_mem_iff_b b hb a ha E r (b ^ r - 1)]
  have hP : (0 : ℝ) < (b : ℝ) ^ r := by positivity
  simp only [orbit, Set.mem_Ico, Nat.cast_sub hb1, Nat.cast_pow, Nat.cast_one]
  have e1 : ((b : ℝ) ^ r - 1) / (b : ℝ) ^ r = 1 - 1 / (b : ℝ) ^ r := by field_simp
  have e2 : ((b : ℝ) ^ r - 1 + 1) / (b : ℝ) ^ r = 1 := by rw [sub_add_cancel]; field_simp
  rw [e1, e2]
  exact ⟨fun h => ⟨h, Int.fract_lt_one _⟩, fun h => h.1⟩

/-- A floor mismatch forces the approximation into the top cell. -/
theorem top_of_floor_ne (b : ℕ) (hb : 2 ≤ b) {a x : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (E r : ℕ)
    (hη : (x - a) * (b : ℝ) ^ E ≤ 1 / (b : ℝ) ^ r)
    (hne : ⌊x * (b : ℝ) ^ E⌋₊ ≠ ⌊a * (b : ℝ) ^ E⌋₊) :
    ⌊a * (b : ℝ) ^ (E + r)⌋₊ % b ^ r = b ^ r - 1 := by
  rw [← top_iff b hb a ha E r]
  have hbE : (0 : ℝ) < (b : ℝ) ^ E := by positivity
  set X := x * (b : ℝ) ^ E
  set Y := a * (b : ℝ) ^ E
  have hY0 : 0 ≤ Y := by positivity
  have hXY : Y ≤ X := mul_le_mul_of_nonneg_right hax hbE.le
  have hle : ⌊Y⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor hXY
  have hlt : ⌊Y⌋₊ + 1 ≤ ⌊X⌋₊ := by omega
  have h1 : ((⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ X :=
    (Nat.cast_le.2 hlt).trans (Nat.floor_le (hY0.trans hXY))
  have hdiff : X - Y ≤ 1 / (b : ℝ) ^ r := by
    have : X - Y = (x - a) * (b : ℝ) ^ E := by simp only [X, Y]; ring
    rw [this]; exact hη
  have hfr : Int.fract Y = Y - ⌊Y⌋₊ := by
    rw [Int.fract, ← Int.natCast_floor_eq_floor hY0]; push_cast; ring
  rw [hfr]
  push_cast at h1
  linarith

/-- An approximate top visit is a true visit near `0` or near `1`. -/
theorem orbit_mem_of_top (b : ℕ) (hb : 2 ≤ b) {a x : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (j r : ℕ)
    (hη : (x - a) * (b : ℝ) ^ j ≤ 1 / (b : ℝ) ^ r)
    (htop : ⌊a * (b : ℝ) ^ (j + r)⌋₊ % b ^ r = b ^ r - 1) :
    orbit b x j ∈ Set.Ico 0 (1 / (b : ℝ) ^ r) ∨ orbit b x j ∈ Set.Ico (1 - 1 / (b : ℝ) ^ r) 1 := by
  rw [← top_iff b hb a ha j r] at htop
  have hbE : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  set X := x * (b : ℝ) ^ j
  set Y := a * (b : ℝ) ^ j
  have hY0 : 0 ≤ Y := by positivity
  have hXY : Y ≤ X := mul_le_mul_of_nonneg_right hax hbE.le
  have hdiff : X - Y ≤ 1 / (b : ℝ) ^ r := by
    have : X - Y = (x - a) * (b : ℝ) ^ j := by simp only [X, Y]; ring
    rw [this]; exact hη
  have horb : orbit b x j = Int.fract X := rfl
  rw [horb]
  have hfX0 := Int.fract_nonneg X
  have hfX1 := Int.fract_lt_one X
  have hfY1 := Int.fract_lt_one Y
  have hfl : ⌊Y⌋ ≤ ⌊X⌋ := Int.floor_le_floor hXY
  rcases eq_or_lt_of_le hfl with h | h
  · right
    refine ⟨?_, hfX1⟩
    have : Int.fract X = Int.fract Y + (X - Y) := by
      rw [Int.fract, Int.fract, ← h]; ring
    linarith
  · left
    refine ⟨hfX0, ?_⟩
    have h' : (⌊Y⌋ : ℝ) + 1 ≤ ⌊X⌋ := by exact_mod_cast h
    have hX : Int.fract X = X - ⌊X⌋ := rfl
    have hY : Int.fract Y = Y - ⌊Y⌋ := rfl
    linarith

end NormalNumbers.ComputableNormalB
