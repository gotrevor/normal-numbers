import NormalNumbers.C3MrtPhaseDynamics
open Filter Finset
namespace NormalNumbers.CastingOut
theorem depthPhase_level_shift {b : ℕ} (hb : 0 < b) (K n : ℕ) (h : ℤ) :
    ((b : ℝ) * (h : ℝ)) * depthPhase b (K + 1) n
      = (h : ℝ) * depthPhase b K (n + 1) + (h : ℝ) * (omegaNat (n + 1) : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [depthPhase, depthPhase, Finset.sum_range_succ', mul_add,
    Finset.mul_sum, Finset.mul_sum]
  have hterm : ∀ i ∈ range K,
      (b : ℝ) * (h : ℝ) * ((omegaNat (n + (i + 1) + 1) : ℝ) / (b : ℝ) ^ (i + 1 + 1))
        = (h : ℝ) * ((omegaNat (n + 1 + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)) := by
    intro i _
    have e : n + (i + 1) + 1 = n + 1 + i + 1 := by omega
    rw [e]
    have : (b : ℝ) ^ (i + 1 + 1) = (b : ℝ) ^ (i + 1) * (b : ℝ) := by ring
    rw [this]
    field_simp
  rw [Finset.sum_congr rfl hterm]
  have e0 : n + 0 + 1 = n + 1 := by omega
  rw [e0]
  field_simp
  ring

theorem ee_depthPhase_level_shift {b : ℕ} (hb : 0 < b) (K n : ℕ) (h : ℤ) :
    ee (((((b : ℤ) * h : ℤ) : ℝ) * depthPhase b (K + 1) n : ℝ) : ℂ)
      = ee ((((h : ℝ) * depthPhase b K (n + 1) : ℝ)) : ℂ) := by
  have hid := depthPhase_level_shift hb K n h
  have hcast : (((b : ℤ) * h : ℤ) : ℝ) * depthPhase b (K + 1) n
      = (h : ℝ) * depthPhase b K (n + 1) + ((h * (omegaNat (n + 1) : ℤ) : ℤ) : ℝ) := by
    push_cast
    linarith [hid]
  rw [hcast]
  have hpush : ((((h : ℝ) * depthPhase b K (n + 1)
      + ((h * (omegaNat (n + 1) : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ)
      = ((((h : ℝ) * depthPhase b K (n + 1) : ℝ)) : ℂ)
        + (((h * (omegaNat (n + 1) : ℤ) : ℤ) : ℂ)) := by push_cast; ring
  rw [hpush, ee_add, ee_int, mul_one]
end NormalNumbers.CastingOut
