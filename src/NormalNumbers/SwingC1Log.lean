import NormalNumbers.CastingOut

/-!
# Swing at C1, logarithmic density

The log-averaged twin of `ConjC1`.  Logarithmic averaging is where the Tao (2016) two-point and
Tao–Teräväinen (2019) odd-order Elliott results live, so this is where published results might
already carry C1.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- Logarithmic frequency of windows whose digit sum is `≡ r (mod b−1)`. -/
noncomputable def castFreqLog (b : ℕ) (x : ℝ) (L r N : ℕ) : ℝ :=
  (∑ n ∈ (range N).filter (fun n => windowDigitSum b x n L % (b - 1) = r), (1 : ℝ) / (n + 1)) /
    ∑ n ∈ range N, (1 : ℝ) / (n + 1)

/-- The normal casting-out law in logarithmic density. -/
def CastLawLog (b : ℕ) (x : ℝ) (L : ℕ) : Prop :=
  ∀ r < b - 1, Tendsto (castFreqLog b x L r) atTop (𝓝 (normalCastLaw b L r))

/-- **C1-log.** -/
def ConjC1Log : Prop := ∀ b, 3 ≤ b → ∀ L, CastLawLog b (primeLambertAtBase b) L

/-- Natural density implies logarithmic density (partial summation).  Sanity bridge. -/
theorem castLawLog_of_castLaw (b : ℕ) (x : ℝ) (L : ℕ) (h : CastLaw b x L) :
    CastLawLog b x L := by
  sorry

/-- First rung: single digits (`L = 1`). -/
theorem castLawLog_one (b : ℕ) (hb : 3 ≤ b) : CastLawLog b (primeLambertAtBase b) 1 := by
  sorry

theorem conjC1Log : ConjC1Log := by
  sorry

end NormalNumbers.CastingOut
