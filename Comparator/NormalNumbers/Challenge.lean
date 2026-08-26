/-
Comparator CHALLENGE for the Wall theorem and conditional ln-two theorem.

This file imports ONLY Mathlib and renders the project's real definitions under
their real fully-qualified names. The bodies are deliberately duplicated from
the development: comparator verifies that this independent, human-auditable
rendering is byte-identical to the constants used by the proved theorems.
-/
import Mathlib

set_option warningAsError false

namespace NormalNumbers

/-- Number of overlapping occurrences of `w` as a contiguous block of `l`. -/
def countOccurrences (w l : List ℕ) : ℕ :=
  l.tails.countP (w.isPrefixOf ·)

/-- Normality of a digit sequence in base `b`. -/
def IsNormalSequence (b : ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < b) →
    Filter.Tendsto
      (fun n => (countOccurrences w ((List.range n).map s) : ℝ) / n)
      Filter.atTop (nhds ((b : ℝ) ^ w.length)⁻¹)

/-- The standard `i`-th base-`b` digit of `x ∈ [0,1)`. -/
noncomputable def digitOf (b : ℕ) (x : ℝ) (i : ℕ) : ℕ :=
  (⌊x * (b : ℝ) ^ (i + 1)⌋).toNat % b

/-- Real-number normality, read from the fractional part. -/
def IsNormal (b : ℕ) (x : ℝ) : Prop :=
  IsNormalSequence b (digitOf b (Int.fract x))

open Classical in
/-- Visits of the first `n` terms of `u` to `[a,c)`. -/
noncomputable def visitCount (u : ℕ → ℝ) (a c : ℝ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun k => u k ∈ Set.Ico a c).card

/-- Equidistribution modulo one by interval visit frequencies. -/
def Equidistributed (u : ℕ → ℝ) : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ 1 →
    Filter.Tendsto (fun n => (visitCount u a c n : ℝ) / n)
      Filter.atTop (nhds (c - a))

/-- The multiply-by-`b` orbit modulo one. -/
noncomputable def orbit (b : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  Int.fract (x * (b : ℝ) ^ n)

/-- The Bailey--Crandall surrogate orbit for `ln 2`. -/
noncomputable def lnTwoOrbit : ℕ → ℝ
  | 0 => 0
  | n + 1 => Int.fract (2 * lnTwoOrbit n + 1 / (n + 1))

/-! ### Non-vacuity anchors -/

/-- Overlapping blocks are counted at both starting positions. -/
theorem countOccurrences_overlap_anchor :
    countOccurrences [0, 0] [0, 0, 0] = 2 := by
  decide +kernel

/-- The orbit is genuine multiplication modulo one. -/
theorem orbit_two_one_third_anchor :
    orbit 2 ((1 : ℝ) / 3) 1 = (2 : ℝ) / 3 := by
  norm_num [orbit, Int.fract]

/-- The surrogate recurrence has the intended first nonzero value. -/
theorem lnTwoOrbit_two_anchor : lnTwoOrbit 2 = (1 : ℝ) / 2 := by
  norm_num [lnTwoOrbit, Int.fract]

/-! ### Headline results -/

/-- Wall's theorem: base-`b` normality is equivalent to equidistribution of the
multiply-by-`b` orbit. -/
theorem isNormal_iff_equidistributed_orbit (b : ℕ) (hb : 2 ≤ b) (x : ℝ) :
    IsNormal b x ↔ Equidistributed (orbit b x) := by
  sorry

/-- Bailey--Crandall reduction: equidistribution of the explicit surrogate orbit
implies base-two normality of `ln 2`. The hypothesis remains an open conjecture;
the conditional theorem itself is proved. -/
theorem isNormal_log_two_of_equidistributed
    (h : Equidistributed lnTwoOrbit) : IsNormal 2 (Real.log 2) := by
  sorry

end NormalNumbers
