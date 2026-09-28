import NormalNumbers.ElliottCaseAThin

/-!
# The thin scale and the logarithmic ratio it controls

Leaf 2, Case B.  `ElliottStageStep.norm_le_of_reduced` pays for its divisor truncation with
`(a+|b|)·(1 + log Y − log L)·εt`, where `Y = aX+|b|` is the largest value of the affine form on the
window and `L` is any lower bound for its values there.  For this to be `O(εt log W)` — which is
what an `ε log W` conclusion needs — `L` must be the *thin* scale `a(⌊X/W⌋+1) − |b|`, not `1`:
with `L = 1` the cost is `O(εt log X)`, and in a thin window `log X` is not `O(log W)`.

`thinScale` is that scale, clamped at `1` so that it is usable with no side condition.  The two
facts about it:

* `thinScale_le_integerAffine` — it really is a lower bound on the window (`ElliottCaseAThin`).
* `logRatio_le` — `1 + log Y − log (thinScale) ≤ log W + logRatioConst a b`, an **absolute**
  constant depending only on `(a, |b|)`.  The proof is a dichotomy on `⌊X/W⌋ ≥ 2|b|+2`:
  thin gives `Y ≤ (4W+1)·L` from `ElliottCaseAThin.div_le_four_mul`, thick gives
  `X < W(2|b|+2)` hence `Y ≤ W·(a(2|b|+2)+|b|)` directly, with `log L ≥ 0`.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottScaleWindow

open Erdos67b

noncomputable section

/-- The thin scale `max 1 (a(⌊X/W⌋+1) − |b|)`. -/
def thinScale (a : ℕ) (b : ℤ) (X W : ℕ) : ℕ := max 1 (a * (X / W + 1) - b.natAbs)

theorem one_le_thinScale (a : ℕ) (b : ℤ) (X W : ℕ) : 1 ≤ thinScale a b X W :=
  le_max_left _ _

/-- The thin scale is a lower bound for the affine form on the window. -/
theorem thinScale_le_integerAffine {a : ℕ} (ha : 0 < a) (b : ℤ) {X W : ℕ} (hW : 0 < W)
    {n : ℕ} (hn : n ∈ elliottLogWindow X W) (hpos : 0 < integerAffine a b n) :
    ((thinScale a b X W : ℕ) : ℤ) ≤ integerAffine a b n := by
  have hbase := ElliottCaseAThin.le_integerAffine_of_mem_window ha b hW hn hpos
  rw [thinScale]
  rcases le_total (a * (X / W + 1) - b.natAbs) 1 with h | h
  · rw [max_eq_left h]
    simp only [Nat.cast_one]
    omega
  · rw [max_eq_right h]
    exact hbase

/-- The thin scale never exceeds the top scale `Y = aX + |b|`. -/
theorem thinScale_le_top {a : ℕ} (ha : 0 < a) (b : ℤ) {X W : ℕ} (hW : 2 ≤ W) (hX : 2 ≤ X) :
    thinScale a b X W ≤ a * X + b.natAbs := by
  have hq : X / W + 1 ≤ X := by
    have : X / W ≤ X / 2 := Nat.div_le_div_left hW (by norm_num)
    omega
  have h1 : a * (X / W + 1) ≤ a * X := Nat.mul_le_mul_left _ hq
  have h2 : 1 ≤ a * X := by
    have := Nat.mul_le_mul (show 1 ≤ a from ha) (show 1 ≤ X by omega)
    omega
  rw [thinScale]
  omega

/-- The absolute constant in `logRatio_le`. -/
def logRatioConst (a : ℕ) (b : ℤ) : ℝ :=
  1 + Real.log ((5 * (a * (2 * b.natAbs + 2) + b.natAbs + 1) : ℕ) : ℝ)

theorem logRatioConst_nonneg (a : ℕ) (b : ℤ) : 0 ≤ logRatioConst a b := by
  have : (1 : ℝ) ≤ ((5 * (a * (2 * b.natAbs + 2) + b.natAbs + 1) : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ 5 * (a * (2 * b.natAbs + 2) + b.natAbs + 1) := by omega
    exact_mod_cast this
  have := Real.log_nonneg this
  rw [logRatioConst]; linarith

/-- **The logarithmic ratio bound.**  `1 + log Y − log L ≤ log W + logRatioConst a b`, uniformly
in `X` and `W` — the inequality that turns the truncation cost into `O(εt log W)`. -/
theorem logRatio_le {a : ℕ} (ha : 0 < a) (b : ℤ) {X W : ℕ} (hW : 2 ≤ W) (hWX : W ≤ X) :
    1 + Real.log ((a * X + b.natAbs : ℕ) : ℝ)
        - Real.log ((thinScale a b X W : ℕ) : ℝ)
      ≤ Real.log (W : ℝ) + logRatioConst a b := by
  classical
  set bb : ℕ := b.natAbs with hbb
  set L : ℕ := thinScale a b X W with hLdef
  set Y : ℕ := a * X + bb with hYdef
  have hL1 : 1 ≤ L := one_le_thinScale a b X W
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hWR : (0 : ℝ) < (W : ℝ) := by positivity
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast (by omega : 1 ≤ W)
  have hX2 : 2 ≤ X := le_trans hW hWX
  have hYpos : 1 ≤ Y := by
    have : 1 ≤ a * X := by
      have := Nat.mul_le_mul (show 1 ≤ a from ha) (show 1 ≤ X by omega); omega
    omega
  set K : ℕ := 5 * (a * (2 * bb + 2) + bb + 1) with hK
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by
    have : (1 : ℕ) ≤ K := by rw [hK]; omega
    exact_mod_cast this
  -- in both branches `Y ≤ K * W * L`
  have hmain : Y ≤ K * W * L := by
    rcases le_or_gt (2 * bb + 2) (X / W) with hq | hq
    · -- thin
      have hLeq : L = a * (X / W + 1) - bb := by
        rw [hLdef, thinScale]
        have hge : 2 * bb + 3 ≤ X / W + 1 := by omega
        have : bb + 1 ≤ a * (X / W + 1) := by
          calc bb + 1 ≤ X / W + 1 := by omega
            _ = 1 * (X / W + 1) := by ring
            _ ≤ a * (X / W + 1) := Nat.mul_le_mul_right _ ha
        omega
      have hdiv := ElliottCaseAThin.div_le_four_mul (a₁ := a) (W := W) (X := X) (b := bb)
        ha (by omega) hq
      rw [← hLeq] at hdiv
      have hLpos : 0 < L := hL1
      have hlt : Y < (4 * W + 1) * L := (Nat.div_lt_iff_lt_mul hLpos).mp (Nat.lt_succ_of_le hdiv)
      have hstep : (4 * W + 1) * L ≤ K * W * L := by
        refine Nat.mul_le_mul_right _ ?_
        have h5 : 5 ≤ K := by rw [hK]; omega
        calc 4 * W + 1 ≤ 5 * W := by omega
          _ ≤ K * W := Nat.mul_le_mul_right _ h5
      exact le_trans hlt.le hstep
    · -- thick
      have hXlt : X < W * (2 * bb + 2) := by
        have h1 : X < W * (X / W + 1) := ElliottCaseAThin.lt_mul_div_add_one (by omega)
        have h2 : X / W + 1 ≤ 2 * bb + 2 := by omega
        exact lt_of_lt_of_le h1 (Nat.mul_le_mul_left _ h2)
      have h1 : Y ≤ (a * (2 * bb + 2) + bb) * W := by
        have hax : a * X ≤ a * (W * (2 * bb + 2)) := Nat.mul_le_mul_left _ hXlt.le
        have hbw : bb ≤ bb * W := Nat.le_mul_of_pos_right _ (by omega)
        rw [hYdef]
        calc a * X + bb ≤ a * (W * (2 * bb + 2)) + bb * W := Nat.add_le_add hax hbw
          _ = (a * (2 * bb + 2) + bb) * W := by ring
      have h2 : (a * (2 * bb + 2) + bb) * W ≤ K * W * L := by
        have hKge : a * (2 * bb + 2) + bb ≤ K := by rw [hK]; omega
        calc (a * (2 * bb + 2) + bb) * W ≤ K * W := Nat.mul_le_mul_right _ hKge
          _ = K * W * 1 := by ring
          _ ≤ K * W * L := Nat.mul_le_mul_left _ hL1
      exact le_trans h1 h2
  -- take logs
  have hmainR : (Y : ℝ) ≤ (K : ℝ) * (W : ℝ) * (L : ℝ) := by
    have : ((Y : ℕ) : ℝ) ≤ ((K * W * L : ℕ) : ℝ) := by exact_mod_cast hmain
    push_cast at this ⊢
    linarith
  have hYR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hYpos
  have hlog := Real.log_le_log hYR hmainR
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    at hlog
  rw [logRatioConst, ← hbb, ← hK]
  linarith

end

end NormalNumbers.ElliottScaleWindow
