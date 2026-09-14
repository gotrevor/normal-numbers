/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4MinWeight

/-!
# G4 §4C: frequency separation — `∑_α dist(w_α 4^{-j_α}, ℤ)² ≥ 4^{-4} 8^{-K}`

Brief §4C: for each nonzero coefficient `w_α` of `Aᵀ q` choose

  `j_α = K + ⌈log₄ |w_α|⌉ + 1 < J`,   then   `∑_{α, K < j ≤ J} dist(w_α 4^{-j}, ℤ)² ≥ 4^{-4} 8^{-K}`.

This is the arithmetic seed of the whole small-prime contraction: it is what makes the
independent-model bound `exp(-c L 8^{-K})` an `8^{-K}` and not something smaller.  It is proved
here unconditionally, from the §4A support bound of `G4MinWeight`.

The mechanism, made explicit:

* `freqDepth K w = K + 1 + ⌈log₄ |w|⌉` puts `|w| 4^{-j}` into the window `[4^{-(K+2)}, 4^{-(K+1)}]`
  (`mem_window_freqDepth`), which lies in `(0, 1/4]`, so the *nearest integer* is `0` (or, if
  rounding disagrees, the distance is at least `1/2`) and `distZ ≥ 4^{-(K+2)}`
  (`le_distZ_freqDepth`).  One coefficient therefore contributes `≥ 4^{-4} 16^{-K}` to the
  square sum.
* The matrix `A = D_s^{⊗K}` has minimum weight `2^K` (`minWeight_kronPow_diffZ`), so at least
  `2^K` coefficients contribute, and `2^K · 4^{-4} 16^{-K} = 4^{-4} 8^{-K}`
  (`sum_sq_distZ_freqDepth_ge`).

Note the two powers do **not** come from the same place: `16^{-K}` is the square of the window
scale, `2^K` is the code distance.  Weakening either input (e.g. bounding the support below by
`2` instead of `2^K`) destroys the `8^{-K}` that §5 needs against `rK`.

`freqDepth_le` is the uniform admissibility statement `j_α < J`: over the whole Fourier box
`‖q‖∞ ≤ D` the depth never exceeds `K + 1 + ⌈log₄(2^K D)⌉`, because `‖Aᵀq‖∞ ≤ 2^K D`.
-/

open Finset Matrix
open scoped BigOperators

namespace NormalNumbers.G4

/-! ### Distance to the nearest integer -/

/-- Distance from a real number to the nearest integer. -/
noncomputable def distZ (x : ℝ) : ℝ := |x - round x|

lemma distZ_nonneg (x : ℝ) : 0 ≤ distZ x := abs_nonneg _

lemma distZ_eq_norm (x : ℝ) : distZ x = ‖(x : UnitAddCircle)‖ := UnitAddCircle.norm_eq.symm

/-- If `|x|` is at least `c` and at most `1/2`, then so is its distance to `ℤ`: either the
nearest integer is `0`, or it has absolute value `≥ 1` and the distance is `≥ 1/2`. -/
lemma le_distZ {x c : ℝ} (hc : c ≤ 1 / 2) (h1 : c ≤ |x|) (h2 : |x| ≤ 1 / 2) : c ≤ distZ x := by
  unfold distZ
  rcases eq_or_ne (round x) 0 with h | h
  · rw [h]; simpa using h1
  · have hn : (1 : ℝ) ≤ |(round x : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h
    have hab := abs_sub_abs_le_abs_sub ((round x : ℤ) : ℝ) x
    rw [abs_sub_comm] at hab
    linarith

/-! ### The chosen layer for a frequency coefficient -/

/-- `4 ^ ⌈log₄ n⌉ ≤ 4 n` for `n ≥ 1`. -/
lemma pow_clog_le (n : ℕ) (hn : 1 ≤ n) : 4 ^ Nat.clog 4 n ≤ 4 * n := by
  rcases eq_or_lt_of_le hn with h | h
  · simp [← h]
  · have hm : 1 ≤ Nat.clog 4 n := Nat.clog_pos (by norm_num) h
    have hlt := Nat.pow_pred_clog_lt_self (b := 4) (by norm_num) h
    calc 4 ^ Nat.clog 4 n = 4 ^ (Nat.clog 4 n - 1) * 4 := by
          rw [← pow_succ]; congr 1; omega
      _ ≤ n * 4 := Nat.mul_le_mul_right 4 (le_of_lt hlt)
      _ = 4 * n := by ring

/-- **Brief §4C**: the layer assigned to a nonzero frequency coefficient,
`j = K + ⌈log₄ |w|⌉ + 1`. -/
def freqDepth (K : ℕ) (w : ℤ) : ℕ := K + 1 + Nat.clog 4 w.natAbs

/-- The assigned layer is always a **retained** layer: `j > K`.  This is what makes the
separation compatible with the §4A cancellation, which annihilates layers `1 … K`. -/
lemma lt_freqDepth (K : ℕ) (w : ℤ) : K < freqDepth K w := by
  unfold freqDepth; omega

/-- The window: `|w| 4^{-j}` lies between `4^{-(K+2)}` and `4^{-(K+1)}`. -/
lemma mem_window_freqDepth (K : ℕ) {w : ℤ} (hw : w ≠ 0) :
    1 / (4 : ℝ) ^ (K + 2) ≤ |(w : ℝ) / 4 ^ freqDepth K w| ∧
      |(w : ℝ) / 4 ^ freqDepth K w| ≤ 1 / (4 : ℝ) ^ (K + 1) := by
  have hn : 1 ≤ w.natAbs := Int.natAbs_pos.2 hw
  set m := Nat.clog 4 w.natAbs with hm
  have hup : (w.natAbs : ℝ) ≤ 4 ^ m := by exact_mod_cast Nat.le_pow_clog (by norm_num) w.natAbs
  have hlo : (4 : ℝ) ^ m ≤ 4 * w.natAbs := by exact_mod_cast pow_clog_le w.natAbs hn
  have habs : |(w : ℝ)| = (w.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    norm_num
  have hpow : (0 : ℝ) < 4 ^ freqDepth K w := by positivity
  have hsplit : (4 : ℝ) ^ freqDepth K w = 4 ^ (K + 1) * 4 ^ m := by
    rw [freqDepth, ← pow_add]
  rw [abs_div, habs, abs_of_pos hpow, hsplit]
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc (1 : ℝ) * (4 ^ (K + 1) * 4 ^ m) = 4 ^ m * 4 ^ (K + 1) := by ring
      _ ≤ (4 * w.natAbs) * 4 ^ (K + 1) := by
          exact mul_le_mul_of_nonneg_right hlo (by positivity)
      _ = (w.natAbs : ℝ) * 4 ^ (K + 2) := by rw [pow_succ]; ring
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc (w.natAbs : ℝ) * 4 ^ (K + 1) ≤ 4 ^ m * 4 ^ (K + 1) := by
          exact mul_le_mul_of_nonneg_right hup (by positivity)
      _ = 1 * (4 ^ (K + 1) * 4 ^ m) := by ring

/-- **The single-coefficient separation.**  For `w ≠ 0` the assigned layer keeps
`w 4^{-j}` at distance `≥ 4^{-(K+2)}` from `ℤ`. -/
theorem le_distZ_freqDepth (K : ℕ) {w : ℤ} (hw : w ≠ 0) :
    1 / (4 : ℝ) ^ (K + 2) ≤ distZ ((w : ℝ) / 4 ^ freqDepth K w) := by
  obtain ⟨h1, h2⟩ := mem_window_freqDepth K hw
  refine le_distZ ?_ h1 (h2.trans ?_)
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (4 : ℝ) ^ 2 ≤ 4 ^ (K + 2) := by
      apply pow_le_pow_right₀ (by norm_num); omega
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (4 : ℝ) ^ 1 ≤ 4 ^ (K + 1) := by
      apply pow_le_pow_right₀ (by norm_num); omega
    nlinarith


/-! ### The integer difference matrix and the full separation bound -/

/-- The integer adjacent-difference matrix, the `ℤ`-form of `diff`. -/
def diffZ (s : ℕ) : Matrix (Fin s) (Fin (s + 1)) ℤ :=
  fun a => Pi.single a.castSucc (1 : ℤ) - Pi.single a.succ 1

lemma diffZ_cast (s : ℕ) (a : Fin s) (c : Fin (s + 1)) :
    ((diffZ s a c : ℤ) : ℝ) = diff s a c := by
  simp only [diffZ, diff, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> norm_num

lemma cast_vecMul_kronPow_diffZ (K s : ℕ) (q : (Fin K → Fin s) → ℤ) (c : Fin K → Fin (s + 1)) :
    (((kronPow K (diffZ s)).vecMul q c : ℤ) : ℝ)
      = (kronPow K (diff s)).vecMul (fun a => (q a : ℝ)) c := by
  simp only [Matrix.vecMul, dotProduct, kronPow]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun i _ => diffZ_cast s (a i) (c i)

/-- **Brief §4A over `ℤ`**: `q ᵥ* D_s^{⊗K}` has at least `2^K` nonzero entries. -/
theorem minWeight_kronPow_diffZ (K s : ℕ) : MinWeight (kronPow K (diffZ s)) (2 ^ K) := by
  intro q hq
  have hqR : (fun a => (q a : ℝ)) ≠ 0 := by
    intro h
    refine hq (funext fun a => ?_)
    have h2 := congrFun h a
    simp only [Pi.zero_apply] at h2 ⊢
    exact_mod_cast h2
  have hR := minWeight_kronPow (minWeight_diff s) K (fun a => (q a : ℝ)) hqR
  refine hR.trans (le_of_eq ?_)
  unfold wt
  congr 1
  ext c
  simp only [Finset.mem_filter, mem_univ, true_and, ne_eq,
    ← cast_vecMul_kronPow_diffZ K s q c, Int.cast_eq_zero]

/-- **Brief §4A over `ℤ`**: `‖q ᵥ* D_s^{⊗K}‖∞ ≤ 2^K ‖q‖∞`. -/
lemma natAbs_vecMul_kronPow_diffZ_le (K s D : ℕ) {q : (Fin K → Fin s) → ℤ}
    (hq : ∀ a, |q a| ≤ (D : ℤ)) (c : Fin K → Fin (s + 1)) :
    ((kronPow K (diffZ s)).vecMul q c).natAbs ≤ 2 ^ K * D := by
  have hqR : ∀ a, |((q a : ℝ))| ≤ (D : ℝ) := by
    intro a
    rw [← Int.cast_abs]
    exact_mod_cast hq a
  have h := abs_vecMul_kronPow_le (diff s) K (colSum_diff_le s) (by positivity) _ hqR c
  rw [← cast_vecMul_kronPow_diffZ] at h
  have hZ : |(kronPow K (diffZ s)).vecMul q c| ≤ (2 : ℤ) ^ K * D := by
    rw [← Int.cast_abs] at h
    exact_mod_cast h
  zify
  exact hZ

/-- **Uniform admissibility of the layer choice on the whole Fourier box** (brief §4C, the
`j_α < J` condition): the assigned depth never exceeds `K + 1 + ⌈log₄(2^K D)⌉`. -/
theorem freqDepth_le (K s D : ℕ) {q : (Fin K → Fin s) → ℤ} (hq : ∀ a, |q a| ≤ (D : ℤ))
    (c : Fin K → Fin (s + 1)) :
    freqDepth K ((kronPow K (diffZ s)).vecMul q c) ≤ K + 1 + Nat.clog 4 (2 ^ K * D) := by
  unfold freqDepth
  exact Nat.add_le_add_left
    (Nat.clog_mono_right _ (natAbs_vecMul_kronPow_diffZ_le K s D hq c)) _

/-- **The frequency-separation bound of brief §4C.**  For every nonzero integer frequency `q`,
the layer choice `j_α = K + 1 + ⌈log₄|w_α|⌉` applied to `w = q ᵥ* D_s^{⊗K}` gives

  `∑_α dist(w_α 4^{-j_α}, ℤ)² ≥ 4^{-4} · 8^{-K}`.

The `16^{-K}` is the square of the window scale `4^{-(K+2)}`; the `2^K` is the minimum weight of
the tensor code.  Their product is the `8^{-K}` that §5 needs to dominate `rK`. -/
theorem sum_sq_distZ_freqDepth_ge (K s : ℕ) {q : (Fin K → Fin s) → ℤ} (hq : q ≠ 0) :
    1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K
      ≤ ∑ c : Fin K → Fin (s + 1),
          distZ (((kronPow K (diffZ s)).vecMul q c : ℤ) /
            (4 : ℝ) ^ freqDepth K ((kronPow K (diffZ s)).vecMul q c)) ^ 2 := by
  classical
  set w := (kronPow K (diffZ s)).vecMul q with hwdef
  set F : Finset (Fin K → Fin (s + 1)) := univ.filter (fun c => w c ≠ 0) with hF
  have hcard : 2 ^ K ≤ F.card := minWeight_kronPow_diffZ K s q hq
  have hterm : ∀ c ∈ F,
      (1 / (4 : ℝ) ^ (K + 2)) ^ 2 ≤ distZ ((w c : ℝ) / (4 : ℝ) ^ freqDepth K (w c)) ^ 2 := by
    intro c hc
    have hne : w c ≠ 0 := by rw [hF] at hc; exact (Finset.mem_filter.1 hc).2
    have h1 := le_distZ_freqDepth K hne
    have h0 : (0 : ℝ) ≤ 1 / (4 : ℝ) ^ (K + 2) := by positivity
    gcongr
  have harith : (1 : ℝ) / 4 ^ 4 * (1 / 8 : ℝ) ^ K = (2 : ℝ) ^ K * (1 / (4 : ℝ) ^ (K + 2)) ^ 2 := by
    have h1 : ((4 : ℝ) ^ (K + 2)) ^ 2 = 16 ^ K * 256 := by
      rw [← pow_mul, show (K + 2) * 2 = 2 * K + 4 by ring, pow_add, pow_mul]
      norm_num
    have h2 : (16 : ℝ) ^ K = 8 ^ K * 2 ^ K := by rw [← mul_pow]; norm_num
    simp only [div_pow, one_pow]
    rw [h1, h2]
    have h8 : (8 : ℝ) ^ K ≠ 0 := by positivity
    have h2' : (2 : ℝ) ^ K ≠ 0 := by positivity
    field_simp
    ring
  calc (1 : ℝ) / 4 ^ 4 * (1 / 8 : ℝ) ^ K = (2 : ℝ) ^ K * (1 / (4 : ℝ) ^ (K + 2)) ^ 2 := harith
    _ ≤ (F.card : ℝ) * (1 / (4 : ℝ) ^ (K + 2)) ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast hcard
    _ = ∑ _c ∈ F, (1 / (4 : ℝ) ^ (K + 2)) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ c ∈ F, distZ ((w c : ℝ) / (4 : ℝ) ^ freqDepth K (w c)) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ ∑ c : Fin K → Fin (s + 1),
          distZ ((w c : ℝ) / (4 : ℝ) ^ freqDepth K (w c)) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F) ?_
        intro c _ _
        exact sq_nonneg _

end NormalNumbers.G4
