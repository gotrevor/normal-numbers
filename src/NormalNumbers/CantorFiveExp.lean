/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorFiveExpGeneric

/-!
# Exact irrationality exponent for the base-5 exponent points

Base-5 port of the exponent half of `CantorExactExponent`: the point `ptF (expFree μ₀) ω` (the
base-3 run schedule, digits `{0,1,3,4}` on free places) has irrationality exponent exactly `μ₀`
whenever it avoids the scale tests `expTestF` from some scale on, and the tests have mass
`≤ 1/(m+1)²` eventually when `μ₀ > 2 + log₄ 5`.  The window lemmas of the base-3 file
(`window_core`, `fc_tri_ge`) are about the schedule only and are reused.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorFiveExp

open CantorLiouville Derandomize CantorFiveMoment CantorFiveNormal CantorExpGeneric
  CantorFiveExpGeneric CantorExactExponent

/-- The threshold `2 + log₄ 5`. -/
noncomputable def thresholdF : ℝ := 2 + Real.logb 4 5

theorem two_lt_of_thresholdF {μ : ℝ} (h : thresholdF < μ) : 2 < μ := by
  have : 0 < Real.logb 4 5 := Real.logb_pos (by norm_num) (by norm_num)
  unfold thresholdF at h; linarith

theorem rhoF_lt_one (μ₀ : ℝ) (hμ : thresholdF < μ₀) : 5 * (4 : ℝ) ^ (-(μ₀ - 2)) < 1 := by
  have h1 : (5 : ℝ) = 4 ^ Real.logb 4 5 :=
    (Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)).symm
  rw [h1, ← Real.rpow_add (by norm_num)]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  unfold thresholdF at hμ; linarith

variable {μ₀ : ℚ}

/-! ## Truncations and the lower bound -/

theorem ptDigitF_run_zero (hμ : 1 < μ₀) (ω : ℕ → Bool) (k : ℕ) :
    ∀ i, expRunStart μ₀ k ≤ i → i < expRunEnd μ₀ (expRunStart μ₀ k) →
      ptDigitF (expFree μ₀) ω i = 0 := fun i h1 h2 => by
  simp [ptDigitF, expFree_of_run hμ h1 h2]

theorem ptF_trunc (hμ : 1 < μ₀) (ω : ℕ → Bool) (k : ℕ) :
    ptF (expFree μ₀) ω = (hdF (expFree μ₀) ω (expRunStart μ₀ k) : ℝ) / 5 ^ expRunStart μ₀ k +
      tlF (expFree μ₀) ω (expRunEnd μ₀ (expRunStart μ₀ k)) := by
  set a := expRunStart μ₀ k
  set E := expRunEnd μ₀ a
  have hE := hdF_zero_ext (expFree μ₀) ω a E (le_expRunEnd hμ a) (ptDigitF_run_zero hμ ω k)
  rw [ptF_split (expFree μ₀) ω E, hE]
  push_cast
  rw [show (5 : ℝ) ^ E = 5 ^ (E - a) * 5 ^ a by
    rw [← pow_add]; congr 1; have := le_expRunEnd hμ a; omega]
  congr 1
  field_simp

theorem liouvilleWithF_of_ne (hμ : 1 < μ₀) (ω : ℕ → Bool)
    (h : ∀ N, ∃ k, N ≤ k ∧ ptF (expFree μ₀) ω ≠
      (hdF (expFree μ₀) ω (expRunStart μ₀ k) : ℝ) / 5 ^ expRunStart μ₀ k) :
    LiouvilleWith μ₀ (ptF (expFree μ₀) ω) := by
  refine ⟨2, frequently_atTop.2 fun N => ?_⟩
  obtain ⟨k, hk, hne⟩ := h N
  set a := expRunStart μ₀ k
  set E := expRunEnd μ₀ a
  refine ⟨5 ^ a, ?_, (hdF (expFree μ₀) ω a : ℤ), ?_, ?_⟩
  · have := lt_expRunStart hμ k
    have := Nat.lt_pow_self (n := a) (by norm_num : 1 < 5)
    omega
  · push_cast; exact hne
  · push_cast
    rw [ptF_trunc hμ ω k, add_sub_cancel_left, abs_of_nonneg (tlF_nonneg _ _ _)]
    have h1 := tlF_le (expFree μ₀) ω E
    have h2 : ((5 : ℝ) ^ a) ^ (μ₀ : ℝ) ≤ 5 ^ E := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by rw [mul_comm]; exact expRunEnd_ge_r μ₀ a)
    have h3 : 1 / (5 : ℝ) ^ E < 2 / ((5 : ℝ) ^ a) ^ (μ₀ : ℝ) := by
      have hp : (0 : ℝ) < ((5 : ℝ) ^ a) ^ (μ₀ : ℝ) := by positivity
      rw [div_lt_div_iff₀ (by positivity) hp]; linarith
    linarith

/-- **Lower bound**: nonzero free digits recur ⇒ `μ₀`-approximable. -/
theorem liouvilleWith_ptF (hμ : 1 < μ₀) (ω : ℕ → Bool)
    (hf : ∀ N, ∃ i, N ≤ i ∧ ptDigitF (expFree μ₀) ω i ≠ 0) :
    LiouvilleWith μ₀ (ptF (expFree μ₀) ω) := by
  refine liouvilleWithF_of_ne hμ ω fun N => ⟨N, le_rfl, fun heq => ?_⟩
  obtain ⟨i, hi, h2⟩ := hf (expRunEnd μ₀ (expRunStart μ₀ N))
  have := tlF_ge (expFree μ₀) ω _ i hi h2
  rw [ptF_trunc hμ ω N] at heq
  have : (0 : ℝ) < 1 / 5 ^ (i + 1) := by positivity
  linarith

/-! ## The tests -/

/-- The scale-`m` exponent test on a coin prefix of length `2 (expL μ₀ m + 1)`. -/
def expTestF (μ₀ : ℚ) (m : ℕ) (p : List Bool) : Bool :=
  hitBF (expFree μ₀) m (expL μ₀ m) p

theorem quarter_pow_le (n : ℕ) (t : ℝ) (h : t ≤ n) : (1 / 4 : ℝ) ^ n ≤ (4 : ℝ) ^ (-t) := by
  rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- **Deterministic mass bound of the scale-`m` test**, base 5. -/
theorem expTestF_mass_le (hμ : 2 < μ₀) : ∃ C : ℝ, ∀ m : ℕ, (μ₀ : ℝ) ≤ Nat.sqrt m →
    2 ≤ Nat.sqrt m →
    coins.real {ω | expTestF μ₀ m (pre ω (2 * (expL μ₀ m + 1))) = true} ≤
      36 * 4 ^ C * (5 * (4 : ℝ) ^ (-((μ₀ : ℝ) - 2))) ^ m +
        (4 : ℝ) ^ (-(((Nat.sqrt m : ℝ) - 2) / μ₀)) := by
  have hμ1 : (1 : ℚ) < μ₀ := by linarith
  obtain ⟨C, hC⟩ := window_core hμ
  refine ⟨C, fun m hsμ hs2 => ?_⟩
  set μ : ℝ := (μ₀ : ℝ)
  have hμR : (2 : ℝ) < μ := by simp only [μ]; exact_mod_cast hμ
  set s := Nat.sqrt m
  set L := expL μ₀ m
  have hsm : s * s ≤ m := Nat.sqrt_le m
  have hs2m : 2 * s ≤ m := le_trans (Nat.mul_le_mul_right s hs2) hsm |>.trans' (by simp)
  obtain ⟨hL1, -⟩ := expL_bounds (by linarith : (0 : ℚ) < μ₀) m
  replace hL1 : μ * m - 1 + s ≤ L := hL1
  have hsR : (s : ℝ) ≥ μ := hsμ
  have hmR : (2 * s : ℝ) ≤ m := by exact_mod_cast hs2m
  have hs3 : (3 : ℝ) ≤ s := by
    have : 2 < s := by
      have : (2 : ℝ) < s := lt_of_lt_of_le hμR hsR
      exact_mod_cast this
    exact_mod_cast this
  have hm7 : m + 7 ≤ L := by
    have : (m : ℝ) + 7 ≤ L := by nlinarith
    exact_mod_cast this
  have hex : ∃ k, L < expRunStart μ₀ (k + 1) + m + 3 :=
    ⟨L, by have := lt_expRunStart hμ1 (L + 1); omega⟩
  set k := Nat.find hex
  have hk2 : L < expRunStart μ₀ (k + 1) + m + 3 := Nat.find_spec hex
  have hk1 : expRunStart μ₀ k + m + 3 ≤ L := by
    rcases Nat.eq_zero_or_eq_succ_pred k with h0 | hj
    · rw [h0]; simp [expRunStart]; omega
    · have := Nat.find_min hex (show k - 1 < k by omega)
      rw [show k - 1 + 1 = k by omega] at this; omega
  have hmass0 : (0 : ℝ) ≤ 36 * 4 ^ C * (5 * (4 : ℝ) ^ (-(μ - 2))) ^ m := by positivity
  have hmass1 : (0 : ℝ) ≤ (4 : ℝ) ^ (-(((s : ℝ) - 2) / μ)) := by positivity
  unfold expTestF
  rcases le_or_gt (expRunEnd μ₀ (expRunStart μ₀ k)) (m + expRunStart μ₀ k + 3) with hbc | htri
  · -- Borel–Cantelli case
    have hw := hC μ le_rfl (by linarith) k (m + 1) (L - 1) (by push_cast; exact_mod_cast (by omega : expRunEnd μ₀ (expRunStart μ₀ k) ≤ m + 1 + expRunStart μ₀ k + 2))
      (by
        have : (L : ℝ) ≤ expRunStart μ₀ (k + 1) + m + 2 := by exact_mod_cast (by omega : L ≤ _)
        push_cast; nlinarith)
      (by rw [Nat.cast_sub (by omega)]; push_cast; nlinarith)
    have hb := hit_mass_bcF (expFree μ₀) m L (by omega)
    refine hb.trans (le_add_of_le_of_nonneg ?_ hmass1)
    have hp := quarter_pow_le (fc (expFree μ₀) (m + 1) (L - 1)) ((μ - 2) * m - C)
      (by push_cast at hw; nlinarith)
    have e : (5 * (4 : ℝ) ^ (-(μ - 2))) ^ m = 5 ^ m * 4 ^ (-((μ - 2) * m)) := by
      rw [mul_pow, ← Real.rpow_natCast ((4 : ℝ) ^ (-(μ - 2))), ← Real.rpow_mul (by norm_num)]
      ring_nf
    rw [e]
    have e2 : (4 : ℝ) ^ (-((μ - 2) * m - C)) = 4 ^ C * 4 ^ (-((μ - 2) * m)) := by
      rw [← Real.rpow_add (by norm_num)]; ring_nf
    rw [e2] at hp
    calc 36 * 5 ^ m * (1 / 4 : ℝ) ^ fc (expFree μ₀) (m + 1) (L - 1)
        ≤ 36 * 5 ^ m * (4 ^ C * 4 ^ (-((μ - 2) * m))) := by gcongr
      _ = _ := by ring
  · -- triangle case
    have ht := hit_mass_triF (expFree μ₀) m L (expRunStart μ₀ k) (expRunEnd μ₀ (expRunStart μ₀ k))
      (fun i h1 h2 => expFree_of_run hμ1 h1 h2) (by omega) (by omega)
    refine ht.trans (le_add_of_nonneg_of_le hmass0 ?_)
    exact quarter_pow_le _ _ (fc_tri_ge hμ1 k m L s hk1 (by omega) hL1 (by positivity) hmR)

/-- **Mass of the scale-`m` test, eventually `≤ 1/(m+1)²`.** -/
theorem ev_expTestF_mass (hμ : thresholdF < μ₀) :
    ∀ᶠ m : ℕ in atTop, coins.real {ω | expTestF μ₀ m (pre ω (2 * (expL μ₀ m + 1))) = true} ≤
      1 / ((m : ℝ) + 1) ^ 2 := by
  have h2 : (2 : ℚ) < μ₀ := by exact_mod_cast two_lt_of_thresholdF hμ
  obtain ⟨C, hC⟩ := expTestF_mass_le h2
  set μ : ℝ := (μ₀ : ℝ)
  have hμR : (2 : ℝ) < μ := by simp only [μ]; exact_mod_cast h2
  set ρ : ℝ := 5 * (4 : ℝ) ^ (-(μ - 2))
  have hρ1 : ρ < 1 := rhoF_lt_one μ hμ
  have hρ0 : 0 < ρ := by positivity
  set r : ℝ := (4 : ℝ) ^ (-(1 / μ))
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
    have : 0 < 1 / μ := by positivity
    linarith)
  have hB : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ 2 * ρ ^ m < 1 / (288 * 4 ^ C) :=
    (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 (by rw [abs_of_pos hρ0]; exact hρ1)).eventually
      (gt_mem_nhds (by positivity))
  have hD : ∀ᶠ s : ℕ in atTop, (s : ℝ) ^ 4 * r ^ s < 1 / (32 * 4 ^ (2 / μ)) :=
    (tendsto_pow_const_mul_const_pow_of_abs_lt_one 4 (by rw [abs_of_pos hr0]; exact hr1)).eventually
      (gt_mem_nhds (by positivity))
  have hD' := tendsto_nat_sqrt.eventually (hD.and (eventually_ge_atTop (⌈μ⌉₊ + 2)))
  filter_upwards [hB, hD', eventually_ge_atTop 1] with m hBm ⟨hDm, hsm⟩ hm1
  set s := Nat.sqrt m
  have hsμ : μ ≤ s := by
    have : (⌈μ⌉₊ : ℝ) + 2 ≤ s := by exact_mod_cast hsm
    linarith [Nat.le_ceil μ]
  refine (hC m hsμ (by omega)).trans ?_
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have t1 : 36 * 4 ^ C * ρ ^ m ≤ 1 / (2 * ((m : ℝ) + 1) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have : ((m : ℝ) + 1) ^ 2 ≤ 4 * m ^ 2 := by nlinarith
    have hC0 : (0 : ℝ) < 4 ^ C := by positivity
    have hρm : 0 ≤ ρ ^ m := by positivity
    have := (lt_div_iff₀ (by positivity)).1 hBm
    nlinarith
  have t2 : (4 : ℝ) ^ (-(((s : ℝ) - 2) / μ)) ≤ 1 / (2 * ((m : ℝ) + 1) ^ 2) := by
    have e : (4 : ℝ) ^ (-(((s : ℝ) - 2) / μ)) = 4 ^ (2 / μ) * r ^ s := by
      rw [← Real.rpow_natCast r, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1; field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have hms : (m : ℝ) + 1 ≤ ((s : ℝ) + 1) ^ 2 := by
      have h := Nat.lt_succ_sqrt m
      have : m + 1 ≤ (s + 1) * (s + 1) := h
      have : (m : ℝ) + 1 ≤ (s + 1) * (s + 1) := by exact_mod_cast this
      nlinarith
    have h4 : ((m : ℝ) + 1) ^ 2 ≤ 16 * (s : ℝ) ^ 4 := by
      have hs1 : (1 : ℝ) ≤ s := by linarith
      have : ((s : ℝ) + 1) ^ 2 ≤ 4 * s ^ 2 := by nlinarith
      have h0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
      calc ((m : ℝ) + 1) ^ 2 ≤ (((s : ℝ) + 1) ^ 2) ^ 2 := pow_le_pow_left₀ h0 hms 2
        _ ≤ (4 * s ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
        _ = 16 * (s : ℝ) ^ 4 := by ring
    have hC0 : (0 : ℝ) < 4 ^ (2 / μ) := by positivity
    have hrs : 0 ≤ r ^ s := by positivity
    have := (lt_div_iff₀ (by positivity)).1 hDm
    nlinarith
  have : 1 / (2 * ((m : ℝ) + 1) ^ 2) + 1 / (2 * ((m : ℝ) + 1) ^ 2) = 1 / ((m : ℝ) + 1) ^ 2 := by
    field_simp; ring
  linarith

end NormalNumbers.CantorFiveExp
