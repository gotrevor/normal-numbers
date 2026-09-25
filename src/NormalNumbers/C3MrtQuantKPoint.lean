/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtKPointNoExc

/-!
# The quantitative layer: a RATE, not just `Tendsto`

`C3MrtKPointNoExc` gives, for each fixed `K`, natural-density-zero `K`-point correlations from
one named input.  The headline `WeylLambertTwist` needs more: `QuantDepthElliottGen` asks for a
single `η N → 0` (beating every power of `llProxy`) with `‖depthAvg … D N‖ ≤ C D · η N` for ALL
depths `D` at once, because the depth actually used, `depthLL b N`, grows with `N`.

So the qualitative rung has to be replaced by a rate.  This file starts that: the top-down
Toeplitz step, which is where the rate is decided, in quantitative form.

Cutting the halving stack at level `k₀` gives

    (normalised class sum) ≤ Φ(Y/2^{k₀}) + G·2^{-k₀} + (log₂ Y + 1)/Y,

with `Φ a ≍ Cst(2 log a)^{-c}/M` the per-scale window bound.  Taking `k₀ ≍ log log Y` makes the
second term negligible and leaves `≍ Cst (log Y − log log Y)^{-c}/M`: a genuine power-of-log
saving, which is what the `C D = A_D e^{D²}` assembly of the budget layer can consume.
-/

open Filter Finset Topology

namespace NormalNumbers

namespace CastingOut

/-- **The top-down Toeplitz estimate, quantitative.**  Cutting the stack at level `k₀`: the
levels above `k₀` see the antitone bound at the lowest scale `Y/2^{k₀}` and carry total weight
`≤ 1`; the levels below contribute at most `G·2^{-k₀}`. -/
theorem top_down_weighted_le {Φ : ℕ → ℝ} (h0 : ∀ a, 0 ≤ Φ a) {G : ℝ} (hG : ∀ a, Φ a ≤ G)
    (hanti : ∀ {a b : ℕ}, a ≤ b → Φ b ≤ Φ a) (Y K k₀ : ℕ) :
    ∑ k ∈ range K, Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ)
      ≤ (Φ (Y / 2 ^ k₀) + G * (1 / 2) ^ k₀) * (Y : ℝ) := by
  have hG0 : (0 : ℝ) ≤ G := le_trans (h0 0) (hG 0)
  have hY0 : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg _
  -- every level is at most its weight times the scale
  have hscale : ∀ k : ℕ, ((Y / 2 ^ (k + 1) : ℕ) : ℝ) ≤ (1 / 2) ^ (k + 1) * (Y : ℝ) := by
    intro k
    have h := Nat.cast_div_le (α := ℝ) (m := Y) (n := 2 ^ (k + 1))
    have hpow : ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
    rw [hpow] at h
    calc ((Y / 2 ^ (k + 1) : ℕ) : ℝ) ≤ (Y : ℝ) / (2 : ℝ) ^ (k + 1) := h
      _ = (1 / 2) ^ (k + 1) * (Y : ℝ) := by rw [div_pow, one_pow]; ring
  have hdiv : ∀ k : ℕ, k + 1 ≤ k₀ → Φ (Y / 2 ^ k₀) ≥ Φ (Y / 2 ^ (k + 1)) := by
    intro k hk
    refine hanti (Nat.div_le_div_left ?_ (by positivity))
    exact Nat.pow_le_pow_right (by norm_num) hk
  have hterm : ∀ k : ℕ, k + 1 ≤ k₀ →
      Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ)
        ≤ Φ (Y / 2 ^ k₀) * ((1 / 2) ^ (k + 1) * (Y : ℝ)) := by
    intro k hk
    calc Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ)
        ≤ Φ (Y / 2 ^ (k + 1)) * ((1 / 2) ^ (k + 1) * (Y : ℝ)) :=
          mul_le_mul_of_nonneg_left (hscale k) (h0 _)
      _ ≤ Φ (Y / 2 ^ k₀) * ((1 / 2) ^ (k + 1) * (Y : ℝ)) :=
          mul_le_mul_of_nonneg_right (hdiv k hk) (by positivity)
  have htermG : ∀ k : ℕ, Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ)
      ≤ G * ((1 / 2) ^ (k + 1) * (Y : ℝ)) := by
    intro k
    calc Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ)
        ≤ Φ (Y / 2 ^ (k + 1)) * ((1 / 2) ^ (k + 1) * (Y : ℝ)) :=
          mul_le_mul_of_nonneg_left (hscale k) (h0 _)
      _ ≤ G * ((1 / 2) ^ (k + 1) * (Y : ℝ)) :=
          mul_le_mul_of_nonneg_right (hG _) (by positivity)
  have hgeo1 : ∑ k ∈ range K, ((1 : ℝ) / 2) ^ (k + 1) ≤ 1 := by
    rw [Finset.range_eq_Ico]
    simpa using geom_half_Ico_le 0 K
  rcases le_or_gt K k₀ with hKk | hKk
  · -- every level is above the cut
    have hsum : ∑ k ∈ range K, Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ)
        ≤ ∑ k ∈ range K, Φ (Y / 2 ^ k₀) * ((1 / 2) ^ (k + 1) * (Y : ℝ)) :=
      Finset.sum_le_sum fun k hk => hterm k (by
        have := Finset.mem_range.1 hk
        omega)
    have hrw : ∑ k ∈ range K, Φ (Y / 2 ^ k₀) * ((1 / 2) ^ (k + 1) * (Y : ℝ))
        = Φ (Y / 2 ^ k₀) * (Y : ℝ) * ∑ k ∈ range K, ((1 : ℝ) / 2) ^ (k + 1) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [hrw] at hsum
    have hfin : Φ (Y / 2 ^ k₀) * (Y : ℝ) * ∑ k ∈ range K, ((1 : ℝ) / 2) ^ (k + 1)
        ≤ Φ (Y / 2 ^ k₀) * (Y : ℝ) := by
      nlinarith [hgeo1, mul_nonneg (h0 (Y / 2 ^ k₀)) hY0]
    have hgy : (0 : ℝ) ≤ G * (1 / 2) ^ k₀ * (Y : ℝ) := by positivity
    nlinarith [hsum, hfin, hgy]
  · -- split the stack at `k₀`
    have hsplit : ∑ k ∈ range K, Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ)
        = (∑ k ∈ Finset.Ico 0 k₀, Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ))
          + ∑ k ∈ Finset.Ico k₀ K, Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ) := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le k₀) hKk.le]
    rw [hsplit]
    have hA : ∑ k ∈ Finset.Ico 0 k₀, Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ)
        ≤ Φ (Y / 2 ^ k₀) * (Y : ℝ) := by
      have h1 : ∑ k ∈ Finset.Ico 0 k₀, Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ)
          ≤ ∑ k ∈ Finset.Ico 0 k₀, Φ (Y / 2 ^ k₀) * ((1 / 2) ^ (k + 1) * (Y : ℝ)) :=
        Finset.sum_le_sum fun k hk => hterm k (by
          have := (Finset.mem_Ico.1 hk).2
          omega)
      have hrw : ∑ k ∈ Finset.Ico 0 k₀, Φ (Y / 2 ^ k₀) * ((1 / 2) ^ (k + 1) * (Y : ℝ))
          = Φ (Y / 2 ^ k₀) * (Y : ℝ) * ∑ k ∈ Finset.Ico 0 k₀, ((1 : ℝ) / 2) ^ (k + 1) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      have hgeo : ∑ k ∈ Finset.Ico 0 k₀, ((1 : ℝ) / 2) ^ (k + 1) ≤ 1 := by
        simpa using geom_half_Ico_le 0 k₀
      rw [hrw] at h1
      nlinarith [h1, hgeo, mul_nonneg (h0 (Y / 2 ^ k₀)) hY0]
    have hB : ∑ k ∈ Finset.Ico k₀ K, Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ)
        ≤ G * (1 / 2) ^ k₀ * (Y : ℝ) := by
      have h1 : ∑ k ∈ Finset.Ico k₀ K, Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ)
          ≤ ∑ k ∈ Finset.Ico k₀ K, G * ((1 / 2) ^ (k + 1) * (Y : ℝ)) :=
        Finset.sum_le_sum fun k _ => htermG k
      have hrw : ∑ k ∈ Finset.Ico k₀ K, G * ((1 / 2) ^ (k + 1) * (Y : ℝ))
          = G * (Y : ℝ) * ∑ k ∈ Finset.Ico k₀ K, ((1 : ℝ) / 2) ^ (k + 1) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      rw [hrw] at h1
      have hgeo := geom_half_Ico_le k₀ K
      nlinarith [h1, hgeo, mul_nonneg hG0 hY0]
    nlinarith [hA, hB]

#print axioms NormalNumbers.CastingOut.top_down_weighted_le

open scoped Classical in
/-- **The class sum, quantitatively.**  The halving stack cut at level `k₀`, with the per-scale
window bound `Φ` antitone and `≤ 1`.  This is `class_sum_tendsto_of_window` with the limit
replaced by the inequality it was extracted from — which is what a RATE needs. -/
theorem class_sum_le_of_window {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {Φ : ℕ → ℝ}
    (h0 : ∀ a, 0 ≤ Φ a) (h1 : ∀ a, Φ a ≤ 1) (hanti : ∀ {a b : ℕ}, a ≤ b → Φ b ≤ Φ a)
    {M : ℕ} (r : ℕ)
    (hB : ∀ a : ℕ, ‖∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M), f n‖
        ≤ Φ a * (a : ℝ))
    (Y k₀ : ℕ) :
    ‖∑ n ∈ (Finset.Ioc 0 Y).filter (fun n => n % M = r % M), f n‖
      ≤ (Φ (Y / 2 ^ k₀) + (1 / 2) ^ k₀) * (Y : ℝ) + ((Nat.log 2 Y + 1 : ℕ) : ℝ) := by
  classical
  set F : ℕ → ℂ := fun n => if n % M = r % M then f n else 0 with hFdef
  have hFnorm : ∀ n, ‖F n‖ ≤ 1 := by
    intro n
    simp only [hFdef]
    by_cases hn : n % M = r % M
    · simp only [if_pos hn]; exact hf n
    · simp [hn]
  have hfilter : ∀ a b : ℕ,
      ∑ n ∈ (Finset.Ioc a b).filter (fun n => n % M = r % M), f n = ∑ n ∈ Finset.Ioc a b, F n := by
    intro a b; simp only [hFdef]; rw [Finset.sum_filter]
  have hhead : Y / 2 ^ (Nat.log 2 Y + 1) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_pow_succ_log_self (by norm_num) Y)
  have hstack : ‖∑ n ∈ Finset.Ioc 0 Y, F n‖
      ≤ (∑ k ∈ range (Nat.log 2 Y + 1), Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ))
        + ((Nat.log 2 Y + 1 : ℕ) : ℝ) := by
    rw [sum_Ioc_halving_stack F Y (Nat.log 2 Y + 1), hhead]
    simp only [Finset.Ioc_self, Finset.sum_empty, zero_add]
    refine le_trans (norm_sum_le _ _) ?_
    have hlev : ∀ k ∈ range (Nat.log 2 Y + 1),
        ‖∑ n ∈ Finset.Ioc (Y / 2 ^ (k + 1)) (Y / 2 ^ k), F n‖
          ≤ Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ) + 1 := fun k _ =>
      norm_sum_level_le hFnorm (double_le_level Y k) (level_le_double_succ Y k)
        (by rw [← hfilter]; exact hB _)
    refine le_trans (Finset.sum_le_sum hlev) ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have htop := top_down_weighted_le h0 h1 hanti Y (Nat.log 2 Y + 1) k₀
  rw [hfilter]
  have : (1 : ℝ) * (1 / 2) ^ k₀ = (1 / 2) ^ k₀ := one_mul _
  linarith [hstack, htop]

#print axioms NormalNumbers.CastingOut.class_sum_le_of_window


end CastingOut

end NormalNumbers
