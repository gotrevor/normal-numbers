/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtMean

/-!
# The explicit `log log log` schedule, and the quantitative form of the crux

`C3MrtMean.weylLambertTwist_of_schedule` closes the C3 crux from any depth schedule whose mean
discarded phase `LL(N)/b^{D_N}` vanishes.  The repo already carries such a schedule, built for
the Pair-B decoupling: `PairDecouple.depthLL b N = ⌊log_b (u_N+1)²⌋ + 1` with
`u_N = log₂ log₂ N`, which is `O(log log log N)` and satisfies `b^{depthLL} > (u_N+1)²`.

Instantiating gives the final shape of the obligation:

* `weylLambertTwist_of_depthElliottLL` — the crux follows from the twisted `depthLL b N`-point
  correlations vanishing.  **`O(log log log N)` correlation points.**
* `QuantDepthElliott` / `weylLambertTwist_of_quantDepthElliott` — the *quantitative* form, which
  is the realistic target: a `D`-point bound `b^{κD} · η(N)` where the single `N`-decay `η`
  beats every power of `log log log N`.  The `D = 1` rung already has `η(N) = (log N)^{-a}`
  (Selberg–Delange, `C3MrtRungOne`), which beats every power of anything log-log-sized.  So the
  budget is extremely generous: the constant may grow like ANY fixed power of `b^D`.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- `u_N + 1` with `u_N = log₂ log₂ N`: the size scale of the schedule. -/
noncomputable def llProxy (N : ℕ) : ℝ := (Nat.log 2 (Nat.log 2 N) : ℝ) + 1

lemma one_le_llProxy (N : ℕ) : 1 ≤ llProxy N := by
  have : (0 : ℝ) ≤ (Nat.log 2 (Nat.log 2 N) : ℝ) := Nat.cast_nonneg _
  rw [llProxy]; linarith

lemma tendsto_llProxy : Tendsto llProxy atTop atTop := by
  have h2 : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N)) atTop atTop :=
    (PairDecouple.tendsto_natLog_atTop 2 le_rfl).comp
      (PairDecouple.tendsto_natLog_atTop 2 le_rfl)
  have h3 : Tendsto (fun N : ℕ => ((Nat.log 2 (Nat.log 2 N) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp h2
  exact tendsto_atTop_add_const_right atTop (1 : ℝ) h3

/-- `LL(N) = 4 log(log₂ N) + 11 ≤ 15 (u_N + 1)`. -/
lemma LLbound_le_llProxy (N : ℕ) : LLbound N ≤ 15 * llProxy N := by
  have h1 := PairDecouple.log_le_natLog_succ (Nat.log 2 N)
  have h2 : Real.log 2 < 0.7 := by
    have := Real.log_two_lt_d9
    linarith
  have h3 : (0 : ℝ) ≤ (Nat.log 2 (Nat.log 2 N) : ℝ) + 1 := by positivity
  rw [LLbound, llProxy]
  nlinarith [h1, h2, h3]

/-- **The mean discarded phase vanishes along `depthLL`.** -/
theorem tendsto_LLbound_div_pow_depthLL {b : ℕ} (hb : 2 ≤ b) :
    Tendsto (fun N : ℕ => LLbound N / (b : ℝ) ^ PairDecouple.depthLL b N) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun N : ℕ => 15 / llProxy N) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_llProxy
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [] with N
    have hb0 : (0 : ℝ) < b := by
      have : (2 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
    have : 0 ≤ LLbound N := by
      rw [LLbound]
      have : (0 : ℝ) ≤ Real.log (Nat.log 2 N) := Real.log_natCast_nonneg _
      linarith
    positivity
  filter_upwards [] with N
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hden : (0 : ℝ) < (b : ℝ) ^ PairDecouple.depthLL b N := by positivity
  have hsq : llProxy N ^ 2 ≤ (b : ℝ) ^ PairDecouple.depthLL b N := by
    have := PairDecouple.pow_depthLL_gt b N hb
    rw [llProxy]
    push_cast at this ⊢
    linarith
  have hp1 : (1 : ℝ) ≤ llProxy N := one_le_llProxy N
  have hLLnn : 0 ≤ LLbound N := by
    rw [LLbound]
    have : (0 : ℝ) ≤ Real.log (Nat.log 2 N) := Real.log_natCast_nonneg _
    linarith
  have hkey : LLbound N / (b : ℝ) ^ PairDecouple.depthLL b N ≤ 15 / llProxy N := by
    calc LLbound N / (b : ℝ) ^ PairDecouple.depthLL b N
        ≤ (15 * llProxy N) / (b : ℝ) ^ PairDecouple.depthLL b N :=
          (div_le_div_iff_of_pos_right hden).2 (LLbound_le_llProxy N)
      _ ≤ (15 * llProxy N) / (llProxy N ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      _ = 15 / llProxy N := by rw [sq]; field_simp
  exact hkey

/-- **The crux from the `log log log`-depth correlations.** -/
theorem weylLambertTwist_of_depthElliottLL {b : ℕ} (hb : 3 ≤ b)
    (H : ∀ (P Q j : ℕ) (h : ℤ), 0 < Q → 0 < j → j < Q →
      Tendsto (fun N : ℕ => depthAvg b P Q j h (PairDecouple.depthLL b N) N) atTop (𝓝 0)) :
    WeylLambertTwist b :=
  weylLambertTwist_of_schedule hb (PairDecouple.depthLL b)
    (PairDecouple.eventually_depthLL_add_le b 3 (by omega))
    (tendsto_LLbound_div_pow_depthLL (by omega)) H

/-! ### The quantitative target -/

/-- **The realistic form of the remaining obligation.**  A `D`-point twisted-correlation bound
`b^{κD} · η(N)`, with a single `N`-decay `η` beating every power of `log₂ log₂ N`.

The budget is generous: the constant may grow like any fixed power of `b^D`, because the
schedule only needs `D_N ≍ log_b log log N`, so `b^{κ D_N}` is merely polynomial in
`log log N`.  The `D = 1` rung (`depthAvg_one_tendsto`, Selberg–Delange) has
`η(N) = (log N)^{-a}`, which beats every power of `log log N` with room to spare. -/
def QuantDepthElliott (b : ℕ) : Prop :=
  ∀ (P Q j : ℕ) (h : ℤ), 0 < Q → 0 < j → j < Q →
    ∃ (κ : ℕ) (η : ℕ → ℝ), (∀ N, 0 ≤ η N) ∧
      (∀ D N : ℕ, ‖depthAvg b P Q j h D N‖ ≤ (b : ℝ) ^ (κ * D) * η N) ∧
      (∀ m : ℕ, Tendsto (fun N : ℕ => llProxy N ^ m * η N) atTop (𝓝 0))

/-- `b ^ depthLL b N ≤ b * (u_N + 1)²`. -/
lemma pow_depthLL_le {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    (b : ℝ) ^ PairDecouple.depthLL b N ≤ (b : ℝ) * llProxy N ^ 2 := by
  have hx : (Nat.log 2 (Nat.log 2 N) + 1) ^ 2 ≠ 0 := by positivity
  have h := Nat.pow_log_le_self b hx
  have hR : ((b ^ Nat.log b ((Nat.log 2 (Nat.log 2 N) + 1) ^ 2) : ℕ) : ℝ)
      ≤ (((Nat.log 2 (Nat.log 2 N) + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
  rw [PairDecouple.depthLL, pow_succ, llProxy]
  push_cast at hR ⊢
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  nlinarith [hR, hb0]

/-- **`QuantDepthElliott` closes the crux.** -/
theorem weylLambertTwist_of_quantDepthElliott {b : ℕ} (hb : 3 ≤ b)
    (H : QuantDepthElliott b) : WeylLambertTwist b := by
  refine weylLambertTwist_of_depthElliottLL hb fun P Q j h hQ hj0 hjQ => ?_
  obtain ⟨κ, η, hη0, hbd, hdec⟩ := H P Q j h hQ hj0 hjQ
  have hb0 : (0 : ℝ) < b := by
    have : (3 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hmaj : Tendsto (fun N : ℕ => (b : ℝ) ^ κ * (llProxy N ^ (2 * κ) * η N)) atTop (𝓝 0) := by
    simpa using (hdec (2 * κ)).const_mul ((b : ℝ) ^ κ)
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [] with N
  set D : ℕ := PairDecouple.depthLL b N with hD
  have hstep : (b : ℝ) ^ (κ * D) ≤ (b : ℝ) ^ κ * llProxy N ^ (2 * κ) := by
    have h1 : (b : ℝ) ^ (κ * D) = ((b : ℝ) ^ D) ^ κ := by rw [← pow_mul, mul_comm]
    have h2 : ((b : ℝ) ^ D) ^ κ ≤ ((b : ℝ) * llProxy N ^ 2) ^ κ := by
      refine pow_le_pow_left₀ (by positivity) ?_ κ
      rw [hD]; exact pow_depthLL_le (by omega) N
    calc (b : ℝ) ^ (κ * D) = ((b : ℝ) ^ D) ^ κ := h1
      _ ≤ ((b : ℝ) * llProxy N ^ 2) ^ κ := h2
      _ = (b : ℝ) ^ κ * llProxy N ^ (2 * κ) := by rw [mul_pow, ← pow_mul, mul_comm 2 κ]
  refine (hbd D N).trans ?_
  calc (b : ℝ) ^ (κ * D) * η N
      ≤ ((b : ℝ) ^ κ * llProxy N ^ (2 * κ)) * η N :=
        mul_le_mul_of_nonneg_right hstep (hη0 N)
    _ = (b : ℝ) ^ κ * (llProxy N ^ (2 * κ) * η N) := by ring

end CastingOut

end NormalNumbers
