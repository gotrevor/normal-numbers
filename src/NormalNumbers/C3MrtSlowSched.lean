/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtUnifK

/-!
# The SLOWED depth schedule, and `θ < 1` for the geometric `K`-point profile

`C3MrtUnifK.weylLambertTwist_of_geom` closes the C3 crux from a `K`-point correlation input whose
saving decays like `b^{-θK}`, but only for `θ < 1/2`.  That boundary is an artefact of the depth
schedule, not of the mathematics: `PairDecouple.depthLL b N` is built so that
`b^{depthLL} > (u_N+1)²` (**two** powers of `u_N = log₂log₂N`), whereas the only thing the
mean-phase discard of `weylLambertTwist_of_schedule` actually needs is
`LLbound N / b^{D_N} → 0`, and `LLbound N ≍ 15 u_N` is just **one** power.

So we slow the schedule down to the minimum that still works:

    slowArg b N = (u_N + 1) · (log_b (u_N+1) + 2),   depthSlow b N = log_b (slowArg b N) + 1

giving `b^{depthSlow} ∈ ((u+1)W, b(u+1)W]` with `W = log_b(u+1)+2`.  The discard is then
`≤ 15/W → 0` (one power of `u` cancels, the surviving `W` does the work), while the geometric
saving becomes

    b^{-θ·depthSlow} · log(2 log a_N)  ≳  ((u+1)W)^{-θ} · u log 2  ≍  u^{1-θ} (log u)^{-θ},

which beats `exp(depthSlow^m) = exp(O(log u)^m)`'s logarithm `(O(log u))^m` for **every** `θ < 1`.

Main results.
* `depthSlow`, `pow_depthSlow_gt`, `pow_depthSlow_le` — the schedule and its two-sided size.
* `tendsto_LLbound_div_pow_depthSlow` — the mean discard still vanishes.
* `depthSlow_le_depthLL` — the slow schedule is eventually *below* the old one, so every
  `KN N ≤ depthLL b N` side condition in `C3MrtUnifK` is inherited for free.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-! ### Two elementary `Nat.log` facts -/

theorem add_two_le_two_pow : ∀ k : ℕ, 2 ≤ k → k + 2 ≤ 2 ^ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> omega
    · have h := ih hn
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
      omega

/-- `log_b m + 2 ≤ m` for `m ≥ 3`, `b ≥ 2`. -/
theorem natLog_add_two_le {b m : ℕ} (hb : 2 ≤ b) (hm : 3 ≤ m) : Nat.log b m + 2 ≤ m := by
  have hle : Nat.log b m ≤ Nat.log 2 m := Nat.log_anti_left (by norm_num) hb
  set j : ℕ := Nat.log 2 m with hj
  have hpow : 2 ^ j ≤ m := Nat.pow_log_le_self 2 (by omega)
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · omega
  · have := add_two_le_two_pow j hj2
    omega

/-- `log_b m · log 2 ≤ log m`. -/
theorem natLog_mul_log_two_le {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    (Nat.log b m : ℝ) * Real.log 2 ≤ Real.log m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hpow : 2 ^ Nat.log b m ≤ m := by
    refine le_trans (Nat.pow_le_pow_left hb _) (Nat.pow_log_le_self b (by omega))
  have hR : ((2 : ℝ)) ^ Nat.log b m ≤ (m : ℝ) := by
    have : ((2 ^ Nat.log b m : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpow
    push_cast at this; exact this
  have h1 : Real.log ((2 : ℝ) ^ Nat.log b m) ≤ Real.log m :=
    Real.log_le_log (by positivity) hR
  rw [Real.log_pow] at h1
  linarith

/-! ### The slow schedule -/

/-- `W_N = log_b(u_N + 1) + 2`: the single extra logarithmic factor the slow schedule carries. -/
def slowW (b N : ℕ) : ℕ := Nat.log b (Nat.log 2 (Nat.log 2 N) + 1) + 2

/-- `slowArg b N = (u_N + 1) · W_N ≍ u log u`. -/
def slowArg (b N : ℕ) : ℕ := (Nat.log 2 (Nat.log 2 N) + 1) * slowW b N

/-- **The slowed depth schedule**, `D_N = log_b((u_N+1)·W_N) + 1`. -/
def depthSlow (b N : ℕ) : ℕ := Nat.log b (slowArg b N) + 1

theorem two_le_slowW (b N : ℕ) : 2 ≤ slowW b N := Nat.le_add_left _ _

theorem slowArg_pos (b N : ℕ) : 0 < slowArg b N :=
  Nat.mul_pos (Nat.succ_pos _) (lt_of_lt_of_le Nat.zero_lt_two (two_le_slowW b N))

theorem depthSlow_pos (b N : ℕ) : 0 < depthSlow b N := Nat.succ_pos _

/-- `b ^ depthSlow b N > slowArg b N`. -/
theorem pow_depthSlow_gt {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    ((slowArg b N : ℕ) : ℝ) < (b : ℝ) ^ depthSlow b N := by
  have h : slowArg b N < b ^ depthSlow b N :=
    Nat.lt_pow_succ_log_self (by omega) _
  have : ((slowArg b N : ℕ) : ℝ) < ((b ^ depthSlow b N : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this; exact this

/-- `b ^ depthSlow b N ≤ b · slowArg b N`. -/
theorem pow_depthSlow_le {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    (b : ℝ) ^ depthSlow b N ≤ (b : ℝ) * ((slowArg b N : ℕ) : ℝ) := by
  have h := Nat.pow_log_le_self b (slowArg_pos b N).ne'
  have hR : ((b ^ Nat.log b (slowArg b N) : ℕ) : ℝ) ≤ ((slowArg b N : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hR
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  rw [depthSlow, pow_succ]
  nlinarith [hR, hb0]

/-- **The slow schedule sits below the old one**, once `u_N ≥ 2`.  Every `KN N ≤ depthLL b N`
side condition in `C3MrtUnifK` is therefore inherited. -/
theorem depthSlow_le_depthLL {b : ℕ} (hb : 2 ≤ b) :
    ∀ᶠ N : ℕ in atTop, depthSlow b N ≤ PairDecouple.depthLL b N := by
  have hu : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N)) atTop atTop :=
    (PairDecouple.tendsto_natLog_atTop 2 le_rfl).comp
      (PairDecouple.tendsto_natLog_atTop 2 le_rfl)
  filter_upwards [hu.eventually_ge_atTop 2] with N hN
  set u : ℕ := Nat.log 2 (Nat.log 2 N) with hudef
  have hW : slowW b N ≤ u + 1 := by
    rw [slowW]
    exact natLog_add_two_le hb (by omega)
  have harg : slowArg b N ≤ (u + 1) ^ 2 := by
    rw [slowArg, sq]
    exact Nat.mul_le_mul_left _ hW
  have := Nat.log_mono_right (b := b) harg
  rw [depthSlow, PairDecouple.depthLL, ← hudef]
  omega

/-- `D_N + M ≤ N` eventually: the schedule is admissible for `weylLambertTwist_of_schedule`. -/
theorem eventually_depthSlow_add_le {b : ℕ} (hb : 2 ≤ b) (M : ℕ) :
    ∀ᶠ N : ℕ in atTop, depthSlow b N + M ≤ N := by
  filter_upwards [depthSlow_le_depthLL hb, PairDecouple.eventually_depthLL_add_le b M hb]
    with N h1 h2
  omega

theorem tendsto_slowW {b : ℕ} (hb : 2 ≤ b) :
    Tendsto (fun N : ℕ => slowW b N) atTop atTop := by
  have hu : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_succ _)
      ((PairDecouple.tendsto_natLog_atTop 2 le_rfl).comp
        (PairDecouple.tendsto_natLog_atTop 2 le_rfl))
  have h := (PairDecouple.tendsto_natLog_atTop b hb).comp hu
  exact tendsto_atTop_mono (fun N => Nat.le_add_right _ 2) h

/-- **The mean discarded phase still vanishes along the slow schedule.**  One power of `u_N`
cancels between `LLbound ≍ 15u` and `b^{D_N} ≥ (u+1)W`; the surviving `W → ∞` does the work. -/
theorem tendsto_LLbound_div_pow_depthSlow {b : ℕ} (hb : 2 ≤ b) :
    Tendsto (fun N : ℕ => LLbound N / (b : ℝ) ^ depthSlow b N) atTop (𝓝 0) := by
  have hWR : Tendsto (fun N : ℕ => ((slowW b N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_slowW hb)
  have hmaj : Tendsto (fun N : ℕ => 15 / ((slowW b N : ℕ) : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hWR
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
  have hden : (0 : ℝ) < (b : ℝ) ^ depthSlow b N := by positivity
  have hWpos : (0 : ℝ) < ((slowW b N : ℕ) : ℝ) := by
    have : (2 : ℕ) ≤ slowW b N := two_le_slowW b N
    have : (2 : ℝ) ≤ ((slowW b N : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hlow : llProxy N * ((slowW b N : ℕ) : ℝ) ≤ (b : ℝ) ^ depthSlow b N := by
    have h := pow_depthSlow_gt hb N
    have harg : ((slowArg b N : ℕ) : ℝ) = llProxy N * ((slowW b N : ℕ) : ℝ) := by
      rw [slowArg, llProxy]; push_cast; ring
    rw [harg] at h
    linarith
  have hp1 : (1 : ℝ) ≤ llProxy N := one_le_llProxy N
  have hLLnn : 0 ≤ LLbound N := by
    rw [LLbound]
    have : (0 : ℝ) ≤ Real.log (Nat.log 2 N) := Real.log_natCast_nonneg _
    linarith
  calc LLbound N / (b : ℝ) ^ depthSlow b N
      ≤ (15 * llProxy N) / (b : ℝ) ^ depthSlow b N :=
        (div_le_div_iff_of_pos_right hden).2 (LLbound_le_llProxy N)
    _ ≤ (15 * llProxy N) / (llProxy N * ((slowW b N : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlow
    _ = 15 / ((slowW b N : ℕ) : ℝ) := by
        rw [mul_comm (llProxy N) (((slowW b N : ℕ) : ℝ))]
        rw [div_mul_eq_div_div_swap]
        congr 1
        field_simp

/-- `W_N ≤ 2 + 2 log(u_N + 1)`: the extra factor is genuinely only logarithmic. -/
theorem slowW_le_log {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    ((slowW b N : ℕ) : ℝ) ≤ 2 + 2 * Real.log (llProxy N) := by
  set u : ℕ := Nat.log 2 (Nat.log 2 N) with hudef
  have hcast : ((u + 1 : ℕ) : ℝ) = llProxy N := by rw [llProxy]; push_cast; ring
  have h := natLog_mul_log_two_le hb (u + 1)
  rw [hcast] at h
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 0.7 := by
    have := Real.log_two_lt_d9; linarith
  have hlp : 0 ≤ Real.log (llProxy N) := Real.log_nonneg (one_le_llProxy N)
  have hnl : (0 : ℝ) ≤ (Nat.log b (u + 1) : ℝ) := Nat.cast_nonneg _
  have hkey : (Nat.log b (u + 1) : ℝ) ≤ 2 * Real.log (llProxy N) := by
    nlinarith [h, hlog2, hnl, hlp, Real.log_two_gt_d9]
  have : ((slowW b N : ℕ) : ℝ) = (Nat.log b (u + 1) : ℝ) + 2 := by
    rw [slowW, ← hudef]; push_cast; ring
  rw [this]; linarith

/-- `b^{depthSlow} ≤ b·(u+1)·(2 + 2 log(u+1))`: the schedule size, in analytic form. -/
theorem pow_depthSlow_le_log {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    (b : ℝ) ^ depthSlow b N ≤ (b : ℝ) * (llProxy N * (2 + 2 * Real.log (llProxy N))) := by
  have h1 := pow_depthSlow_le hb N
  have harg : ((slowArg b N : ℕ) : ℝ) = llProxy N * ((slowW b N : ℕ) : ℝ) := by
    rw [slowArg, llProxy]; push_cast; ring
  rw [harg] at h1
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have h2 := slowW_le_log hb N
  have hp1 : (1 : ℝ) ≤ llProxy N := one_le_llProxy N
  have h3 : llProxy N * ((slowW b N : ℕ) : ℝ) ≤ llProxy N * (2 + 2 * Real.log (llProxy N)) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have h4 := mul_le_mul_of_nonneg_left h3 hb0.le
  linarith

#print axioms NormalNumbers.CastingOut.add_two_le_two_pow
#print axioms NormalNumbers.CastingOut.natLog_add_two_le
#print axioms NormalNumbers.CastingOut.natLog_mul_log_two_le
#print axioms NormalNumbers.CastingOut.pow_depthSlow_gt
#print axioms NormalNumbers.CastingOut.pow_depthSlow_le
#print axioms NormalNumbers.CastingOut.depthSlow_le_depthLL
#print axioms NormalNumbers.CastingOut.eventually_depthSlow_add_le
#print axioms NormalNumbers.CastingOut.tendsto_LLbound_div_pow_depthSlow
#print axioms NormalNumbers.CastingOut.slowW_le_log
#print axioms NormalNumbers.CastingOut.pow_depthSlow_le_log

end CastingOut

end NormalNumbers
