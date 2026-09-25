/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtSchedule
import NormalNumbers.C3MrtMultiLinear

/-!
# The constant budget: what the `D`-point correlation bound is allowed to carry

`C3MrtSchedule.QuantDepthElliott` states the remaining obligation with a constant budget
`b^{κD}`.  Lap 37 (`prod_le_lcm_mul_pow`) showed the `K`-fold rung's exchange
`1/lcm(d_i) → 1/∏ d_i` costs a factor `K^{K²}`, and **`b^{κD}` cannot pay for it**: along the
ratified schedule `D_N = depthLL b N ≍ log_b log log N` one has

    D_N^{D_N²} = exp(Θ((log log log N)² · log log log log N)) ,

while `b^{κ D_N} ≤ b^κ · (log log N)^{2κ} = exp(O(log log log N))`.  So the `K`-fold assembly
does **not** land inside `QuantDepthElliott` as stated.  (The lap-39 handoff's claim that
`K^{K²}` is `(log log N)^{o(1)}` is arithmetically wrong: `(log log N)^m = exp(m log log log N)`,
and `v² log v ≫ m v`.)

This file widens the budget to a free `C : ℕ → ℝ`, with the decay clause replaced by the JOINT
vanishing `C(D_N)·η(N) → 0` along the schedule, and proves:

* `weylLambertTwist_of_quantDepthElliottGen` — the widened `Prop` still closes the crux;
* `quantDepthElliottGen_of_quantDepthElliott` — the old `Prop` implies the new one, so nothing
  in the existing ledger is weakened or lost;
* `budget_absorb` — **the route-decisive lemma**.  Any budget `C D ≤ exp(c(D+1)³)` is absorbed
  by a decay `η N ≤ A(log N)^{-a}` with `a > 0`.  The mechanism is the triple-log schedule:
  `D_N + 1 ≤ 2t + 3` with `t = ⌊log₂(⌊log₂⌊log₂ N⌋⌋+1)⌋`, whereas `log log N ≥ (2^t − 2)log 2`;
  so the budget is polynomial in `t` and the decay is exponential in `t`.
* `pow_self_sq_le_exp_cube` — `K^{K²} ≤ exp(K³)`, which puts lap 37's constant inside that cap.

The decay `(log N)^{-a}` is not wishful: it is exactly what the `D = 1` rung has
(`C3MrtRungOne`, Selberg–Delange), and exactly what
`probes/swingc3_weyl_lambert_twist.py` measures for the leaf itself (`a ≈ 1.3–3.7`).
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-! ### The widened obligation -/

/-- **The general-budget form of the remaining obligation.**  A `D`-point twisted-correlation
bound `C D · η N` whose constant `C` is *free*, subject only to the joint vanishing
`C(depthLL b N)·η(N) → 0` along the ratified schedule.

This is the honest shape: it is exactly what the crux consumes, and it is what the `K`-fold
assembly of laps 36–39 produces (whose constant carries lap 37's `K^{K²}`, which the `b^{κD}`
budget of `QuantDepthElliott` cannot pay for). -/
def QuantDepthElliottGen (b : ℕ) : Prop :=
  ∀ (P Q j : ℕ) (h : ℤ), 0 < Q → 0 < j → j < Q →
    ∃ (C : ℕ → ℝ) (η : ℕ → ℝ), (∀ N, 0 ≤ η N) ∧
      (∀ D N : ℕ, ‖depthAvg b P Q j h D N‖ ≤ C D * η N) ∧
      Tendsto (fun N : ℕ => C (PairDecouple.depthLL b N) * η N) atTop (𝓝 0)

/-- **The widened `Prop` still closes the crux.** -/
theorem weylLambertTwist_of_quantDepthElliottGen {b : ℕ} (hb : 3 ≤ b)
    (H : QuantDepthElliottGen b) : WeylLambertTwist b := by
  refine weylLambertTwist_of_depthElliottLL hb fun P Q j h hQ hj0 hjQ => ?_
  obtain ⟨C, η, _, hbd, hlim⟩ := H P Q j h hQ hj0 hjQ
  exact squeeze_zero_norm (fun N => hbd _ N) hlim

/-- **Nothing is lost.**  The `b^{κD}` budget of `QuantDepthElliott` is a special case, so every
consumer of the old `Prop` survives verbatim. -/
theorem quantDepthElliottGen_of_quantDepthElliott {b : ℕ} (hb : 2 ≤ b)
    (H : QuantDepthElliott b) : QuantDepthElliottGen b := by
  intro P Q j h hQ hj0 hjQ
  obtain ⟨κ, η, hη0, hbd, hdec⟩ := H P Q j h hQ hj0 hjQ
  refine ⟨fun D => (b : ℝ) ^ (κ * D), η, hη0, hbd, ?_⟩
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hmaj : Tendsto (fun N : ℕ => (b : ℝ) ^ κ * (llProxy N ^ (2 * κ) * η N)) atTop (𝓝 0) := by
    simpa using (hdec (2 * κ)).const_mul ((b : ℝ) ^ κ)
  refine squeeze_zero (fun N => mul_nonneg (by positivity) (hη0 N)) (fun N => ?_) hmaj
  set D : ℕ := PairDecouple.depthLL b N with hD
  have hstep : (b : ℝ) ^ (κ * D) ≤ (b : ℝ) ^ κ * llProxy N ^ (2 * κ) := by
    have h1 : (b : ℝ) ^ (κ * D) = ((b : ℝ) ^ D) ^ κ := by rw [← pow_mul, mul_comm]
    have h2 : ((b : ℝ) ^ D) ^ κ ≤ ((b : ℝ) * llProxy N ^ 2) ^ κ := by
      refine pow_le_pow_left₀ (by positivity) ?_ κ
      rw [hD]; exact pow_depthLL_le hb N
    calc (b : ℝ) ^ (κ * D) = ((b : ℝ) ^ D) ^ κ := h1
      _ ≤ ((b : ℝ) * llProxy N ^ 2) ^ κ := h2
      _ = (b : ℝ) ^ κ * llProxy N ^ (2 * κ) := by rw [mul_pow, ← pow_mul, mul_comm 2 κ]
  calc (b : ℝ) ^ (κ * D) * η N
      ≤ ((b : ℝ) ^ κ * llProxy N ^ (2 * κ)) * η N :=
        mul_le_mul_of_nonneg_right hstep (hη0 N)
    _ = (b : ℝ) ^ κ * (llProxy N ^ (2 * κ) * η N) := by ring

/-! ### Lap 37's constant fits inside `exp(K³)` -/

/-- `K^{K²} ≤ exp(K³)`: the `1/lcm → 1/∏` exchange constant of `prod_le_lcm_mul_pow` is inside
the cap `budget_absorb` accepts. -/
theorem pow_self_sq_le_exp_cube (K : ℕ) : ((K : ℝ)) ^ (K * K) ≤ Real.exp ((K : ℝ) ^ 3) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hlog : Real.log K ≤ (K : ℝ) := by
    have := Real.log_le_sub_one_of_pos hK0
    linarith
  have hrw : ((K : ℝ)) ^ (K * K) = Real.exp (((K : ℝ) * K) * Real.log K) := by
    rw [show ((K : ℝ) * K) * Real.log K = ((K * K : ℕ) : ℝ) * Real.log K by push_cast; ring,
      ← Real.log_pow, Real.exp_log (by positivity)]
  rw [hrw]
  refine Real.exp_le_exp.2 ?_
  have h1 : ((K : ℝ) * K) * Real.log K ≤ ((K : ℝ) * K) * K :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  calc ((K : ℝ) * K) * Real.log K ≤ ((K : ℝ) * K) * K := h1
    _ = (K : ℝ) ^ 3 := by ring


/-! ### The schedule is polynomial in `t`, the decay exponential in `t` -/

/-- **The triple-log index** `t_N = ⌊log₂(⌊log₂⌊log₂ N⌋⌋+1)⌋ ≍ log log log N`.  It is the
natural variable for the budget question: the schedule's depth is LINEAR in `t`, while
`log log N` is EXPONENTIAL in `t`. -/
def tIdx (N : ℕ) : ℕ := Nat.log 2 (Nat.log 2 (Nat.log 2 N) + 1)

lemma tendsto_tIdx : Tendsto tIdx atTop atTop := by
  have hL1 : Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop :=
    PairDecouple.tendsto_natLog_atTop 2 le_rfl
  have h2 : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N)) atTop atTop := hL1.comp hL1
  exact hL1.comp (tendsto_atTop_mono (fun N => Nat.le_succ _) h2)

/-- **The schedule's depth, in triple-log terms.**  With
`t = ⌊log₂(⌊log₂⌊log₂ N⌋⌋ + 1)⌋` the ratified depth satisfies `D_N ≤ 2t + 2`.  The bound is
uniform in `b ≥ 2` because `Nat.log b ≤ Nat.log 2`. -/
theorem depthLL_le_triple_log {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    PairDecouple.depthLL b N ≤ 2 * Nat.log 2 (Nat.log 2 (Nat.log 2 N) + 1) + 2 := by
  set s : ℕ := Nat.log 2 (Nat.log 2 N) with hs
  set t : ℕ := Nat.log 2 (s + 1) with ht
  have h1 : Nat.log b ((s + 1) ^ 2) ≤ Nat.log 2 ((s + 1) ^ 2) :=
    Nat.log_anti_left (by norm_num) hb
  have h2 : (s + 1) < 2 ^ (t + 1) := Nat.lt_pow_succ_log_self (by norm_num) (s + 1)
  have h3 : (s + 1) ^ 2 < 2 ^ (2 * t + 2) := by
    have := Nat.pow_lt_pow_left h2 (n := 2) (by norm_num)
    calc (s + 1) ^ 2 < (2 ^ (t + 1)) ^ 2 := this
      _ = 2 ^ (2 * t + 2) := by rw [← pow_mul]; ring_nf
  have h4 : Nat.log 2 ((s + 1) ^ 2) < 2 * t + 2 :=
    Nat.log_lt_of_lt_pow (by positivity) h3
  rw [PairDecouple.depthLL, ← hs]
  omega

/-- **`log log N` is exponential in `t`.**  With the same `t`,
`log log N ≥ (2^t − 2)·log 2`.  This is the whole mechanism: the budget's exponent is a
polynomial in `t`, the decay's is `2^t`. -/
theorem log_log_ge_triple_log {N : ℕ} (hN : 2 ≤ N) :
    ((2 : ℝ) ^ (Nat.log 2 (Nat.log 2 (Nat.log 2 N) + 1)) - 2) * Real.log 2
      ≤ Real.log (Real.log (N : ℝ)) := by
  set w : ℕ := Nat.log 2 N with hw
  set s : ℕ := Nat.log 2 w with hs
  set t : ℕ := Nat.log 2 (s + 1) with ht
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith
  -- `2 ^ w ≤ N`
  have hwN : (2 : ℕ) ^ w ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hw1 : 1 ≤ w := by
    rw [hw]
    exact Nat.log_pos (by norm_num) hN
  -- `2 ^ s ≤ w`
  have hsw : (2 : ℕ) ^ s ≤ w := Nat.pow_log_le_self 2 (by omega)
  -- `2 ^ t ≤ s + 1`
  have hts : (2 : ℕ) ^ t ≤ s + 1 := Nat.pow_log_le_self 2 (by omega)
  -- real versions
  have hwNR : ((2 : ℝ)) ^ w ≤ (N : ℝ) := by exact_mod_cast hwN
  have hswR : ((2 : ℝ)) ^ s ≤ (w : ℝ) := by exact_mod_cast hsw
  have htsR : ((2 : ℝ)) ^ t ≤ (s : ℝ) + 1 := by exact_mod_cast hts
  -- `log N ≥ 2^s · log 2`
  have hstep1 : ((2 : ℝ)) ^ s * Real.log 2 ≤ Real.log (N : ℝ) := by
    have h1 : Real.log ((2 : ℝ) ^ w) ≤ Real.log (N : ℝ) := by
      refine Real.log_le_log (by positivity) hwNR
    rw [Real.log_pow] at h1
    have h2 : ((2 : ℝ)) ^ s * Real.log 2 ≤ (w : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hswR (le_of_lt hlog2pos)
    linarith
  have hpos : (0 : ℝ) < ((2 : ℝ)) ^ s * Real.log 2 := by positivity
  -- `log log N ≥ s·log 2 + log (log 2)`
  have hstep2 : Real.log (((2 : ℝ)) ^ s * Real.log 2) ≤ Real.log (Real.log (N : ℝ)) :=
    Real.log_le_log hpos hstep1
  have hstep3 : Real.log (((2 : ℝ)) ^ s * Real.log 2)
      = (s : ℝ) * Real.log 2 + Real.log (Real.log 2) := by
    rw [Real.log_mul (by positivity) (by linarith), Real.log_pow]
  -- `log (log 2) ≥ -log 2`
  have hstep4 : -Real.log 2 ≤ Real.log (Real.log 2) := by
    have h1 : Real.log ((2 : ℝ)⁻¹) ≤ Real.log (Real.log 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    rwa [Real.log_inv] at h1
  have hstep5 : ((2 : ℝ)) ^ t - 1 ≤ (s : ℝ) := by linarith
  nlinarith [hstep2, hstep3, hstep4, hstep5, hlog2pos]

/-- **Polynomial beats `2^t`.**  For every `c ≥ 0` and `ε > 0`, eventually
`c(2t+3)³ ≤ ε·2^t`. -/
theorem eventually_cube_le_pow_two {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, c * (2 * (t : ℝ) + 3) ^ 3 ≤ ε * (2 : ℝ) ^ t := by
  have hbase : Tendsto (fun t : ℕ => ((t : ℝ) ^ 3 / (2 : ℝ) ^ t)) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num)
  have hmaj : Tendsto (fun t : ℕ => 125 * ((t : ℝ) ^ 3 / (2 : ℝ) ^ t)) atTop (𝓝 0) := by
    simpa using hbase.const_mul (125 : ℝ)
  have hkey : Tendsto (fun t : ℕ => (2 * (t : ℝ) + 3) ^ 3 / (2 : ℝ) ^ t) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun t => by positivity) ?_ hmaj
    filter_upwards [eventually_ge_atTop 1] with t ht
    have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    have e1 : (0 : ℝ) ≤ ((t : ℝ) - 1) * (t : ℝ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have e2 : (0 : ℝ) ≤ ((t : ℝ) - 1) * (t : ℝ) := mul_nonneg (by linarith) (by linarith)
    have hnum : (2 * (t : ℝ) + 3) ^ 3 ≤ 125 * (t : ℝ) ^ 3 := by nlinarith [e1, e2, h1]
    calc (2 * (t : ℝ) + 3) ^ 3 / (2 : ℝ) ^ t ≤ (125 * (t : ℝ) ^ 3) / (2 : ℝ) ^ t := by gcongr
      _ = 125 * ((t : ℝ) ^ 3 / (2 : ℝ) ^ t) := by ring
  have hεc : (0 : ℝ) < ε / (c + 1) := by positivity
  filter_upwards [hkey.eventually (gt_mem_nhds hεc), eventually_ge_atTop 1] with t hlt _
  have h2 : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  have habs : (2 * (t : ℝ) + 3) ^ 3 / (2 : ℝ) ^ t < ε / (c + 1) := by
    have := hlt
    simpa using this
  have h3 : (2 * (t : ℝ) + 3) ^ 3 ≤ (ε / (c + 1)) * (2 : ℝ) ^ t := by
    rw [div_lt_iff₀ h2] at habs; linarith
  have h4 : c * (2 * (t : ℝ) + 3) ^ 3 ≤ c * ((ε / (c + 1)) * (2 : ℝ) ^ t) :=
    mul_le_mul_of_nonneg_left h3 hc
  have h5 : c * ((ε / (c + 1)) * (2 : ℝ) ^ t) ≤ ε * (2 : ℝ) ^ t := by
    have hc1 : (0 : ℝ) < c + 1 := by linarith
    have : c * (ε / (c + 1)) ≤ ε := by
      rw [mul_div_assoc'] at *
      rw [div_le_iff₀ hc1]
      nlinarith [hε.le, hc]
    nlinarith [h2.le, this]
  linarith

/-! ### The route-decisive absorption -/

/-- **The budget is absorbed.**  A constant budget `C D ≤ exp(c(D+1)³)` — which by
`pow_self_sq_le_exp_cube` covers lap 37's `K^{K²}`, and by monotonicity any
`K^{K²}·b^{κK}·A` — together with a decay `η N ≤ A·(log N)^{-a}`, `a > 0`, satisfies the joint
vanishing clause of `QuantDepthElliottGen`.

The mechanism, in one line: with `t = ⌊log₂(⌊log₂⌊log₂ N⌋⌋+1)⌋`, the budget's exponent is
`≤ c(2t+3)³` (a POLYNOMIAL in `t`) while `log log N ≥ (2^t − 2)log 2` (EXPONENTIAL in `t`).
So the whole `D ≥ 3` route survives lap 37's constant, and the `b^{κD}` budget of
`QuantDepthElliott` was simply the wrong shape, not a real obstruction. -/
theorem budget_absorb {b : ℕ} (hb : 2 ≤ b) {C η : ℕ → ℝ} {c A a : ℝ}
    (hc : 0 ≤ c) (hC0 : ∀ D, 0 ≤ C D) (hCle : ∀ D, C D ≤ Real.exp (c * ((D : ℝ) + 1) ^ 3))
    (hη0 : ∀ N, 0 ≤ η N) (ha : 0 < a)
    (hηle : ∀ᶠ N in atTop, η N ≤ A * (Real.log (N : ℝ)) ^ (-a)) :
    Tendsto (fun N : ℕ => C (PairDecouple.depthLL b N) * η N) atTop (𝓝 0) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmaj : Tendsto (fun N : ℕ => A * (Real.log (N : ℝ)) ^ (-(a / 2))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < a / 2)).comp hlogN
    simpa using h.const_mul A
  -- the triple-log index tends to infinity
  have hL1 : Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop :=
    PairDecouple.tendsto_natLog_atTop 2 le_rfl
  have ht3 : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 (Nat.log 2 N) + 1)) atTop atTop := by
    have h2 : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N)) atTop atTop := hL1.comp hL1
    exact hL1.comp (tendsto_atTop_mono (fun N => Nat.le_succ _) h2)
  have hev : ∀ᶠ t : ℕ in atTop,
      c * (2 * (t : ℝ) + 3) ^ 3 ≤ (a * Real.log 2 / 4) * (2 : ℝ) ^ t :=
    eventually_cube_le_pow_two hc (by positivity)
  refine squeeze_zero' (Eventually.of_forall fun N => mul_nonneg (hC0 _) (hη0 N)) ?_ hmaj
  filter_upwards [hηle, ht3.eventually hev, ht3.eventually (eventually_ge_atTop 2),
    eventually_ge_atTop 2, hlogN.eventually (eventually_gt_atTop (1 : ℝ))]
    with N hη hcube ht2 hN2 hlog1
  set t : ℕ := Nat.log 2 (Nat.log 2 (Nat.log 2 N) + 1) with htdef
  set D : ℕ := PairDecouple.depthLL b N with hDdef
  have hlogNpos : (0 : ℝ) < Real.log (N : ℝ) := by linarith
  -- (1) `D + 1 ≤ 2t + 3`
  have hDle : (D : ℝ) + 1 ≤ 2 * (t : ℝ) + 3 := by
    have h := depthLL_le_triple_log hb N
    rw [← hDdef, ← htdef] at h
    have hR : (D : ℝ) ≤ 2 * (t : ℝ) + 2 := by exact_mod_cast h
    linarith
  -- (2) the budget exponent is at most `(a/2)·log log N`
  have hcube1 : c * ((D : ℝ) + 1) ^ 3 ≤ c * (2 * (t : ℝ) + 3) ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hDle 3) hc
  have hll := log_log_ge_triple_log (N := N) hN2
  rw [← htdef] at hll
  have hpow2 : (4 : ℝ) ≤ (2 : ℝ) ^ t := by
    have h : ((2 : ℝ)) ^ (2 : ℕ) ≤ (2 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) ht2
    norm_num at h
    linarith
  have hhalf : (a * Real.log 2 / 4) * (2 : ℝ) ^ t
      ≤ (a / 2) * (((2 : ℝ) ^ t - 2) * Real.log 2) := by
    have hprod : (0 : ℝ) ≤ a * Real.log 2 * ((2 : ℝ) ^ t - 4) :=
      mul_nonneg (mul_nonneg ha.le hl2.le) (by linarith)
    nlinarith [hprod]
  have hkey : c * ((D : ℝ) + 1) ^ 3 ≤ (a / 2) * Real.log (Real.log (N : ℝ)) := by
    have hmono : (a / 2) * (((2 : ℝ) ^ t - 2) * Real.log 2)
        ≤ (a / 2) * Real.log (Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hll (by linarith)
    linarith
  -- (3) `C D ≤ (log N)^{a/2}`
  have hCbound : C D ≤ (Real.log (N : ℝ)) ^ (a / 2) := by
    refine (hCle D).trans ?_
    rw [Real.rpow_def_of_pos hlogNpos]
    exact Real.exp_le_exp.2 (by nlinarith [hkey])
  -- (4) combine
  calc C D * η N
      ≤ (Real.log (N : ℝ)) ^ (a / 2) * (A * (Real.log (N : ℝ)) ^ (-a)) :=
        mul_le_mul hCbound hη (hη0 N) (Real.rpow_nonneg hlogNpos.le _)
    _ = A * ((Real.log (N : ℝ)) ^ (a / 2) * (Real.log (N : ℝ)) ^ (-a)) := by ring
    _ = A * (Real.log (N : ℝ)) ^ (a / 2 + -a) := by rw [Real.rpow_add hlogNpos]
    _ = A * (Real.log (N : ℝ)) ^ (-(a / 2)) := by rw [show a / 2 + -a = -(a / 2) by ring]

/-- `depthLL b N ≤ 2·t_N + 2`, in the `tIdx` spelling. -/
theorem depthLL_le_tIdx {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    PairDecouple.depthLL b N ≤ 2 * tIdx N + 2 := depthLL_le_triple_log hb N

/-- **The SHARP absorption, and the sharpest statement of what the `D ≥ 3` route needs.**
A budget `C D ≤ exp(c(D+1)³)` — which covers lap 37's `K^{K²}` and, more to the point, covers
the `exp(Θ(K²))` that the powerful-modulus expansion *intrinsically* costs — is absorbed by the
decay

    η N ≤ exp(−t_N⁴)  ,   t_N ≍ log log log N .

This is strictly stronger than every fixed power of `log log N` (because
`(log log N)^{-m} = exp(−m·t_N·log 2 + O(1))`, LINEAR in `t_N`), but only quasi-polynomially so
— and it is far weaker than the `(log N)^{-a}` of `budget_absorb`.  So the honest ledger entry
for the `D ≥ 3` route is: *the `K`-point log-Elliott saving must beat every power of
`log log N`, by a quasi-polynomial margin in `log log log N`.* -/
theorem budget_absorb_of_tIdx {b : ℕ} (hb : 2 ≤ b) {C η : ℕ → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hC0 : ∀ D, 0 ≤ C D) (hCle : ∀ D, C D ≤ Real.exp (c * ((D : ℝ) + 1) ^ 3))
    (hη0 : ∀ N, 0 ≤ η N)
    (hηle : ∀ᶠ N in atTop, η N ≤ Real.exp (-((tIdx N : ℝ) ^ 4))) :
    Tendsto (fun N : ℕ => C (PairDecouple.depthLL b N) * η N) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun N : ℕ => Real.exp (-(tIdx N : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.comp tendsto_tIdx)
  refine squeeze_zero' (Eventually.of_forall fun N => mul_nonneg (hC0 _) (hη0 N)) ?_ hmaj
  have hev : ∀ᶠ t : ℕ in atTop, c * (2 * (t : ℝ) + 3) ^ 3 - (t : ℝ) ^ 4 ≤ -(t : ℝ) := by
    filter_upwards [eventually_ge_atTop (⌈125 * c⌉₊ + 1), eventually_ge_atTop 1] with t ht ht1
    have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
    have hcast : (125 * c : ℝ) + 1 ≤ (t : ℝ) := by
      have hc1 : ((⌈125 * c⌉₊ + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      have hc2 : (125 * c : ℝ) ≤ ((⌈125 * c⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      push_cast at hc1
      linarith
    have e1 : (0 : ℝ) ≤ ((t : ℝ) - 1) * (t : ℝ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have e2 : (0 : ℝ) ≤ ((t : ℝ) - 1) * (t : ℝ) := mul_nonneg (by linarith) (by linarith)
    have hnum : (2 * (t : ℝ) + 3) ^ 3 ≤ 125 * (t : ℝ) ^ 3 := by nlinarith [e1, e2, h1]
    have hstep : c * (2 * (t : ℝ) + 3) ^ 3 ≤ 125 * c * (t : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_left hnum hc
      linarith
    have hA : (0 : ℝ) ≤ (t : ℝ) ^ 3 * ((t : ℝ) - 125 * c - 1) :=
      mul_nonneg (by positivity) (by linarith)
    have hB : (t : ℝ) ≤ (t : ℝ) ^ 3 := by nlinarith [e1, e2, h1]
    nlinarith [hstep, hA, hB]
  filter_upwards [hηle, tendsto_tIdx.eventually hev] with N hη hlt
  set t : ℕ := tIdx N with htdef
  set D : ℕ := PairDecouple.depthLL b N with hDdef
  have hDle : (D : ℝ) + 1 ≤ 2 * (t : ℝ) + 3 := by
    have h := depthLL_le_tIdx hb N
    rw [← hDdef, ← htdef] at h
    have hR : (D : ℝ) ≤ 2 * (t : ℝ) + 2 := by exact_mod_cast h
    linarith
  have hCbound : C D ≤ Real.exp (c * (2 * (t : ℝ) + 3) ^ 3) :=
    (hCle D).trans (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hDle 3) hc))
  calc C D * η N
      ≤ Real.exp (c * (2 * (t : ℝ) + 3) ^ 3) * Real.exp (-((t : ℝ) ^ 4)) :=
        mul_le_mul hCbound hη (hη0 N) (Real.exp_nonneg _)
    _ = Real.exp (c * (2 * (t : ℝ) + 3) ^ 3 - (t : ℝ) ^ 4) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(t : ℝ)) := Real.exp_le_exp.2 hlt

/-! ### The endpoint the `K`-fold assembly aims at -/

/-- **Lap 37's constant, in the cap's shape.**  `A₀·K^{K²}·b^{κK} ≤ exp(c(K+1)³)` with the
explicit `c = log A₀ + 1 + κ·log b`.  The three factors are the three terms of `c`:
`A₀` pays `log A₀·(K+1)³ ≥ log A₀`, the exchange constant `K^{K²}` pays `(K+1)³ ≥ K³`, and the
`b^{κK}` of `QuantDepthElliott`'s original budget pays `κ log b·(K+1)³ ≥ κ log b·K`. -/
theorem kfold_budget_le_exp_cube {b : ℕ} (hb : 1 ≤ b) (κ : ℕ) {A₀ : ℝ} (hA₀ : 1 ≤ A₀) (D : ℕ) :
    A₀ * (((D : ℝ)) ^ (D * D) * (b : ℝ) ^ (κ * D))
      ≤ Real.exp ((Real.log A₀ + 1 + κ * Real.log b) * ((D : ℝ) + 1) ^ 3) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hlogb : 0 ≤ Real.log b := Real.log_natCast_nonneg b
  have hlogA : 0 ≤ Real.log A₀ := Real.log_nonneg hA₀
  have hA0 : (0 : ℝ) < A₀ := by linarith
  have h1 : A₀ = Real.exp (Real.log A₀) := (Real.exp_log hA0).symm
  have h2 : ((D : ℝ)) ^ (D * D) ≤ Real.exp ((D : ℝ) ^ 3) := pow_self_sq_le_exp_cube D
  have h3 : (b : ℝ) ^ (κ * D) = Real.exp (((κ : ℝ) * D) * Real.log b) := by
    rw [show (((κ : ℝ) * D) * Real.log b) = ((κ * D : ℕ) : ℝ) * Real.log b by push_cast; ring,
      ← Real.log_pow, Real.exp_log (by positivity)]
  have hnn : (0 : ℝ) ≤ ((D : ℝ)) ^ (D * D) := by positivity
  have hstep : A₀ * (((D : ℝ)) ^ (D * D) * (b : ℝ) ^ (κ * D))
      ≤ Real.exp (Real.log A₀ + ((D : ℝ) ^ 3 + ((κ : ℝ) * D) * Real.log b)) := by
    rw [Real.exp_add, Real.exp_add, ← h3, ← h1]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by positivity)) hA0.le
  refine hstep.trans (Real.exp_le_exp.2 ?_)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hc1 : (1 : ℝ) ≤ ((D : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hc2 : ((D : ℝ)) ^ 3 ≤ ((D : ℝ) + 1) ^ 3 := by
    refine pow_le_pow_left₀ hD0 (by linarith) 3
  have hc3 : (D : ℝ) ≤ ((D : ℝ) + 1) ^ 3 := by nlinarith [hD0, hc1]
  have e1 : Real.log A₀ * 1 ≤ Real.log A₀ * ((D : ℝ) + 1) ^ 3 :=
    mul_le_mul_of_nonneg_left hc1 hlogA
  have e2 : (κ : ℝ) * Real.log b * (D : ℝ) ≤ (κ : ℝ) * Real.log b * ((D : ℝ) + 1) ^ 3 :=
    mul_le_mul_of_nonneg_left hc3 (by positivity)
  nlinarith [e1, e2, hc2]

/-- **The endpoint of the `K`-fold campaign, stated once.**  Suppose the assembly of laps 36–39
delivers, for every twist, a depth-uniform bound of the shape it is producing —
`‖depthAvg‖ ≤ A₀·D^{D²}·b^{κD}·η N` — with the Selberg–Delange-shaped decay
`η N ≤ A (log N)^{-a}`, `a > 0`.  Then the crux `WeylLambertTwist b` holds.

This is the honest target the `D ≥ 3` route is now aiming at, and it is exactly
`QuantDepthElliott` with the budget repaired. -/
theorem weylLambertTwist_of_kfold_bound {b : ℕ} (hb : 3 ≤ b) {κ : ℕ} {A₀ A a : ℝ}
    (hA₀ : 1 ≤ A₀) (ha : 0 < a)
    (H : ∀ (P Q j : ℕ) (hh : ℤ), 0 < Q → 0 < j → j < Q →
      ∃ η : ℕ → ℝ, (∀ N, 0 ≤ η N) ∧
        (∀ᶠ N in atTop, η N ≤ A * (Real.log (N : ℝ)) ^ (-a)) ∧
        (∀ D N : ℕ, ‖depthAvg b P Q j hh D N‖
          ≤ (A₀ * (((D : ℝ)) ^ (D * D) * (b : ℝ) ^ (κ * D))) * η N)) :
    WeylLambertTwist b := by
  have hb1 : 1 ≤ b := by omega
  have hlogb : 0 ≤ Real.log b := Real.log_natCast_nonneg b
  have hlogA : 0 ≤ Real.log A₀ := Real.log_nonneg hA₀
  refine weylLambertTwist_of_quantDepthElliottGen hb fun P Q j hh hQ hj0 hjQ => ?_
  obtain ⟨η, hη0, hηle, hbd⟩ := H P Q j hh hQ hj0 hjQ
  refine ⟨fun D => A₀ * (((D : ℝ)) ^ (D * D) * (b : ℝ) ^ (κ * D)), η, hη0, hbd, ?_⟩
  refine budget_absorb (b := b) (c := Real.log A₀ + 1 + κ * Real.log b) (by omega)
    (by positivity) (fun D => by positivity) (fun D => kfold_budget_le_exp_cube hb1 κ hA₀ D)
    hη0 ha hηle

#print axioms QuantDepthElliottGen
#print axioms weylLambertTwist_of_quantDepthElliottGen
#print axioms quantDepthElliottGen_of_quantDepthElliott
#print axioms pow_self_sq_le_exp_cube
#print axioms depthLL_le_triple_log
#print axioms log_log_ge_triple_log
#print axioms eventually_cube_le_pow_two
#print axioms budget_absorb
#print axioms tendsto_tIdx
#print axioms depthLL_le_tIdx
#print axioms budget_absorb_of_tIdx
#print axioms kfold_budget_le_exp_cube
#print axioms weylLambertTwist_of_kfold_bound

end CastingOut

end NormalNumbers
