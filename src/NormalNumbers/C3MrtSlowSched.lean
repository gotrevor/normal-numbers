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

variable {Pnp : (ℕ → ℂ) → ℝ → ℝ → Prop}

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


/-! ### The `θ < 1` exponent estimate

The saving now carries an extra `1/(2+2t)`, `t = log(u_N+1)`, from the logarithmic factor `W` in
the schedule.  A power of `t` is no obstruction: the majorant lemma below absorbs it by halving
the exponential rate. -/

/-- A power of a linear function, minus an exponential DIVIDED by a linear function, still goes
to `-∞`: halve the rate and the linear divisor is swallowed whole. -/
theorem tendsto_polyPow_sub_expDiv {α c₁ : ℝ} (hα : 0 < α) (hc₁ : 0 < c₁) (p : ℕ) :
    Tendsto (fun t : ℝ => (2 + 3 * t) ^ p - c₁ * ((Real.exp (α * t) - 3) / (2 + 2 * t)))
      atTop atBot := by
  have hα2 : (0 : ℝ) < α / 2 := by linarith
  have hmaj := tendsto_polyPow_sub_exp hα2 hc₁ p
  refine tendsto_atBot_mono' atTop ?_ hmaj
  have hR := tendsto_exp_div_polyPow hα2 1
  filter_upwards [hR.eventually_ge_atTop 2, Filter.eventually_ge_atTop (1 : ℝ)] with t ht ht1
  set E : ℝ := Real.exp (α / 2 * t) with hEdef
  have hS : (0 : ℝ) < 2 + 2 * t := by linarith
  have hE5 : 5 + 2 * t ≤ E := by
    rw [pow_one] at ht
    have hp : (0 : ℝ) < 2 + 3 * t := by linarith
    rw [le_div_iff₀ hp] at ht
    linarith
  have hEsq : Real.exp (α * t) = E ^ 2 := by
    rw [hEdef, sq, ← Real.exp_add]
    congr 1
    ring
  have hkey : E - 3 ≤ (Real.exp (α * t) - 3) / (2 + 2 * t) := by
    rw [hEsq, le_div_iff₀ hS]
    nlinarith [hE5, ht1]
  have := mul_le_mul_of_nonneg_left hkey hc₁.le
  linarith

/-- **The geometric profile drives the exponent to `-∞` for EVERY `θ < 1`, on the slow schedule.**

This is the payoff of `C3MrtSlowSched`: `C3MrtUnifK.exponent_tendsto_atBot_of_geom_le` needs
`θ < 1/2` because it pays `b^{D_N} ≍ (u_N+1)²`; here `b^{D_N} ≤ b(u_N+1)(2+2\log(u_N+1))`, so the
surviving saving is `u^{1-θ}(\log u)^{-θ}`, which still beats `\log Cst = (D_N+1)^m = O(\log u)^m`
for every `θ < 1`. -/
theorem exponent_tendsto_atBot_of_geom_slow {b : ℕ} (hb : 2 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) {κ : ℝ} (hκ : 0 < κ) (m : ℕ)
    (KN : ℕ → ℕ) (hKle : ∀ᶠ N : ℕ in atTop, KN N ≤ depthSlow b N) :
    Tendsto (fun N : ℕ =>
        Real.log (CstKdeg m (KN N))
          - κ * cKgeom c₀ θ b (KN N)
            * Real.log (2 * Real.log ((N / 2 ^ (Nat.log 2 (Nat.log 2 N)) : ℕ) : ℝ)))
      atTop atBot := by
  have hbR : (1 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  set α : ℝ := 1 - θ with hαdef
  have hα : 0 < α := by rw [hαdef]; linarith
  set c₁ : ℝ := κ * c₀ * (b : ℝ) ^ (-θ) * Real.log 2 with hc₁def
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hbθ : (0 : ℝ) < (b : ℝ) ^ (-θ) := Real.rpow_pos_of_pos hb0 _
  have hc₁ : 0 < c₁ := by rw [hc₁def]; positivity
  have hu : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N)) atTop atTop :=
    (PairDecouple.tendsto_natLog_atTop 2 le_rfl).comp
      (PairDecouple.tendsto_natLog_atTop 2 le_rfl)
  have ht : Tendsto (fun N : ℕ => Real.log ((Nat.log 2 (Nat.log 2 N) : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hu |>.atTop_add
      tendsto_const_nhds)
  have hmaj := (tendsto_polyPow_sub_expDiv hα hc₁ m).comp ht
  refine tendsto_atBot_mono' atTop ?_ hmaj
  filter_upwards [Filter.eventually_ge_atTop 1024, hu.eventually_ge_atTop 3, hKle,
    depthSlow_le_depthLL hb] with N hN hu3 hKN hSL
  set u : ℕ := Nat.log 2 (Nat.log 2 N) with hudef
  set t : ℝ := Real.log ((u : ℝ) + 1) with htdef
  set D : ℕ := KN N with hDdef
  set L : ℝ := Real.log (2 * Real.log ((N / 2 ^ u : ℕ) : ℝ)) with hLdef
  have hu1 : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
  have hupos : (0 : ℝ) < (u : ℝ) + 1 := by linarith
  have hllp : llProxy N = (u : ℝ) + 1 := by rw [llProxy]
  have hlogllp : Real.log (llProxy N) = t := by rw [hllp]
  have ht0 : 0 ≤ t := by
    rw [htdef]; exact Real.log_nonneg (by linarith)
  have hS : (0 : ℝ) < 2 + 2 * t := by linarith
  -- the constant side
  have hDLL : D ≤ PairDecouple.depthLL b N := le_trans hKN hSL
  have hCst : Real.log (CstKdeg m D) = ((D : ℝ) + 1) ^ m := by
    unfold CstKdeg; rw [Real.log_exp]
  have hDle : ((D : ℝ) + 1) ≤ 2 + 3 * t := by
    have h1 := depthLL_succ_le_log hb N
    rw [hllp] at h1
    have h2 : ((D : ℝ)) ≤ ((PairDecouple.depthLL b N : ℝ)) := by exact_mod_cast hDLL
    linarith
  have hCstle : Real.log (CstKdeg m D) ≤ (2 + 3 * t) ^ m := by
    rw [hCst]
    exact pow_le_pow_left₀ (by positivity) hDle m
  -- the saving side: `b^D ≤ b·(u+1)·(2+2t)`
  have hpowD : (b : ℝ) ^ D ≤ (b : ℝ) * (((u : ℝ) + 1) * (2 + 2 * t)) := by
    have h1 : (b : ℝ) ^ D ≤ (b : ℝ) ^ depthSlow b N :=
      pow_le_pow_right₀ hbR.le hKN
    have h2 := pow_depthSlow_le_log hb N
    rw [hllp, ← htdef] at h2
    linarith
  set M : ℝ := (b : ℝ) * (((u : ℝ) + 1) * (2 + 2 * t)) with hMdef
  have hM : (0 : ℝ) < M := by rw [hMdef]; positivity
  have hA : (b : ℝ) ^ (-θ) * (((u : ℝ) + 1) ^ (-θ) * (1 / (2 + 2 * t)))
      ≤ (b : ℝ) ^ (-(θ * (D : ℕ))) := by
    have hprodpos : (0 : ℝ) < (b : ℝ) ^ (-θ) * ((u : ℝ) + 1) ^ (-θ) := by
      have : (0 : ℝ) < ((u : ℝ) + 1) ^ (-θ) := Real.rpow_pos_of_pos hupos _
      positivity
    have h2 : (1 : ℝ) / (2 + 2 * t) ≤ (2 + 2 * t) ^ (-θ) := by
      have hone : (1 : ℝ) ≤ 2 + 2 * t := by linarith
      have := Real.rpow_le_rpow_of_exponent_le hone (by linarith : (-1 : ℝ) ≤ -θ)
      rw [one_div]
      rwa [Real.rpow_neg_one] at this
    have hsplit : (b : ℝ) ^ (-θ) * (((u : ℝ) + 1) ^ (-θ) * (2 + 2 * t) ^ (-θ)) = M ^ (-θ) := by
      rw [hMdef, Real.mul_rpow hb0.le (by positivity),
        Real.mul_rpow hupos.le (by linarith : (0:ℝ) ≤ 2 + 2 * t)]
    have h3 : M ^ (-θ) ≤ (b : ℝ) ^ (-(θ * (D : ℕ))) := by
      have he2 : -(θ * (D : ℝ)) = (D : ℝ) * (-θ) := by ring
      have hrhs : (b : ℝ) ^ (-(θ * ((D : ℕ) : ℝ))) = ((b : ℝ) ^ ((D : ℕ) : ℝ)) ^ (-θ) := by
        rw [← Real.rpow_mul hb0.le, he2]
      have hpowD' : (b : ℝ) ^ ((D : ℕ) : ℝ) ≤ M := by
        rw [Real.rpow_natCast]; exact hpowD
      rw [hrhs]
      exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hb0 _) hpowD' (by linarith)
    calc (b : ℝ) ^ (-θ) * (((u : ℝ) + 1) ^ (-θ) * (1 / (2 + 2 * t)))
        = ((b : ℝ) ^ (-θ) * ((u : ℝ) + 1) ^ (-θ)) * (1 / (2 + 2 * t)) := by ring
      _ ≤ ((b : ℝ) ^ (-θ) * ((u : ℝ) + 1) ^ (-θ)) * (2 + 2 * t) ^ (-θ) :=
          mul_le_mul_of_nonneg_left h2 hprodpos.le
      _ = M ^ (-θ) := by rw [← hsplit]; ring
      _ ≤ (b : ℝ) ^ (-(θ * (D : ℕ))) := h3
  -- the cut side
  have hL : ((u : ℝ) - 2) * Real.log 2 ≤ L := by
    rw [hLdef, hudef]
    exact log_two_log_cut_ge N hN
  have hL0 : (0 : ℝ) ≤ ((u : ℝ) - 2) * Real.log 2 := by nlinarith [hu1, hlog2]
  -- `(u+1)^{-θ}(u-2) ≥ exp(αt) - 3`
  have hrpow_a : ((u : ℝ) + 1) ^ α = Real.exp (α * t) := by
    rw [Real.rpow_def_of_pos hupos]
    congr 1
    rw [htdef]; ring
  have hrpow_b : ((u : ℝ) + 1) ^ (-θ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hrpow_c : (0 : ℝ) < ((u : ℝ) + 1) ^ (-θ) := Real.rpow_pos_of_pos hupos _
  have hsplit2 : ((u : ℝ) + 1) ^ (-θ) * ((u : ℝ) - 2)
      = ((u : ℝ) + 1) ^ α - 3 * ((u : ℝ) + 1) ^ (-θ) := by
    have h1 : ((u : ℝ) + 1) ^ (-θ) * ((u : ℝ) + 1) = ((u : ℝ) + 1) ^ α := by
      rw [← Real.rpow_add_one (ne_of_gt hupos) (-θ)]
      congr 1
      rw [hαdef]; ring
    have h2 : ((u : ℝ) - 2) = ((u : ℝ) + 1) - 3 := by ring
    rw [h2, mul_sub, h1]
    ring
  have hnum : Real.exp (α * t) - 3 ≤ ((u : ℝ) + 1) ^ (-θ) * ((u : ℝ) - 2) := by
    rw [hsplit2, hrpow_a]
    nlinarith [hrpow_b, hrpow_c]
  -- assemble the saving
  have hsav : c₁ * ((Real.exp (α * t) - 3) / (2 + 2 * t)) ≤ κ * cKgeom c₀ θ b D * L := by
    have hstep1 : c₁ * ((Real.exp (α * t) - 3) / (2 + 2 * t))
        ≤ c₁ * ((((u : ℝ) + 1) ^ (-θ) * ((u : ℝ) - 2)) / (2 + 2 * t)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hS.le) hc₁.le
    have hid : c₁ * ((((u : ℝ) + 1) ^ (-θ) * ((u : ℝ) - 2)) / (2 + 2 * t))
        = κ * c₀ * ((b : ℝ) ^ (-θ) * (((u : ℝ) + 1) ^ (-θ) * (1 / (2 + 2 * t))))
          * (((u : ℝ) - 2) * Real.log 2) := by
      rw [hc₁def]; field_simp
    have hpos : (0 : ℝ) < κ * c₀ := by positivity
    have hstep2 : κ * c₀ * ((b : ℝ) ^ (-θ) * (((u : ℝ) + 1) ^ (-θ) * (1 / (2 + 2 * t))))
        * (((u : ℝ) - 2) * Real.log 2)
        ≤ κ * c₀ * (b : ℝ) ^ (-(θ * (D : ℕ))) * (((u : ℝ) - 2) * Real.log 2) := by
      refine mul_le_mul_of_nonneg_right ?_ hL0
      exact mul_le_mul_of_nonneg_left hA hpos.le
    have hstep3 : κ * c₀ * (b : ℝ) ^ (-(θ * (D : ℕ))) * (((u : ℝ) - 2) * Real.log 2)
        ≤ κ * cKgeom c₀ θ b D * L := by
      have hfacpos : (0 : ℝ) < κ * c₀ * (b : ℝ) ^ (-(θ * (D : ℕ))) := by
        have : (0 : ℝ) < (b : ℝ) ^ (-(θ * (D : ℕ))) := Real.rpow_pos_of_pos hb0 _
        positivity
      have hid2 : κ * cKgeom c₀ θ b D = κ * c₀ * (b : ℝ) ^ (-(θ * (D : ℕ))) := by
        rw [cKgeom]; ring
      rw [hid2]
      exact mul_le_mul_of_nonneg_left hL hfacpos.le
    calc c₁ * ((Real.exp (α * t) - 3) / (2 + 2 * t))
        ≤ c₁ * ((((u : ℝ) + 1) ^ (-θ) * ((u : ℝ) - 2)) / (2 + 2 * t)) := hstep1
      _ = _ := hid
      _ ≤ κ * c₀ * (b : ℝ) ^ (-(θ * (D : ℕ))) * (((u : ℝ) - 2) * Real.log 2) := hstep2
      _ ≤ κ * cKgeom c₀ θ b D * L := hstep3
  have hfinal : ((fun t : ℝ => (2 + 3 * t) ^ m - c₁ * ((Real.exp (α * t) - 3) / (2 + 2 * t)))
      ∘ fun N : ℕ => Real.log ((Nat.log 2 (Nat.log 2 N) : ℝ) + 1)) N
      = (2 + 3 * t) ^ m - c₁ * ((Real.exp (α * t) - 3) / (2 + 2 * t)) := rfl
  rw [hfinal]
  linarith [hCstle, hsav]


/-! ### Discharging the threshold data for the geometric profile

The threshold is not a hypothesis: for every `θ < 1` it can be CONSTRUCTED.  The demand is
`log log Athr K ≳ b^{θK} log K`, so at the diagonal level `K = D_N` it costs
`(u_N log u_N)^θ log log u_N`, while the budget `log log a_N ≍ u_N·log 2` is a full power of
`u_N` — the same `u^{1-θ}` margin that `exponent_tendsto_atBot_of_geom_slow` runs on. -/

/-- The required `log log` of the threshold at level `K`. -/
noncomputable def thrPhi (b M₀ : ℕ) (κ c₀ θ : ℝ) (K : ℕ) : ℝ :=
  (b : ℝ) ^ (θ * K) * Real.log ((K : ℝ) + 2 + (M₀ : ℝ)) / (κ * c₀ * Real.log 2)

/-- The explicit threshold: a double exponential in `thrPhi`. -/
noncomputable def thrAthr (b M₀ : ℕ) (κ c₀ θ : ℝ) (K : ℕ) : ℕ :=
  2 ^ (2 ^ ⌈thrPhi b M₀ κ c₀ θ K⌉₊)

theorem two_le_thrAthr (b M₀ : ℕ) (κ c₀ θ : ℝ) (K : ℕ) : 2 ≤ thrAthr b M₀ κ c₀ θ K := by
  rw [thrAthr]
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ ⌈thrPhi b M₀ κ c₀ θ K⌉₊) :=
        Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow

/-- `2 log (thrAthr K) ≥ 2 ^ ⌈φ K⌉`. -/
theorem pow_ceil_le_two_log_thrAthr (b M₀ : ℕ) (κ c₀ θ : ℝ) (K : ℕ) :
    ((2 : ℝ) ^ ⌈thrPhi b M₀ κ c₀ θ K⌉₊) ≤ 2 * Real.log (thrAthr b M₀ κ c₀ θ K) := by
  set g : ℕ := ⌈thrPhi b M₀ κ c₀ θ K⌉₊ with hg
  have hcast : ((thrAthr b M₀ κ c₀ θ K : ℕ) : ℝ) = (2 : ℝ) ^ ((2 ^ g : ℕ)) := by
    rw [thrAthr, ← hg]; push_cast; ring
  rw [hcast, Real.log_pow]
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hpow : ((2 : ℝ)) ^ g ≤ ((2 ^ g : ℕ) : ℝ) := by push_cast; ring_nf; exact le_rfl
  have hp0 : (0 : ℝ) ≤ ((2 ^ g : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [hpow, hlog2, hp0]

theorem thrPhi_monotone {b M₀ : ℕ} (hb : 2 ≤ b) {κ c₀ θ : ℝ} (hκ : 0 < κ) (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) : Monotone (thrPhi b M₀ κ c₀ θ) := by
  have hbR : (1 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  intro K₁ K₂ hK
  have hKR : (K₁ : ℝ) ≤ (K₂ : ℝ) := by exact_mod_cast hK
  have h1 : (b : ℝ) ^ (θ * K₁) ≤ (b : ℝ) ^ (θ * K₂) := by
    refine Real.rpow_le_rpow_of_exponent_le hbR.le ?_
    nlinarith [hKR, hθ0]
  have h2 : Real.log ((K₁ : ℝ) + 2 + (M₀ : ℝ)) ≤ Real.log ((K₂ : ℝ) + 2 + (M₀ : ℝ)) := by
    refine Real.log_le_log (by positivity) (by linarith)
  have h1pos : (0 : ℝ) < (b : ℝ) ^ (θ * K₁) := Real.rpow_pos_of_pos (by linarith) _
  have hM0R : (0 : ℝ) ≤ (M₀ : ℝ) := Nat.cast_nonneg _
  have hK1R : (0 : ℝ) ≤ (K₁ : ℝ) := Nat.cast_nonneg _
  have h2pos : (0 : ℝ) ≤ Real.log ((K₁ : ℝ) + 2 + (M₀ : ℝ)) :=
    Real.log_nonneg (by linarith)
  rw [thrPhi, thrPhi]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  nlinarith [h1, h2, h1pos, h2pos]

theorem thrAthr_monotone {b M₀ : ℕ} (hb : 2 ≤ b) {κ c₀ θ : ℝ} (hκ : 0 < κ) (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) : Monotone (thrAthr b M₀ κ c₀ θ) := by
  intro K₁ K₂ hK
  have h := Nat.ceil_mono (thrPhi_monotone (M₀ := M₀) hb hκ hc₀ hθ0 hK)
  exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)

/-- **Clause (ii): the threshold really does beat the required power.** -/
theorem thrAthr_rpow_ge {b : ℕ} (hb : 2 ≤ b) {Q P : ℕ} {κ c₀ θ : ℝ} (hκ : 0 < κ) (hc₀ : 0 < c₀)
    (K : ℕ) :
    max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
      ≤ (2 * Real.log (thrAthr b (Q * primorial P) κ c₀ θ K)) ^ (κ * cKgeom c₀ θ b K) := by
  set M₀ : ℕ := Q * primorial P with hM₀
  set g : ℕ := ⌈thrPhi b M₀ κ c₀ θ K⌉₊ with hg
  have hbR : (1 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set e : ℝ := κ * cKgeom c₀ θ b K with hedef
  have he : 0 < e := by
    rw [hedef, cKgeom]
    have : (0 : ℝ) < (b : ℝ) ^ (-(θ * K)) := Real.rpow_pos_of_pos hb0 _
    positivity
  -- the target `T`
  set T : ℝ := max (max 2 ((K : ℝ) + 1)) ((M₀ : ℕ) : ℝ) with hT
  have hT1 : (1 : ℝ) ≤ T := le_trans (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hTle : T ≤ (K : ℝ) + 2 + (M₀ : ℝ) := by
    have hM0 : (0 : ℝ) ≤ ((M₀ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    refine max_le (max_le (by linarith) (by linarith)) (by linarith)
  -- the lower bound on the base
  have hbase : ((2 : ℝ) ^ g) ≤ 2 * Real.log (thrAthr b M₀ κ c₀ θ K) :=
    pow_ceil_le_two_log_thrAthr b M₀ κ c₀ θ K
  have hbasepos : (0 : ℝ) < (2 : ℝ) ^ g := by positivity
  have hstep1 : ((2 : ℝ) ^ g) ^ e
      ≤ (2 * Real.log (thrAthr b M₀ κ c₀ θ K)) ^ e :=
    Real.rpow_le_rpow hbasepos.le hbase he.le
  -- the exponent arithmetic
  have hgphi : thrPhi b M₀ κ c₀ θ K ≤ (g : ℝ) := Nat.le_ceil _
  have hprod : (b : ℝ) ^ (θ * K) * (b : ℝ) ^ (-(θ * K)) = 1 := by
    rw [← Real.rpow_add hb0]; simp
  have hkey : Real.log T ≤ (g : ℝ) * e * Real.log 2 := by
    have hden : (0 : ℝ) < κ * c₀ * Real.log 2 := by positivity
    have hphi : (b : ℝ) ^ (θ * K) * Real.log ((K : ℝ) + 2 + (M₀ : ℝ))
        ≤ (g : ℝ) * (κ * c₀ * Real.log 2) := by
      rw [thrPhi, div_le_iff₀ hden] at hgphi
      exact hgphi
    have hmul : Real.log ((K : ℝ) + 2 + (M₀ : ℝ))
        ≤ (g : ℝ) * (κ * c₀ * Real.log 2) * (b : ℝ) ^ (-(θ * K)) := by
      have hbneg : (0 : ℝ) < (b : ℝ) ^ (-(θ * K)) := Real.rpow_pos_of_pos hb0 _
      have := mul_le_mul_of_nonneg_right hphi hbneg.le
      calc Real.log ((K : ℝ) + 2 + (M₀ : ℝ))
          = (b : ℝ) ^ (θ * K) * (b : ℝ) ^ (-(θ * K))
              * Real.log ((K : ℝ) + 2 + (M₀ : ℝ)) := by rw [hprod]; ring
        _ = (b : ℝ) ^ (θ * K) * Real.log ((K : ℝ) + 2 + (M₀ : ℝ))
              * (b : ℝ) ^ (-(θ * K)) := by ring
        _ ≤ (g : ℝ) * (κ * c₀ * Real.log 2) * (b : ℝ) ^ (-(θ * K)) := this
    have hTlog : Real.log T ≤ Real.log ((K : ℝ) + 2 + (M₀ : ℝ)) :=
      Real.log_le_log (by linarith) hTle
    have hid : (g : ℝ) * (κ * c₀ * Real.log 2) * (b : ℝ) ^ (-(θ * K))
        = (g : ℝ) * e * Real.log 2 := by
      rw [hedef, cKgeom]; ring
    linarith [hTlog, hmul, hid.le, hid.ge]
  have hstep2 : T ≤ ((2 : ℝ) ^ g) ^ e := by
    have h1 : ((2 : ℝ) ^ g) ^ e = Real.exp ((g : ℝ) * e * Real.log 2) := by
      rw [show ((2 : ℝ) ^ g) = (2 : ℝ) ^ ((g : ℕ) : ℝ) from (Real.rpow_natCast 2 g).symm,
        ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
      congr 1
      ring
    rw [h1]
    calc T = Real.exp (Real.log T) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp ((g : ℝ) * e * Real.log 2) := Real.exp_le_exp.2 hkey
  exact le_trans hstep2 hstep1

/-- `k + 1 ≤ 2 ^ k`. -/
theorem add_one_le_two_pow : ∀ k : ℕ, k + 1 ≤ 2 ^ k := by
  intro k
  induction k with
  | zero => norm_num
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
    omega

/-- **The Nat reduction for clause (iii).**  A double-exponential threshold `2^{2^g}` clears the
cut `N / 2^{u_N}` as soon as `g + 1 ≤ u_N`: then `2^g + u_N ≤ 2^{u_N} ≤ log₂ N`. -/
theorem two_pow_two_pow_le_cut {N g : ℕ} (hN : 2 ≤ N)
    (hg : g + 1 ≤ Nat.log 2 (Nat.log 2 N)) :
    2 ^ (2 ^ g) ≤ N / 2 ^ (Nat.log 2 (Nat.log 2 N)) := by
  set u : ℕ := Nat.log 2 (Nat.log 2 N) with hu
  have hL : 2 ^ u ≤ Nat.log 2 N := two_pow_llLevel_le hN
  have hstep : 2 ^ g + u ≤ 2 ^ u := by
    have h1 : 2 ^ g ≤ 2 ^ (u - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : u ≤ 2 ^ (u - 1) := by
      have h := add_one_le_two_pow (u - 1)
      omega
    have h3 : 2 ^ (u - 1) + 2 ^ (u - 1) = 2 ^ u := by
      have hu1 : (u - 1) + 1 = u := by omega
      calc 2 ^ (u - 1) + 2 ^ (u - 1) = 2 ^ (u - 1) * 2 := by ring
        _ = 2 ^ ((u - 1) + 1) := by rw [pow_succ]
        _ = 2 ^ u := by rw [hu1]
    omega
  have hsum : 2 ^ g + u ≤ Nat.log 2 N := le_trans hstep hL
  rw [Nat.le_div_iff_mul_le (by positivity)]
  calc 2 ^ (2 ^ g) * 2 ^ u = 2 ^ (2 ^ g + u) := by rw [pow_add]
    _ ≤ 2 ^ (Nat.log 2 N) := Nat.pow_le_pow_right (by norm_num) hsum
    _ ≤ N := Nat.pow_log_le_self 2 (by omega)

set_option maxHeartbeats 1000000 in
/-- **The analytic step: `⌈φ(D_N)⌉ + 1 ≤ u_N` eventually.**  `φ` costs
`b^{θ D_N}·log(D_N+2+M₀) ≍ (u log u)^θ · log log u`, while the budget is `u_N` itself; the margin
is the same `u^{1-θ}` that `exponent_tendsto_atBot_of_geom_slow` runs on. -/
theorem ceil_thrPhi_depthSlow_add_one_le {b : ℕ} (hb : 2 ≤ b) (M₀ : ℕ) {κ c₀ θ : ℝ}
    (hκ : 0 < κ) (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) :
    ∀ᶠ N : ℕ in atTop,
      ⌈thrPhi b M₀ κ c₀ θ (depthSlow b N)⌉₊ + 1 ≤ Nat.log 2 (Nat.log 2 N) := by
  have hbR : (1 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hM0 : (0 : ℝ) ≤ (M₀ : ℝ) := Nat.cast_nonneg _
  set α : ℝ := 1 - θ with hαdef
  have hαpos : 0 < α := by rw [hαdef]; linarith
  set C' : ℝ := (b : ℝ) * ((M₀ : ℝ) + 3) / (κ * c₀ * Real.log 2) with hC'def
  have hden : (0 : ℝ) < κ * c₀ * Real.log 2 := by positivity
  have hdenne : κ * c₀ * Real.log 2 ≠ 0 := ne_of_gt hden
  have hC'pos : 0 < C' := by rw [hC'def]; positivity
  have huT : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N)) atTop atTop :=
    (PairDecouple.tendsto_natLog_atTop 2 le_rfl).comp
      (PairDecouple.tendsto_natLog_atTop 2 le_rfl)
  have htT : Tendsto (fun N : ℕ => Real.log ((Nat.log 2 (Nat.log 2 N) : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp huT |>.atTop_add
      tendsto_const_nhds)
  have hR := (tendsto_exp_div_polyPow hαpos 2).comp htT
  filter_upwards [huT.eventually_ge_atTop 3, hR.eventually_ge_atTop (C' + 1),
    depthSlow_le_depthLL hb] with N hu3 hRN hSL
  simp only [Function.comp_apply] at hRN
  set u : ℕ := Nat.log 2 (Nat.log 2 N) with hudef
  set y : ℝ := (u : ℝ) + 1 with hydef
  set t : ℝ := Real.log y with htdef
  set D : ℕ := depthSlow b N with hDdef
  have hu1 : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
  have hy4 : (4 : ℝ) ≤ y := by rw [hydef]; linarith
  have hypos : (0 : ℝ) < y := by linarith
  have hllp : llProxy N = y := by rw [llProxy]
  have ht0 : 0 ≤ t := by rw [htdef]; exact Real.log_nonneg (by linarith)
  have hS1 : (1 : ℝ) ≤ 2 + 2 * t := by linarith
  have hyθ : (0 : ℝ) < y ^ θ := Real.rpow_pos_of_pos hypos _
  have hyθ1 : (1 : ℝ) ≤ y ^ θ := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ y) hθ0.le
    rwa [Real.rpow_zero] at h
  -- the two schedule inputs
  have hDle : ((D : ℝ) + 1) ≤ 2 + 3 * t := by
    have h1 := depthLL_succ_le_log hb N
    rw [hllp, ← htdef] at h1
    have h2 : ((D : ℝ)) ≤ ((PairDecouple.depthLL b N : ℝ)) := by exact_mod_cast hSL
    linarith
  have hpowD : (b : ℝ) ^ D ≤ (b : ℝ) * (y * (2 + 2 * t)) := by
    have h2 := pow_depthSlow_le_log hb N
    rw [hllp, ← htdef, ← hDdef] at h2
    exact h2
  -- `b^{θ D} ≤ b · y^θ · (2+2t)`: only the `y^θ` survives, and that is the whole point
  have hrpowD : (b : ℝ) ^ (θ * (D : ℝ)) ≤ (b : ℝ) * (y ^ θ * (2 + 2 * t)) := by
    have hsplit : (b : ℝ) ^ (θ * (D : ℝ)) = ((b : ℝ) ^ D) ^ θ := by
      rw [show θ * (D : ℝ) = (D : ℝ) * θ from by ring, Real.rpow_mul hb0.le, Real.rpow_natCast]
    have h1 : ((b : ℝ) ^ D) ^ θ ≤ ((b : ℝ) * (y * (2 + 2 * t))) ^ θ :=
      Real.rpow_le_rpow (by positivity) hpowD hθ0.le
    have h2 : ((b : ℝ) * (y * (2 + 2 * t))) ^ θ
        = (b : ℝ) ^ θ * (y ^ θ * (2 + 2 * t) ^ θ) := by
      rw [Real.mul_rpow hb0.le (by positivity), Real.mul_rpow hypos.le (by linarith)]
    have h3 : (b : ℝ) ^ θ ≤ (b : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le hbR.le hθ.le
      rwa [Real.rpow_one] at this
    have h4 : (2 + 2 * t) ^ θ ≤ 2 + 2 * t := by
      have := Real.rpow_le_rpow_of_exponent_le hS1 hθ.le
      rwa [Real.rpow_one] at this
    calc (b : ℝ) ^ (θ * (D : ℝ)) = ((b : ℝ) ^ D) ^ θ := hsplit
      _ ≤ ((b : ℝ) * (y * (2 + 2 * t))) ^ θ := h1
      _ = (b : ℝ) ^ θ * (y ^ θ * (2 + 2 * t) ^ θ) := h2
      _ ≤ (b : ℝ) * (y ^ θ * (2 + 2 * t) ^ θ) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ ≤ (b : ℝ) * (y ^ θ * (2 + 2 * t)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hyθ.le) hb0.le
  -- the log factor: `log(D+2+M₀) ≤ 2 + 3t + M₀`
  have hlogDnn : (0 : ℝ) ≤ Real.log ((D : ℝ) + 2 + (M₀ : ℝ)) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
    linarith
  have hlogD : Real.log ((D : ℝ) + 2 + (M₀ : ℝ)) ≤ 2 + 3 * t + (M₀ : ℝ) := by
    have hpos : (0 : ℝ) < (D : ℝ) + 2 + (M₀ : ℝ) := by
      have : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
      linarith
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  -- the product, majorised by `C' · y^θ · (2+3t)²`
  have hprod : (2 + 2 * t) * (2 + 3 * t + (M₀ : ℝ)) ≤ ((M₀ : ℝ) + 3) * (2 + 3 * t) ^ 2 := by
    nlinarith [ht0, hM0, mul_nonneg ht0 hM0, sq_nonneg t,
      mul_nonneg (mul_nonneg hM0 ht0) ht0]
  have hA : (0 : ℝ) < (b : ℝ) * y ^ θ := by positivity
  have hnum : (b : ℝ) ^ (θ * (D : ℝ)) * Real.log ((D : ℝ) + 2 + (M₀ : ℝ))
      ≤ (b : ℝ) * ((M₀ : ℝ) + 3) * (y ^ θ * (2 + 3 * t) ^ 2) := by
    have hstep1 := mul_le_mul hrpowD hlogD hlogDnn (by positivity)
    calc (b : ℝ) ^ (θ * (D : ℝ)) * Real.log ((D : ℝ) + 2 + (M₀ : ℝ))
        ≤ ((b : ℝ) * (y ^ θ * (2 + 2 * t))) * (2 + 3 * t + (M₀ : ℝ)) := hstep1
      _ = ((b : ℝ) * y ^ θ) * ((2 + 2 * t) * (2 + 3 * t + (M₀ : ℝ))) := by ring
      _ ≤ ((b : ℝ) * y ^ θ) * (((M₀ : ℝ) + 3) * (2 + 3 * t) ^ 2) :=
          mul_le_mul_of_nonneg_left hprod hA.le
      _ = (b : ℝ) * ((M₀ : ℝ) + 3) * (y ^ θ * (2 + 3 * t) ^ 2) := by ring
  have hid : C' * (κ * c₀ * Real.log 2) = (b : ℝ) * ((M₀ : ℝ) + 3) := by
    rw [hC'def]; field_simp
  have hφle : thrPhi b M₀ κ c₀ θ D ≤ C' * (y ^ θ * (2 + 3 * t) ^ 2) := by
    rw [thrPhi, div_le_iff₀ hden]
    calc (b : ℝ) ^ (θ * (D : ℝ)) * Real.log ((D : ℝ) + 2 + (M₀ : ℝ))
        ≤ (b : ℝ) * ((M₀ : ℝ) + 3) * (y ^ θ * (2 + 3 * t) ^ 2) := hnum
      _ = C' * (κ * c₀ * Real.log 2) * (y ^ θ * (2 + 3 * t) ^ 2) := by rw [hid]
      _ = C' * (y ^ θ * (2 + 3 * t) ^ 2) * (κ * c₀ * Real.log 2) := by ring
  -- the exponential margin: `y^θ · exp(α t) = y`
  have hyα : y ^ θ * Real.exp (α * t) = y := by
    have h1 : Real.exp (α * t) = y ^ α := by
      rw [Real.rpow_def_of_pos hypos, htdef]
      congr 1
      ring
    have h2 : θ + α = 1 := by rw [hαdef]; ring
    rw [h1, ← Real.rpow_add hypos, h2, Real.rpow_one]
  have hRN' : (C' + 1) * (2 + 3 * t) ^ 2 ≤ Real.exp (α * t) := by
    have hpos : (0 : ℝ) < (2 + 3 * t) ^ 2 := by positivity
    rw [le_div_iff₀ hpos] at hRN
    linarith
  have hkey : thrPhi b M₀ κ c₀ θ D ≤ y - 2 := by
    have hmul : y ^ θ * ((C' + 1) * (2 + 3 * t) ^ 2) ≤ y ^ θ * Real.exp (α * t) :=
      mul_le_mul_of_nonneg_left hRN' hyθ.le
    rw [hyα] at hmul
    have hsq : (4 : ℝ) ≤ (2 + 3 * t) ^ 2 := by nlinarith [ht0]
    have hbig : (2 : ℝ) ≤ y ^ θ * (2 + 3 * t) ^ 2 := by nlinarith [hyθ1, hsq]
    have hexp : y ^ θ * ((C' + 1) * (2 + 3 * t) ^ 2)
        = C' * (y ^ θ * (2 + 3 * t) ^ 2) + y ^ θ * (2 + 3 * t) ^ 2 := by ring
    rw [hexp] at hmul
    linarith [hφle]
  -- conclude in ℕ
  clear_value D t y u
  have hcast : ((u - 1 : ℕ) : ℝ) = (u : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ u := by omega
    rw [Nat.cast_sub h1, Nat.cast_one]
  have hceil : ⌈thrPhi b M₀ κ c₀ θ D⌉₊ ≤ u - 1 := by
    refine Nat.ceil_le.2 ?_
    rw [hcast]
    rw [hydef] at hkey
    linarith
  omega

/-! ### The crux at `θ < 1` -/

theorem tendsto_depthSlow {b : ℕ} (hb : 2 ≤ b) :
    Tendsto (fun N : ℕ => depthSlow b N) atTop atTop := by
  have harg : Tendsto (fun N : ℕ => slowArg b N) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_) (tendsto_slowW hb)
    rw [slowArg]
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have h := (PairDecouple.tendsto_natLog_atTop b hb).comp harg
  exact tendsto_atTop_mono (fun N => Nat.le_succ _) h

set_option maxHeartbeats 1600000 in
/-- **The diagonal at any level below the SLOW schedule, from the geometric input, `θ < 1`.**
Verbatim `C3MrtUnifK.depthAvg_gen_tendsto_of_geom` with the exponent estimate swapped for
`exponent_tendsto_atBot_of_geom_slow`; nothing else in that assembly cares which schedule the
levels sit under. -/
theorem depthAvg_gen_tendsto_of_geom_slow {b Q : ℕ} (hb : 2 ≤ b) (hQ : 0 < Q) (P j : ℕ) (hh : ℤ)
    {c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (KN : ℕ → ℕ) (hKN : ∀ N, 0 < KN N)
    (hKle : ∀ᶠ N : ℕ in atTop, KN N ≤ depthSlow b N)
    (hin : ∀ K, KPointNoExcFor Pnp (cKgeom c₀ θ b) (CstKdeg m) K)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      Pnp (zOmegaNat (depthRoot b hh 0)) X L)
    (Athr : ℕ → ℕ) (hA2 : ∀ K, 2 ≤ Athr K)
    (hAthr : ∀ K : ℕ, max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log (Athr K)) ^ (κ * cKgeom c₀ θ b K))
    (hAle : ∀ᶠ N : ℕ in atTop, Athr (KN N) ≤ N / 2 ^ (Nat.log 2 (Nat.log 2 N))) :
    Tendsto (fun N : ℕ => depthAvg b P Q j hh (KN N) N) atTop (𝓝 0) := by
  have hb0 : 0 < b := by omega
  have hk₀ : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N)) atTop atTop :=
    (PairDecouple.tendsto_natLog_atTop 2 le_rfl).comp
      (PairDecouple.tendsto_natLog_atTop 2 le_rfl)
  have hbase : ∀ᶠ N : ℕ in atTop,
      0 < 2 * Real.log ((N / 2 ^ (Nat.log 2 (Nat.log 2 N)) : ℕ) : ℝ) := by
    filter_upwards [tendsto_cut_atTop.eventually_ge_atTop 2] with N hN
    have h2 : (2 : ℝ) ≤ ((N / 2 ^ (Nat.log 2 (Nat.log 2 N)) : ℕ) : ℝ) := by exact_mod_cast hN
    have hlog : 0 < Real.log ((N / 2 ^ (Nat.log 2 (Nat.log 2 N)) : ℕ) : ℝ) :=
      Real.log_pos (by linarith)
    linarith
  have hrate := rate_tendsto_of_exponent (cK := cKgeom c₀ θ b) (CstK := CstKdeg m)
    (fun K => CstKdeg_pos m K) (κ := κ) (M₀ := Q * primorial P) KN
    (fun N => N / 2 ^ (Nat.log 2 (Nat.log 2 N))) hbase
    (exponent_tendsto_atBot_of_geom_slow hb hc₀ hθ0 hθ hκ m KN hKle)
  have hΦ := windowPhi_diag_tendsto (cK := cKgeom c₀ θ b) (CstK := CstKdeg m) (κ := κ)
    (M₀ := Q * primorial P) KN (fun N => Athr (KN N))
    (fun N => N / 2 ^ (Nat.log 2 (Nat.log 2 N)))
    (fun N => hA2 _) (fun K => (CstKdeg_pos m K).le) hAle hrate
  have hhalf : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ (Nat.log 2 (Nat.log 2 N))) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hk₀
  refine depthAvg_gen_tendsto_of_unif hQ P j hh (fun K => cKgeom_pos hc₀ hb0 K)
    (fun K => CstKdeg_pos m K) KN hKN hin hκ hκ1 hnp Athr hA2 hAthr
    (fun N => Nat.log 2 (Nat.log 2 N)) ?_
  simpa using hΦ.add hhalf

/-- **The divisible twist level, for an ARBITRARY divergent schedule.**  Schedule-generic form of
`C3MrtUnifK.depthAvg_dvd_tendsto_of_primitive`, whose proof only ever used that the schedule
eventually exceeds `v`. -/
theorem depthAvg_dvd_tendsto_of_primitive_sched {b : ℕ} (hb : 2 ≤ b) (P Q j : ℕ) (h' : ℤ) (v : ℕ)
    (Dsch : ℕ → ℕ) (hD : Tendsto Dsch atTop atTop)
    (hprim : Tendsto (fun N : ℕ => depthAvg b P Q j h' (Dsch N - v) N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => depthAvg b P Q j ((b : ℤ) ^ v * h') (Dsch N) N) atTop (𝓝 0) := by
  have hb0 : 0 < b := by omega
  have hshift : Tendsto (fun N : ℕ => 2 * (v : ℝ) / N) atTop (𝓝 0) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul (2 * (v : ℝ))
    rw [mul_zero] at this
    exact this.congr fun N => by ring
  have hmaj : Tendsto (fun N : ℕ =>
      ‖depthAvg b P Q j h' (Dsch N - v) N‖ + 2 * (v : ℝ) / N) atTop (𝓝 0) := by
    simpa using hprim.norm.add hshift
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hD.eventually_ge_atTop v] with N hN
  exact norm_depthAvg_dvd_le hb0 P Q j h' hN N

/-! ### The threshold data, on the slow schedule

`C3MrtUnifK.KPointThresholdOKWith` asks for the threshold to be passed for every level
`K ≤ depthLL b N`.  The slow schedule only ever uses levels `K ≤ depthSlow b N`, so it needs
strictly less; and — unlike the `depthLL` version at `θ > 1/2` — the weaker demand is one the
geometric profile can actually MEET.  See `kPointThresholdSlow_of_geom`. -/

/-- The threshold data, demanded only up to the SLOW schedule's levels. -/
def KPointThresholdSlow (b Q P : ℕ) (cK : ℕ → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ ≤ 1 → ∃ Athr : ℕ → ℕ, (∀ K, 2 ≤ Athr K) ∧
    (∀ K : ℕ, max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log (Athr K)) ^ (κ * cK K)) ∧
    (∀ᶠ N : ℕ in atTop, ∀ K : ℕ, K ≤ depthSlow b N →
        Athr K ≤ N / 2 ^ (Nat.log 2 (Nat.log 2 N)))

/-- Nothing is lost: the `depthLL` threshold data implies the slow one. -/
theorem kPointThresholdSlow_of_with {b Q P : ℕ} (hb : 2 ≤ b) {cK : ℕ → ℝ}
    (h : KPointThresholdOKWith b Q P cK) : KPointThresholdSlow b Q P cK := by
  intro κ hκ hκ1
  obtain ⟨Athr, hA2, hAthr, hAcut⟩ := h κ hκ hκ1
  refine ⟨Athr, hA2, hAthr, ?_⟩
  filter_upwards [hAcut, depthSlow_le_depthLL hb] with N hcut hSL K hK
  exact hcut K (le_trans hK hSL)

/-- **THE THRESHOLD DATA IS A THEOREM.**  For the geometric profile `c_K = c₀ b^{-θK}` with
`θ < 1`, the threshold demanded by the slow schedule can be CONSTRUCTED:
`Athr K = 2^(2^⌈φ K⌉)` with `φ K = b^{θK}·log(K+2+M₀)/(κ c₀ log 2)`.

Clause (ii) holds by design (`thrAthr_rpow_ge`); clause (iii) — the cut
`Athr(D_N) ≤ N/2^{u_N}` — is `ceil_thrPhi_depthSlow_add_one_le` plus `two_pow_two_pow_le_cut`,
and it is exactly where `θ < 1` is spent a second time: the demand
`log log Athr(D_N) ≍ (u log u)^θ log log u` must sit inside the budget `log log a_N ≍ u log 2`.

So `weylLambertTwist_of_geom_slow`'s second hypothesis is not an assumption: the crux rests on
the `K`-point correlation input ALONE. -/
theorem kPointThresholdSlow_of_geom {b : ℕ} (hb : 2 ≤ b) (Q P : ℕ) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) : KPointThresholdSlow b Q P (cKgeom c₀ θ b) := by
  intro κ hκ hκ1
  refine ⟨thrAthr b (Q * primorial P) κ c₀ θ, two_le_thrAthr b (Q * primorial P) κ c₀ θ,
    fun K => thrAthr_rpow_ge hb hκ hc₀ K, ?_⟩
  filter_upwards [ceil_thrPhi_depthSlow_add_one_le hb (Q * primorial P) hκ hc₀ hθ0 hθ,
    Filter.eventually_ge_atTop 2] with N hceil hN K hK
  refine le_trans (thrAthr_monotone hb hκ hc₀ hθ0 hK) ?_
  rw [thrAthr]
  exact two_pow_two_pow_le_cut hN hceil

/-- The diagonal obligation, on the SLOW schedule. -/
def DepthDiagonalSlow (b : ℕ) : Prop :=
  ∀ (P Q j : ℕ) (h : ℤ), 0 < Q → 0 < j → j < Q →
    Tendsto (fun N : ℕ => depthAvg b P Q j h (depthSlow b N) N) atTop (𝓝 0)

/-- **The crux from the slow diagonal.**  `weylLambertTwist_of_schedule` is parametric in the
schedule, so the slow schedule plugs straight in: `eventually_depthSlow_add_le` for
admissibility, `tendsto_LLbound_div_pow_depthSlow` for the mean-phase discard. -/
theorem weylLambertTwist_of_depthDiagonalSlow {b : ℕ} (hb : 3 ≤ b) (H : DepthDiagonalSlow b) :
    WeylLambertTwist b :=
  weylLambertTwist_of_schedule hb (depthSlow b)
    (eventually_depthSlow_add_le (by omega) 3)
    (tendsto_LLbound_div_pow_depthSlow (by omega)) H

/-! ### The archimedean certificate as a PARAMETER too

`depthDiagonalSlow_of_geom` is the one place the chain *instantiates* the non-pretentiousness
hypothesis (at `Pnp = TTNonPretentious`, via `ttNonPretentious_zOmegaNat`).  Lap 102 showed that
instance is vacuous, so the instantiation is named here as `ArchSupply Pnp b` and the chain is
restated over it.  For the faithful `Pnp = TTNonPretentiousAt A` (`C3MrtTTDefect`), supplying
`ArchSupply` is precisely the open archimedean obligation — characters `q > 1` and twists up to
`X²`; nothing else in the chain changes. -/

/-- **The archimedean certificate, abstracted.**  For every primitive twist `h'` there is an
exponent `κ ∈ (0, 1]` on which the non-pretentiousness hypothesis `Pnp` holds for
`zOmegaNat (depthRoot b h' 0)` throughout `1 ≤ L ≤ (log X)^κ`. -/
def ArchSupply (Pnp : (ℕ → ℂ) → ℝ → ℝ → Prop) (b : ℕ) : Prop :=
  ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') → ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
    ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      Pnp (zOmegaNat (depthRoot b h' 0)) X L

/-- The old certificate, in the abstracted shape: unconditional, with `κ = ttExponent`.  It is
also (lap 102) *content-free*, since `TTNonPretentious` is provable outright. -/
theorem archSupply_tt {b : ℕ} (hb0 : 0 < b) : ArchSupply TTNonPretentious b := by
  intro h' hnd
  have hznorm : ‖depthRoot b h' 0‖ = 1 := norm_ee_real _
  have hz1 : depthRoot b h' 0 ≠ 1 := depthRoot_ne_one_of_not_dvd hb0 hnd
  exact ⟨ttExponent (depthRoot b h' 0), ttExponent_pos hznorm hz1,
    ttExponent_le_one hznorm, ttNonPretentious_zOmegaNat hznorm hz1 le_rfl⟩

/-- **`DepthDiagonalSlow b` from the geometric input, over an ABSTRACT archimedean hypothesis.**
`depthDiagonalSlow_of_geom` is the `Pnp = TTNonPretentious` instance. -/
theorem depthDiagonalSlow_of_geom_for {b : ℕ} (hb : 2 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ K, KPointNoExcFor Pnp (cKgeom c₀ θ b) (CstKdeg m) K)
    (hsup : ArchSupply Pnp b)
    (hthr : ∀ P Q : ℕ, 0 < Q → KPointThresholdSlow b Q P (cKgeom c₀ θ b)) :
    DepthDiagonalSlow b := by
  intro P Q j hh hQ hj0 hjQ
  have hb0 : 0 < b := by omega
  rcases eq_or_ne hh 0 with rfl | hne
  · exact depthAvg_zero_tendsto b P Q j hj0 hjQ
  obtain ⟨v, h', hfac, hnd⟩ := exists_pow_mul_not_dvd hb hh hne
  subst hfac
  obtain ⟨κ, hκ, hκ1, hnp⟩ := hsup h' hnd
  obtain ⟨Athr, hA2, hAthr, hAcut⟩ := hthr P Q hQ κ hκ hκ1
  set KN : ℕ → ℕ := fun N => max 1 (depthSlow b N - v) with hKNdef
  have hKN : ∀ N, 0 < KN N := fun N => lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hvN := (tendsto_depthSlow hb).eventually_ge_atTop (v + 1)
  have hKle : ∀ᶠ N : ℕ in atTop, KN N ≤ depthSlow b N := by
    filter_upwards [hvN] with N hN
    rw [hKNdef]; simp only; omega
  have hKeq : ∀ᶠ N : ℕ in atTop, KN N = depthSlow b N - v := by
    filter_upwards [hvN] with N hN
    rw [hKNdef]; simp only; omega
  have hAle : ∀ᶠ N : ℕ in atTop,
      Athr (KN N) ≤ N / 2 ^ (Nat.log 2 (Nat.log 2 N)) := by
    filter_upwards [hAcut, hKle] with N hcut hle
    exact hcut _ hle
  have hgen := depthAvg_gen_tendsto_of_geom_slow hb hQ P j h' hc₀ hθ0 hθ m KN hKN hKle hin
    hκ hκ1 hnp Athr hA2 hAthr hAle
  have hprim : Tendsto (fun N : ℕ =>
      depthAvg b P Q j h' (depthSlow b N - v) N) atTop (𝓝 0) := by
    refine hgen.congr' ?_
    filter_upwards [hKeq] with N hN
    rw [hN]
  exact depthAvg_dvd_tendsto_of_primitive_sched hb P Q j h' v (depthSlow b)
    (tendsto_depthSlow hb) hprim

/-- **THE C3 CRUX, over an abstract archimedean hypothesis.** -/
theorem weylLambertTwist_of_geom_slow_for {b : ℕ} (hb : 3 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ K, KPointNoExcFor Pnp (cKgeom c₀ θ b) (CstKdeg m) K)
    (hsup : ArchSupply Pnp b)
    (hthr : ∀ P Q : ℕ, 0 < Q → KPointThresholdSlow b Q P (cKgeom c₀ θ b)) :
    WeylLambertTwist b :=
  weylLambertTwist_of_depthDiagonalSlow hb
    (depthDiagonalSlow_of_geom_for (by omega) hc₀ hθ0 hθ m hin hsup hthr)

/-- **THE C3 CRUX FROM THE ABSTRACT INPUT ALONE** — the threshold data is discharged. -/
theorem weylLambertTwist_of_geom_input_for {b : ℕ} (hb : 3 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ K, KPointNoExcFor Pnp (cKgeom c₀ θ b) (CstKdeg m) K)
    (hsup : ArchSupply Pnp b) :
    WeylLambertTwist b :=
  weylLambertTwist_of_geom_slow_for hb hc₀ hθ0 hθ m hin hsup
    fun P Q _ => kPointThresholdSlow_of_geom (by omega) Q P hc₀ hθ0 hθ

/-- **`ConjC3` FROM THE ABSTRACT `K`-POINT INPUT + ARCHIMEDEAN SUPPLY.**  The headline in the
shape lap 102 forces: two named inputs, neither of them vacuous by construction. -/
theorem conjC3_of_geom_input_for {c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ b : ℕ, 3 ≤ b → ∀ K, KPointNoExcFor Pnp (cKgeom c₀ θ b) (CstKdeg m) K)
    (hsup : ∀ b : ℕ, 3 ≤ b → ArchSupply Pnp b) :
    ConjC3 :=
  conjC3_of_weylLambertTwist fun b hb =>
    weylLambertTwist_of_geom_input_for hb hc₀ hθ0 hθ m (hin b hb) (hsup b hb)

/-- **`DepthDiagonalSlow b` FROM THE GEOMETRICALLY DEGRADING INPUT AT `θ < 1`.**  All twist
levels, exactly as in `C3MrtUnifK.depthDiagonal_of_geom`. -/
theorem depthDiagonalSlow_of_geom {b : ℕ} (hb : 2 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ K, KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) K)
    (hthr : ∀ P Q : ℕ, 0 < Q → KPointThresholdSlow b Q P (cKgeom c₀ θ b)) :
    DepthDiagonalSlow b :=
  depthDiagonalSlow_of_geom_for hb hc₀ hθ0 hθ m (fun K => kPointNoExcFor_of_with (hin K))
    (archSupply_tt (by omega)) hthr

/-- **THE C3 CRUX FROM THE GEOMETRIC `K`-POINT INPUT, `θ < 1`.**  This supersedes
`C3MrtUnifK.weylLambertTwist_of_geom`: the admissible decay rate for the `K`-point saving is
widened from `θ < 1/2` to `θ < 1` — i.e. the input may lose a full factor `b^{-1}` per extra
correlation point, near the `V^{-0.49J'}` shape TT Thm 3.3 actually produces — at the cost of
slowing the depth schedule to `b^{D_N} ≍ log log N · log log log N`, which is the minimum the
mean-phase discard permits. -/
theorem weylLambertTwist_of_geom_slow {b : ℕ} (hb : 3 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ K, KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) K)
    (hthr : ∀ P Q : ℕ, 0 < Q → KPointThresholdSlow b Q P (cKgeom c₀ θ b)) :
    WeylLambertTwist b :=
  weylLambertTwist_of_depthDiagonalSlow hb
    (depthDiagonalSlow_of_geom (by omega) hc₀ hθ0 hθ m hin hthr)

/-- The lap-89 form, recovered through the bridge: the `depthLL` threshold data still suffices. -/
theorem weylLambertTwist_of_geom_slow_of_with {b : ℕ} (hb : 3 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ K, KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) K)
    (hthr : ∀ P Q : ℕ, 0 < Q → KPointThresholdOKWith b Q P (cKgeom c₀ θ b)) :
    WeylLambertTwist b :=
  weylLambertTwist_of_geom_slow hb hc₀ hθ0 hθ m hin
    fun P Q hQ => kPointThresholdSlow_of_with (by omega) (hthr P Q hQ)

/-- …and hence `ConjC3`, base by base. -/
theorem conjC3_of_geom_slow {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ b : ℕ, 3 ≤ b → ∀ K, KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) K)
    (hthr : ∀ b : ℕ, 3 ≤ b → ∀ P Q : ℕ, 0 < Q →
      KPointThresholdSlow b Q P (cKgeom c₀ θ b)) :
    ConjC3 :=
  conjC3_of_weylLambertTwist fun b hb =>
    weylLambertTwist_of_geom_slow hb hc₀ hθ0 hθ m (hin b hb) (hthr b hb)

/-- **THE C3 CRUX FROM THE `K`-POINT INPUT ALONE.**  No threshold hypothesis: it is discharged
by `kPointThresholdSlow_of_geom`.  Everything the crux still needs is the one open analytic
statement `KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) K`. -/
theorem weylLambertTwist_of_geom_input {b : ℕ} (hb : 3 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ K, KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) K) :
    WeylLambertTwist b :=
  weylLambertTwist_of_geom_slow hb hc₀ hθ0 hθ m hin
    fun P Q _ => kPointThresholdSlow_of_geom (by omega) Q P hc₀ hθ0 hθ

/-- **`ConjC3` FROM THE `K`-POINT INPUT ALONE**, for every geometric decay rate `θ < 1`. -/
theorem conjC3_of_geom_input {c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ b : ℕ, 3 ≤ b → ∀ K, KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) K) :
    ConjC3 :=
  conjC3_of_weylLambertTwist fun b hb =>
    weylLambertTwist_of_geom_input hb hc₀ hθ0 hθ m (hin b hb)

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
#print axioms NormalNumbers.CastingOut.tendsto_polyPow_sub_expDiv
#print axioms NormalNumbers.CastingOut.exponent_tendsto_atBot_of_geom_slow
#print axioms NormalNumbers.CastingOut.two_le_thrAthr
#print axioms NormalNumbers.CastingOut.pow_ceil_le_two_log_thrAthr
#print axioms NormalNumbers.CastingOut.thrPhi_monotone
#print axioms NormalNumbers.CastingOut.thrAthr_monotone
#print axioms NormalNumbers.CastingOut.thrAthr_rpow_ge
#print axioms NormalNumbers.CastingOut.tendsto_depthSlow
#print axioms NormalNumbers.CastingOut.depthAvg_dvd_tendsto_of_primitive_sched
#print axioms NormalNumbers.CastingOut.depthAvg_gen_tendsto_of_geom_slow
#print axioms NormalNumbers.CastingOut.weylLambertTwist_of_depthDiagonalSlow
#print axioms NormalNumbers.CastingOut.kPointThresholdSlow_of_with
#print axioms NormalNumbers.CastingOut.depthDiagonalSlow_of_geom
#print axioms NormalNumbers.CastingOut.weylLambertTwist_of_geom_slow
#print axioms NormalNumbers.CastingOut.weylLambertTwist_of_geom_slow_of_with
#print axioms NormalNumbers.CastingOut.conjC3_of_geom_slow
#print axioms NormalNumbers.CastingOut.add_one_le_two_pow
#print axioms NormalNumbers.CastingOut.two_pow_two_pow_le_cut
#print axioms NormalNumbers.CastingOut.ceil_thrPhi_depthSlow_add_one_le
#print axioms NormalNumbers.CastingOut.kPointThresholdSlow_of_geom
#print axioms NormalNumbers.CastingOut.weylLambertTwist_of_geom_input
#print axioms NormalNumbers.CastingOut.conjC3_of_geom_input

end CastingOut

end NormalNumbers
