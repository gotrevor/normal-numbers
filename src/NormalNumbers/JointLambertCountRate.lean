/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertCountMarkov
import NormalNumbers.JointLambertCountCandidates

/-!
# The final rate: why the answer is `(log log N)² log log log N`

§5 of `docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md` converts a count of at least
`X / (8 B log X)` at the height `X = ⌊N/D_N⌋` into the bound
`N exp(-C (log log N)² log log log N)`.  All of that conversion is one inequality:

    log D_N + log B + log(8 log X) + O(1) ≤ C (log log N)² log log log N,

with `D_N = 2(2k³)^(a-1)`, `B ≤ (2k³)^(1 + c k²)` and `k = countK N ≤ 6 log log N`.

`eventually_rate_le` is that inequality.  This is the **only** place where the sharp
`k² log k` size of the modulus is used — `eventually_schedule_feasible` deliberately spent
the cruder `k³`, which was free there but would give the weaker `(log log N)³` here.  The
exponent `2` on `log log N` comes from `k²`, and the single `log log log N` comes from
`log k`; that is exactly the gain of drawing the congruence primes from `(k³, 2k³)` instead
of from near `(log X)²`.
-/

namespace NormalNumbers.JointLambert

open Filter

/-- **The rate inequality of §5.**  For fixed `c, a` there are `C > 0` and `N₀` such that
for every `N ≥ N₀`, with `k = countK N`,

    (1 + c k² + a) · log(2k³) + log(8 log N) + 2 ≤ C (log log N)² log log log N.

The left side dominates `log B + log D_N + log(8 log X) + O(1)`; the right side is the
exponent of the ratified count. -/
theorem eventually_rate_le (c a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ((1 : ℝ) + (c : ℝ) * (countK N : ℝ) ^ 2 + (a : ℝ))
            * Real.log (2 * (countK N : ℝ) ^ 3)
          + Real.log (8 * Real.log (N : ℝ)) + 2
        ≤ C * (Real.log (Real.log (N : ℝ))) ^ 2
            * Real.log (Real.log (Real.log (N : ℝ))) := by
  refine ⟨360 * (1 + (c : ℝ) + (a : ℝ)) + 6, by positivity, ?_⟩
  -- `μ = log log N ≥ 20` eventually, hence `ν = log μ ≥ 1`
  have htend2 : Filter.Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    ((htend2.eventually_ge_atTop (20 : ℝ)).and eventually_countK_le)
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hμ20, hk1, hkle⟩ := hN0 N hN
  set k : ℕ := countK N with hkdef
  set μ : ℝ := Real.log (Real.log (N : ℝ)) with hμdef
  set ν : ℝ := Real.log μ with hνdef
  have hμ1 : (1 : ℝ) ≤ μ := by linarith
  have hν1 : (1 : ℝ) ≤ ν := by
    have he : Real.exp 1 ≤ 20 := Real.exp_one_lt_d9.le.trans (by norm_num)
    calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log 20 := Real.log_le_log (Real.exp_pos 1) he
      _ ≤ ν := by rw [hνdef]; exact Real.log_le_log (by norm_num) hμ20
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  -- `log(2k³) ≤ 10 ν`
  have hlog6 : Real.log 6 ≤ 2 := by
    have h6 : (6 : ℝ) ≤ Real.exp 2 := by
      have h27 : (2.7 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
      have : Real.exp 1 * Real.exp 1 ≤ Real.exp 2 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1:ℝ)]
    calc Real.log 6 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h6
      _ = 2 := Real.log_exp 2
  have hlogk : Real.log (k : ℝ) ≤ 2 + ν := by
    have h1 : Real.log (k : ℝ) ≤ Real.log (6 * μ) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (6 * μ) = Real.log 6 + ν := by
      rw [Real.log_mul (by norm_num) (by linarith), hνdef]
    linarith
  have hlog2k3 : Real.log (2 * (k : ℝ) ^ 3) ≤ 10 * ν := by
    have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have h3 : Real.log ((k : ℝ) ^ 3) = 3 * Real.log (k : ℝ) := by
      rw [Real.log_pow]; push_cast; ring
    rw [Real.log_mul (by norm_num) (by positivity), h3]
    linarith
  have hlog2k3nn : (0 : ℝ) ≤ Real.log (2 * (k : ℝ) ^ 3) := by
    refine Real.log_nonneg ?_
    have h3 : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hkR
    linarith
  -- `1 + c k² + a ≤ 36 (1 + c + a) μ²`
  have hksq : (k : ℝ) ^ 2 ≤ 36 * μ ^ 2 := by
    have h := pow_le_pow_left₀ (show (0:ℝ) ≤ (k:ℝ) by linarith) hkle 2
    calc (k : ℝ) ^ 2 ≤ (6 * μ) ^ 2 := h
      _ = 36 * μ ^ 2 := by ring
  have hcoef : (1 : ℝ) + (c : ℝ) * (k : ℝ) ^ 2 + (a : ℝ)
      ≤ 36 * (1 + (c : ℝ) + (a : ℝ)) * μ ^ 2 := by
    have hμsq : (1 : ℝ) ≤ μ ^ 2 := by nlinarith [hμ1]
    nlinarith [hksq, hμsq, Nat.cast_nonneg (α := ℝ) c, Nat.cast_nonneg (α := ℝ) a]
  -- `log(8 log N) ≤ 4 μ`
  have hlogN : Real.log (8 * Real.log (N : ℝ)) ≤ 4 * μ := by
    have hlN : (0 : ℝ) < Real.log (N : ℝ) := by
      have hlNnn : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
      rcases le_or_gt (Real.log (N : ℝ)) 1 with h | h
      · exfalso
        have hz : μ ≤ 0 := by rw [hμdef]; exact Real.log_nonpos hlNnn h
        linarith
      · linarith
    have h8 : Real.log 8 ≤ 3 := by
      have h3 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      rw [h3]; linarith
    rw [Real.log_mul (by norm_num) (ne_of_gt hlN)]
    rw [← hμdef]
    linarith
  -- assemble
  have hμ2ν : (1 : ℝ) ≤ μ ^ 2 * ν := by nlinarith [hμ1, hν1]
  have hmain : ((1 : ℝ) + (c : ℝ) * (k : ℝ) ^ 2 + (a : ℝ)) * Real.log (2 * (k : ℝ) ^ 3)
      ≤ 360 * (1 + (c : ℝ) + (a : ℝ)) * (μ ^ 2 * ν) := by
    calc ((1 : ℝ) + (c : ℝ) * (k : ℝ) ^ 2 + (a : ℝ)) * Real.log (2 * (k : ℝ) ^ 3)
        ≤ (36 * (1 + (c : ℝ) + (a : ℝ)) * μ ^ 2) * (10 * ν) := by
          refine mul_le_mul hcoef hlog2k3 hlog2k3nn (by positivity)
      _ = 360 * (1 + (c : ℝ) + (a : ℝ)) * (μ ^ 2 * ν) := by ring
  have hrest : Real.log (8 * Real.log (N : ℝ)) + 2 ≤ 6 * (μ ^ 2 * ν) := by
    have hμμ2ν : μ ≤ μ ^ 2 * ν := by nlinarith [hμ1, hν1]
    linarith [hlogN, hμ2ν, hμμ2ν]
  have hgoal : ((1 : ℝ) + (c : ℝ) * (k : ℝ) ^ 2 + (a : ℝ)) * Real.log (2 * (k : ℝ) ^ 3)
      + Real.log (8 * Real.log (N : ℝ)) + 2
      ≤ (360 * (1 + (c : ℝ) + (a : ℝ)) + 6) * (μ ^ 2 * ν) := by
    nlinarith [hmain, hrest]
  calc ((1 : ℝ) + (c : ℝ) * (k : ℝ) ^ 2 + (a : ℝ)) * Real.log (2 * (k : ℝ) ^ 3)
        + Real.log (8 * Real.log (N : ℝ)) + 2
      ≤ (360 * (1 + (c : ℝ) + (a : ℝ)) + 6) * (μ ^ 2 * ν) := hgoal
    _ = (360 * (1 + (c : ℝ) + (a : ℝ)) + 6) * μ ^ 2 * ν := by ring


/-! ### The two tail-cost limits of §4

After dividing the three-range tail bound by the candidate scale `M / log X`, the near cost
is `O((log X)² 2^{-k})` and the middle cost is `O((log X)²(a+1)(c+1)^{k²}2^{-k³})`.  Both
tend to `0`, and both reduce to the single inequality `(log X)^4 ≤ 2^{countK X}`, which is
the *definition* of `k = ⌈4 log₂ log X⌉` read backwards. -/

/-- `(log X)^4 ≤ 2^k` — the defining property of `k = ⌈4 log₂ log X⌉`. -/
theorem pow_two_countK_ge {X : ℕ} (hX : 1 ≤ Real.log (X : ℝ)) :
    (Real.log (X : ℝ)) ^ 4 ≤ (2 : ℝ) ^ (countK X) := by
  set L : ℝ := Real.log (X : ℝ) with hLdef
  have hL0 : (0 : ℝ) < L := by linarith
  have hceil : 4 * Real.logb 2 L ≤ ((countK X : ℕ) : ℝ) := Nat.le_ceil _
  have hrw : (2 : ℝ) ^ (countK X) = (2 : ℝ) ^ (((countK X : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (2 : ℝ) (countK X)]
  rw [hrw]
  have hstep : (2 : ℝ) ^ (4 * Real.logb 2 L) ≤ (2 : ℝ) ^ (((countK X : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2) |>.mpr hceil
  refine le_trans (le_of_eq ?_) hstep
  have hval : (2 : ℝ) ^ (Real.logb 2 L) = L := Real.rpow_logb (by norm_num) (by norm_num) hL0
  calc L ^ 4 = ((2 : ℝ) ^ (Real.logb 2 L)) ^ (4 : ℕ) := by rw [hval]
    _ = (2 : ℝ) ^ (Real.logb 2 L * (4 : ℕ)) := by
        rw [← Real.rpow_natCast ((2:ℝ) ^ (Real.logb 2 L)) 4, ← Real.rpow_mul (by norm_num)]
    _ = (2 : ℝ) ^ (4 * Real.logb 2 L) := by rw [show Real.logb 2 L * ((4:ℕ):ℝ)
          = 4 * Real.logb 2 L by push_cast; ring]

/-- **The near cost vanishes.**  `(log X)² (1/2)^k ≤ 1/(log X)²`, hence `→ 0`. -/
theorem eventually_near_cost_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, (Real.log (X : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ (countK X) ≤ ε := by
  have htend : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbig : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) ∧ 1 / ε ≤ (Real.log (X : ℝ)) ^ 2 := by
    have h1 := htend.eventually_ge_atTop (1 : ℝ)
    have h2 := htend.eventually_ge_atTop (Real.sqrt (1 / ε) + 1)
    filter_upwards [h1, h2] with X hX1 hX2
    refine ⟨hX1, ?_⟩
    have hs : Real.sqrt (1 / ε) ≤ Real.log (X : ℝ) := by linarith
    have := Real.sq_sqrt (show (0:ℝ) ≤ 1 / ε by positivity)
    nlinarith [Real.sqrt_nonneg (1 / ε), hs]
  filter_upwards [hbig] with X hX
  obtain ⟨hX1, hXε⟩ := hX
  have hpow := pow_two_countK_ge (X := X) hX1
  have hL0 : (0 : ℝ) < Real.log (X : ℝ) := by linarith
  have hhalf : (1 / 2 : ℝ) ^ (countK X) = 1 / (2 : ℝ) ^ (countK X) := by
    rw [div_pow, one_pow]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (countK X) := by positivity
  rw [hhalf]
  rw [mul_one_div, div_le_iff₀ h2pos]
  have hsq : (0 : ℝ) < (Real.log (X : ℝ)) ^ 2 := by positivity
  calc (Real.log (X : ℝ)) ^ 2 ≤ ε * (Real.log (X : ℝ)) ^ 4 := by
        rw [show (Real.log (X:ℝ)) ^ 4 = (Real.log (X:ℝ)) ^ 2 * (Real.log (X:ℝ)) ^ 2 by ring]
        have := mul_le_mul_of_nonneg_left hXε (le_of_lt hsq)
        rw [mul_one_div] at this
        rw [div_le_iff₀ hε] at hXε
        nlinarith [hXε, hsq]
    _ ≤ ε * (2 : ℝ) ^ (countK X) := mul_le_mul_of_nonneg_left hpow hε.le

/-- `countK X → ∞`: for every `m` eventually `m ≤ countK X`. -/
theorem eventually_countK_ge (m : ℕ) : ∀ᶠ X : ℕ in atTop, m ≤ countK X := by
  have htend2 : Filter.Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hl2 : (0 : ℝ) < 4 / Real.log 2 := by
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have htendk : Filter.Tendsto
      (fun N : ℕ => 4 * Real.logb 2 (Real.log (N : ℝ))) atTop atTop := by
    have h := Filter.Tendsto.const_mul_atTop hl2 htend2
    refine h.congr fun N => ?_
    rw [Real.logb]
    ring
  filter_upwards [htendk.eventually_ge_atTop ((m : ℝ))] with X hX
  have hle : ((m : ℕ) : ℝ) ≤ ((countK X : ℕ) : ℝ) := le_trans hX (Nat.le_ceil _)
  exact_mod_cast hle

/-- **The middle cost vanishes.**  `(c+1)^{k²}(1/2)^{k³} ≤ (1/2)^{k}` once `2(c+1) ≤ 2^k`,
so the middle cost is dominated by `(a+1)` times the near cost.  This is the inequality in
which the cube of the pool beats the square of the divisor count. -/
theorem eventually_middle_cost_small (a c : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      (Real.log (X : ℝ)) ^ 2 * (((a : ℝ) + 1) * ((c : ℝ) + 1) ^ ((countK X) ^ 2)
        * (1 / 2 : ℝ) ^ ((countK X) ^ 3)) ≤ ε := by
  have haε : (0 : ℝ) < ε / ((a : ℝ) + 1) := by positivity
  filter_upwards [eventually_near_cost_small haε, eventually_countK_ge (2 * (c + 1)),
    eventually_countK_ge 1] with X hnear hcpool hk1
  set k : ℕ := countK X with hkdef
  -- `2(c+1) ≤ k ≤ 2^k`, so `(c+1)(1/2)^k ≤ 1/2`
  have hkpow : (2 : ℝ) * ((c : ℝ) + 1) ≤ (2 : ℝ) ^ k := by
    have h1 : ((2 * (c + 1) : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hcpool
    have h2 : (k : ℝ) ≤ (2 : ℝ) ^ k := by
      have : (k : ℕ) ≤ 2 ^ k := Nat.lt_two_pow_self.le
      exact_mod_cast this
    push_cast at h1
    linarith
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hhalf : ((c : ℝ) + 1) * (1 / 2 : ℝ) ^ k ≤ 1 / 2 := by
    rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ h2k (by norm_num)]
    linarith
  -- `(c+1)^{k²}(1/2)^{k³} = ((c+1)(1/2)^k)^{k²} ≤ (1/2)^{k²} ≤ (1/2)^k`
  have hid : ((c : ℝ) + 1) ^ (k ^ 2) * (1 / 2 : ℝ) ^ (k ^ 3)
      = (((c : ℝ) + 1) * (1 / 2 : ℝ) ^ k) ^ (k ^ 2) := by
    rw [mul_pow, ← pow_mul, show k * k ^ 2 = k ^ 3 by ring]
  have hstep1 : (((c : ℝ) + 1) * (1 / 2 : ℝ) ^ k) ^ (k ^ 2) ≤ (1 / 2 : ℝ) ^ (k ^ 2) :=
    pow_le_pow_left₀ (by positivity) hhalf _
  have hstep2 : (1 / 2 : ℝ) ^ (k ^ 2) ≤ (1 / 2 : ℝ) ^ k := by
    refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
    calc k = k ^ 1 := (pow_one k).symm
      _ ≤ k ^ 2 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hcombine : ((c : ℝ) + 1) ^ (k ^ 2) * (1 / 2 : ℝ) ^ (k ^ 3) ≤ (1 / 2 : ℝ) ^ k := by
    rw [hid]; exact le_trans hstep1 hstep2
  have hLsq : (0 : ℝ) ≤ (Real.log (X : ℝ)) ^ 2 := by positivity
  have hapos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  calc (Real.log (X : ℝ)) ^ 2 * (((a : ℝ) + 1) * ((c : ℝ) + 1) ^ (k ^ 2)
          * (1 / 2 : ℝ) ^ (k ^ 3))
      = ((a : ℝ) + 1) * ((Real.log (X : ℝ)) ^ 2
          * (((c : ℝ) + 1) ^ (k ^ 2) * (1 / 2 : ℝ) ^ (k ^ 3))) := by ring
    _ ≤ ((a : ℝ) + 1) * ((Real.log (X : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ hapos.le
        exact mul_le_mul_of_nonneg_left hcombine hLsq
    _ ≤ ((a : ℝ) + 1) * (ε / ((a : ℝ) + 1)) := mul_le_mul_of_nonneg_left hnear hapos.le
    _ = ε := by field_simp

end NormalNumbers.JointLambert
