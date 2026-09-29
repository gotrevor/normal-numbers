/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertCountPrimes

/-!
# The small-pool schedule is feasible at every large height

`exists_prime_supply_every_height` leaves the caller two inequalities in `B` and `X`:

* `(B : ℝ) ^ 3 ≤ X`;
* `C · B · log X · exp(-(η/2)√log X) ≤ 2/5`.

Here they are discharged for the schedule of `docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md` §3:

    k = countK X = ⌈4 log₂ log X⌉,   L = k³,   B ≤ (2k³)^(1 + c k²).

The mechanism is the one the note asserts, and it is *not* delicate: `k = O(log log X)`, so
`log B = O_c(k³) = O_c((log log X)³)`, and `(log log X)³ = o(√log X)`.  Cubing `k` and
bounding `log k ≤ k` is deliberately wasteful — the true size is `O_c(k² log k)` — because
the crude bound already clears the Siegel–Walfisz barrier by a wide margin.  The sharper
`k² log k` matters only later, in the *final rate*, not here.
-/

namespace NormalNumbers.JointLambert

open Finset Filter

/-- The killed-window height at a chosen prime-search height `X`: `k = ⌈4 log₂ log X⌉`. -/
noncomputable def countK (X : ℕ) : ℕ := ⌈4 * Real.logb 2 (Real.log (X : ℝ))⌉₊

/-- `k` is at most `6 log log X` for large `X`, since `4 / log 2 < 6`. -/
theorem eventually_countK_le : ∀ᶠ X : ℕ in atTop,
    1 ≤ countK X ∧ (countK X : ℝ) ≤ 6 * Real.log (Real.log (X : ℝ)) := by
  have hbase : ∀ᶠ L : ℝ in atTop,
      1 ≤ ⌈4 * Real.logb 2 L⌉₊ ∧ (⌈4 * Real.logb 2 L⌉₊ : ℝ) ≤ 6 * Real.log L := by
    filter_upwards [eventually_ge_atTop (1024 : ℝ)] with L hL
    have hL0 : (0 : ℝ) < L := by linarith
    have hs0 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hs : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have h1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
      rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    have ht : (6.9 : ℝ) ≤ Real.log L := by
      have h := Real.log_le_log (show (0:ℝ) < 1024 by norm_num) hL
      rw [h1024] at h; linarith
    have hlogb : Real.logb 2 L = Real.log L / Real.log 2 := rfl
    have hval : 4 * Real.logb 2 L ≤ 6 * Real.log L - 1 := by
      rw [hlogb, show (4 : ℝ) * (Real.log L / Real.log 2) = (4 * Real.log L) / Real.log 2 by ring,
        div_le_iff₀ hs0]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht) (show (0:ℝ) ≤ 6 * Real.log 2 - 4 by linarith)]
    have hpos : (0 : ℝ) < 4 * Real.logb 2 L := by
      rw [hlogb]
      have : (0:ℝ) < Real.log L := by linarith
      positivity
    refine ⟨Nat.one_le_ceil_iff.mpr hpos, ?_⟩
    have hc := (Nat.ceil_lt_add_one hpos.le).le
    linarith
  have htend : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact htend.eventually hbase

/-- `A (log L)³ ≤ θ √L` eventually: compare squares and use
`Real.isLittleO_pow_log_id_atTop` at `n = 6`. -/
theorem eventually_cube_log_le_sqrt {A θ : ℝ} (hA : 0 < A) (hθ : 0 < θ) :
    ∀ᶠ L : ℝ in atTop, A * (Real.log L) ^ 3 ≤ θ * Real.sqrt L := by
  have hlo := (Real.isLittleO_pow_log_id_atTop (n := 6)).def
    (show (0 : ℝ) < θ ^ 2 / A ^ 2 by positivity)
  filter_upwards [hlo, eventually_ge_atTop (1 : ℝ)] with L hL h1
  have hL0 : (0 : ℝ) < L := by linarith
  have hlogpos : (0 : ℝ) ≤ Real.log L := Real.log_nonneg h1
  have hnorm : Real.log L ^ 6 ≤ θ ^ 2 / A ^ 2 * L := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlogpos, abs_of_nonneg hL0.le, id] using hL
  have hsq : (A * (Real.log L) ^ 3) ^ 2 ≤ (θ * Real.sqrt L) ^ 2 := by
    have hs : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL0.le
    have h2 : A ^ 2 * Real.log L ^ 6 ≤ θ ^ 2 * L := by
      have hmul := mul_le_mul_of_nonneg_left hnorm (show (0:ℝ) ≤ A ^ 2 by positivity)
      calc A ^ 2 * Real.log L ^ 6 ≤ A ^ 2 * (θ ^ 2 / A ^ 2 * L) := hmul
        _ = θ ^ 2 * L := by field_simp
    calc (A * (Real.log L) ^ 3) ^ 2 = A ^ 2 * Real.log L ^ 6 := by ring
      _ ≤ θ ^ 2 * L := h2
      _ = (θ * Real.sqrt L) ^ 2 := by rw [mul_pow, hs]
  have hb : (0 : ℝ) ≤ θ * Real.sqrt L := by positivity
  have ha : (0 : ℝ) ≤ A * (Real.log L) ^ 3 := by positivity
  nlinarith [hsq, ha, hb]

/-- **The small-pool schedule clears the Siegel–Walfisz barrier at every large height.**
With `k = countK X` and any modulus `B ≤ (2k³)^(1 + c k²)`, both side conditions of
`exists_prime_supply_every_height` hold for all sufficiently large `X`. -/
theorem eventually_schedule_feasible (c : ℕ) {C η : ℝ} (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ X : ℕ in atTop, ∀ B : ℕ, 1 ≤ B →
      B ≤ (2 * (countK X) ^ 3) ^ (1 + c * (countK X) ^ 2) →
      (B : ℝ) ^ 3 ≤ (X : ℝ) ∧
        C * (B : ℝ) * Real.log (X : ℝ)
          * Real.exp (-(η / 2) * Real.sqrt (Real.log (X : ℝ))) ≤ 2 / 5 := by
  set θ : ℝ := η / 10 with hθdef
  have hθ : 0 < θ := by rw [hθdef]; positivity
  set D : ℝ := 864 * (1 + (c : ℝ)) with hDdef
  have hD : 0 < D := by rw [hDdef]; positivity
  have hbase : ∀ᶠ L : ℝ in atTop,
      D * (Real.log L) ^ 3 ≤ θ * Real.sqrt L ∧ Real.log L ≤ θ * Real.sqrt L ∧
        Real.log C ≤ θ * Real.sqrt L ∧ 1 ≤ θ * Real.sqrt L ∧
        3 * (θ * Real.sqrt L) ≤ L ∧ 0 < L := by
    have e1 := eventually_cube_log_le_sqrt hD hθ
    have e2 := eventually_cube_log_le_sqrt (show (0:ℝ) < 1 by norm_num) hθ
    have htd : Filter.Tendsto (fun L : ℝ => θ * Real.sqrt L) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hθ Real.tendsto_sqrt_atTop
    have e3 : ∀ᶠ L : ℝ in atTop, Real.log C ≤ θ * Real.sqrt L := htd.eventually_ge_atTop _
    have e4 : ∀ᶠ L : ℝ in atTop, 1 ≤ θ * Real.sqrt L := htd.eventually_ge_atTop _
    filter_upwards [e1, e2, e3, e4, eventually_ge_atTop (max 3 (9 * θ ^ 2))] with L h1 h2 h3 h4 h5
    have hL3 : (3 : ℝ) ≤ L := le_trans (le_max_left _ _) h5
    have hL0 : (0 : ℝ) < L := by linarith
    have hlog1 : (1 : ℝ) ≤ Real.log L := by
      have hx : Real.log 3 ≤ Real.log L := Real.log_le_log (by norm_num) hL3
      have h3e : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
      have hg : (1 : ℝ) ≤ Real.log 3 := by
        calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
          _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) h3e
      linarith
    refine ⟨h1, ?_, h3, h4, ?_, hL0⟩
    · have hcu : Real.log L ≤ 1 * (Real.log L) ^ 3 := by
        nlinarith [hlog1, mul_nonneg (mul_nonneg (sub_nonneg.mpr hlog1) (by linarith : (0:ℝ) ≤ Real.log L)) (by linarith : (0:ℝ) ≤ Real.log L + 1)]
      linarith [h2]
    · have hq : 9 * θ ^ 2 ≤ L := le_trans (le_max_right _ _) h5
      have hs : (3 : ℝ) * θ ≤ Real.sqrt L := by
        have hsq := Real.sqrt_le_sqrt hq
        rwa [show (9 : ℝ) * θ ^ 2 = (3 * θ) ^ 2 by ring, Real.sqrt_sq (by positivity)] at hsq
      nlinarith [Real.sq_sqrt hL0.le, Real.sqrt_nonneg L]
  have htend : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually hbase, eventually_countK_le, eventually_ge_atTop 2] with
    X hX hk hX2
  obtain ⟨hD3, hlogL, hlogC, hone, h3θ, hLpos⟩ := hX
  obtain ⟨hk1, hkle⟩ := hk
  set k : ℕ := countK X with hkdef
  set L : ℝ := Real.log (X : ℝ) with hLdef
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    have h : (0 : ℕ) < X := by omega
    exact_mod_cast h
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  intro B hB1 hBle
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB1
  have hlogB : Real.log (B : ℝ) ≤ θ * Real.sqrt L := by
    have hstep : Real.log (B : ℝ)
        ≤ (1 + (c : ℝ) * (k : ℝ) ^ 2) * Real.log (2 * (k : ℝ) ^ 3) := by
      have hcast : (((2 * k ^ 3) ^ (1 + c * k ^ 2) : ℕ) : ℝ)
          = (2 * (k : ℝ) ^ 3) ^ (1 + c * k ^ 2) := by push_cast; ring
      have h1 : Real.log (B : ℝ) ≤ Real.log (((2 * k ^ 3) ^ (1 + c * k ^ 2) : ℕ) : ℝ) :=
        Real.log_le_log hBpos (by exact_mod_cast hBle)
      rw [hcast, Real.log_pow] at h1
      calc Real.log (B : ℝ) ≤ ((1 + c * k ^ 2 : ℕ) : ℝ) * Real.log (2 * (k : ℝ) ^ 3) := h1
        _ = (1 + (c : ℝ) * (k : ℝ) ^ 2) * Real.log (2 * (k : ℝ) ^ 3) := by push_cast; ring
    have hlog2k : Real.log (2 * (k : ℝ) ^ 3) ≤ 1 + 3 * (k : ℝ) := by
      have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      have h3 : Real.log ((k : ℝ) ^ 3) = 3 * Real.log (k : ℝ) := by
        rw [Real.log_pow]; push_cast; ring
      have h4 : Real.log (k : ℝ) ≤ (k : ℝ) := Real.log_le_self (by linarith)
      rw [Real.log_mul (by norm_num) (by positivity), h3]
      linarith
    have hcoef : (1 : ℝ) + (c : ℝ) * (k : ℝ) ^ 2 ≤ (1 + (c : ℝ)) * (k : ℝ) ^ 2 := by
      nlinarith [hkR, sq_nonneg ((k : ℝ) - 1)]
    have hlin : (1 : ℝ) + 3 * (k : ℝ) ≤ 4 * (k : ℝ) := by linarith
    have hcube : (k : ℝ) ^ 3 ≤ 216 * (Real.log L) ^ 3 := by
      have h := pow_le_pow_left₀ (show (0:ℝ) ≤ (k:ℝ) by linarith) hkle 3
      calc (k : ℝ) ^ 3 ≤ (6 * Real.log L) ^ 3 := h
        _ = 216 * (Real.log L) ^ 3 := by ring
    have hfin : (1 + (c : ℝ) * (k : ℝ) ^ 2) * Real.log (2 * (k : ℝ) ^ 3)
        ≤ D * (Real.log L) ^ 3 := by
      have hp2 : (0 : ℝ) ≤ Real.log (2 * (k : ℝ) ^ 3) := by
        refine Real.log_nonneg ?_
        nlinarith [hkR]
      calc (1 + (c : ℝ) * (k : ℝ) ^ 2) * Real.log (2 * (k : ℝ) ^ 3)
          ≤ ((1 + (c : ℝ)) * (k : ℝ) ^ 2) * (4 * (k : ℝ)) :=
            mul_le_mul hcoef (le_trans hlog2k hlin) hp2 (by positivity)
        _ = 4 * (1 + (c : ℝ)) * (k : ℝ) ^ 3 := by ring
        _ ≤ 4 * (1 + (c : ℝ)) * (216 * (Real.log L) ^ 3) :=
            mul_le_mul_of_nonneg_left hcube (by positivity)
        _ = D * (Real.log L) ^ 3 := by rw [hDdef]; ring
    linarith [hstep, hfin, hD3]
  refine ⟨?_, ?_⟩
  · calc (B : ℝ) ^ 3 = Real.exp (Real.log ((B : ℝ) ^ 3)) := (Real.exp_log (by positivity)).symm
      _ = Real.exp (3 * Real.log (B : ℝ)) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
      _ = (X : ℝ) := Real.exp_log hXpos
  · have hexp : C * (B : ℝ) * L * Real.exp (-(η / 2) * Real.sqrt L)
        = Real.exp (Real.log C + Real.log (B : ℝ) + Real.log L
            + -(η / 2) * Real.sqrt L) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hC, Real.exp_log hBpos,
        Real.exp_log hLpos]
    have hsum : Real.log C + Real.log (B : ℝ) + Real.log L + -(η / 2) * Real.sqrt L ≤ -1 := by
      have hηθ : η / 2 = 5 * θ := by rw [hθdef]; ring
      rw [hηθ]
      nlinarith [hlogC, hlogB, hlogL, hone]
    have he1 : Real.exp (-1 : ℝ) ≤ 2 / 5 := by
      have h27 : (2.7 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
      have hid : Real.exp (-1 : ℝ) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
      rw [hid, div_le_iff₀ (Real.exp_pos 1)]
      linarith
    rw [hexp]
    exact le_trans (Real.exp_le_exp.mpr hsum) he1

end NormalNumbers.JointLambert
