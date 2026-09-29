/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertAGPRange

/-!
# Rescaling the prime search: AGP's *consumer* needs far less than AGP

`docs/JOINT-LAMBERT-AGP-GAP.md` maps the obstacles to proving `AGP` itself.  Those obstacles
are real, but they are obstacles to the *strong* statement, not to the qualitative
joint-Lambert consumer.  Two demands in the old schedule created the detour, and both are
avoidable:

1. **The CRT modulus need not be a fixed power of the prime search endpoint.**  The old
   schedule tied `X = 2^(4k⁴)` to the modulus bound `B ≤ 2^(k⁴)`, i.e. `B = X^{1/4}` — deep in
   the range where only AGP-strength input works.  Nothing downstream needs that: `X` may be
   taken as large a function of the killed-window height `k` as we like.  Here
   `X = 2^(4k¹²)`, so `B ≤ 2^(k⁴)` sits in the **Siegel–Walfisz** range `exp(c√log X)`,
   where the *installed, proved* analytic input already applies.
2. **The excluded conductor need not exceed `log X`.**  `exists_prime_allocation` avoids any
   finite set of non-unit moduli at a cost of one pool prime each.  One excised conductor
   `P` therefore costs at most one prime, with no lower bound on `P` needed at all.

The analytic input is `exists_pointwise_exponential_distribution` (proved, and `#print
axioms`-clean), *not* `agpExpRange_holds` or `exceptionalModulus_gt_log`, which stay open.
-/

namespace NormalNumbers.JointLambert

open Finset Filter

/-! ### Growth: any fixed polynomial is eventually beaten by `2^k` -/

/-- For any degree `d` and any constant `c`, eventually `c·k^d ≤ 2^k`.  This replaces the
hand-rolled `poly_eight_le_two_pow` thresholds at the higher degrees the rescaled schedule
needs (`k¹²`, `k²⁴`); the price is that the threshold is not explicit, which costs nothing
because every consumer only needs *some* threshold. -/
lemma eventually_poly_le_two_pow (d : ℕ) (c : ℝ) :
    ∀ᶠ k : ℕ in atTop, c * (k : ℝ) ^ d ≤ (2 : ℝ) ^ k := by
  have hlim : Tendsto (fun k : ℕ => (k : ℝ) ^ d / (2 : ℝ) ^ k) atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt d (by norm_num)
  rcases le_or_gt c 0 with hc | hc
  · filter_upwards [] with k
    have h1 : c * (k : ℝ) ^ d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by positivity)
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    linarith
  · have hev : ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ d / (2 : ℝ) ^ k ≤ 1 / c := by
      exact hlim.eventually_le_const (by positivity)
    filter_upwards [hev] with k hk
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    rw [div_le_div_iff₀ h2 hc] at hk
    linarith

/-! ### The decay estimate: the rescaled schedule really does dominate the error -/

/-- `2^m = exp (m log 2)` for a natural exponent. -/
private lemma two_pow_eq_exp (m : ℕ) : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]

/-- **The feasibility test of the rescaled schedule.**  With `X = 2^(4k¹²)` the relative error
budget of the installed exponential distribution theorem,

  `C · φ(B) · log X · exp(−(η/2)√(log X))`  with  `φ(B) ≤ B ≤ 2^(k⁴)`,

is at most `4C·k¹²·exp(k⁴ log 2 − η k⁶ √(log 2))`, which tends to `0` because `k⁶ ≫ k⁴`.
This is exactly the inequality that *fails* for the old schedule `X = 2^(4k⁴)`, where the
same computation gives `exp(k⁴ log 2 − η k² √(log 2)) → ∞`. -/
lemma eventually_rescaled_error_small {C η : ℝ} (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop,
      C * ((4 * (k : ℝ) ^ 12) * (2 : ℝ) ^ (k ^ 4)
        * Real.exp (-(η / 2) * (2 * (k : ℝ) ^ 6 * Real.sqrt (Real.log 2)))) ≤ 2 / 5 := by
  set s : ℝ := Real.sqrt (Real.log 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
  -- eventually `η s k² ≥ log 2 + 1`
  have hgrow : ∀ᶠ k : ℕ in atTop, Real.log 2 + 1 ≤ η * s * (k : ℝ) ^ 2 := by
    have : Tendsto (fun k : ℕ => η * s * (k : ℝ) ^ 2) atTop atTop := by
      refine Filter.Tendsto.const_mul_atTop (by positivity) ?_
      exact (tendsto_pow_atTop (two_ne_zero)).comp tendsto_natCast_atTop_atTop
    exact this.eventually_ge_atTop _
  -- eventually `4C k¹² exp(−k) ≤ 2/5`
  have hdecay : ∀ᶠ k : ℕ in atTop,
      4 * C * ((k : ℝ) ^ 12 * Real.exp (-(k : ℝ))) ≤ 2 / 5 := by
    have h0 : Tendsto (fun k : ℕ => (k : ℝ) ^ 12 * Real.exp (-(k : ℝ))) atTop (nhds 0) :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 12).comp tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun k : ℕ => 4 * C * ((k : ℝ) ^ 12 * Real.exp (-(k : ℝ)))) atTop
        (nhds (4 * C * 0)) := h0.const_mul _
    rw [mul_zero] at h1
    exact h1.eventually_le_const (by norm_num)
  filter_upwards [hgrow, hdecay, eventually_ge_atTop 1] with k hgrow hdecay hk1
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  -- the exponent is at most `−k`
  have hexp : (k : ℝ) ^ 4 * Real.log 2 + -(η / 2) * (2 * (k : ℝ) ^ 6 * s) ≤ -(k : ℝ) := by
    have hk4 : (k : ℝ) ≤ (k : ℝ) ^ 4 := by
      calc (k : ℝ) = (k : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (k : ℝ) ^ 4 := pow_le_pow_right₀ hkR (by norm_num)
    have hkey : (Real.log 2 + 1) * (k : ℝ) ^ 4 ≤ η * s * (k : ℝ) ^ 2 * (k : ℝ) ^ 4 := by
      nlinarith [pow_nonneg (le_trans zero_le_one hkR) 4]
    have hid : η * s * (k : ℝ) ^ 2 * (k : ℝ) ^ 4 = (η / 2) * (2 * (k : ℝ) ^ 6 * s) := by ring
    nlinarith
  calc C * ((4 * (k : ℝ) ^ 12) * (2 : ℝ) ^ (k ^ 4)
          * Real.exp (-(η / 2) * (2 * (k : ℝ) ^ 6 * s)))
      = 4 * C * ((k : ℝ) ^ 12
          * Real.exp (((k ^ 4 : ℕ) : ℝ) * Real.log 2 + -(η / 2) * (2 * (k : ℝ) ^ 6 * s))) := by
        rw [Real.exp_add, ← two_pow_eq_exp]; ring
    _ ≤ 4 * C * ((k : ℝ) ^ 12 * Real.exp (-(k : ℝ))) := by
        have hcast : ((k ^ 4 : ℕ) : ℝ) = (k : ℝ) ^ 4 := by push_cast; ring
        rw [hcast]
        have := Real.exp_le_exp.mpr hexp
        have hpos : (0 : ℝ) ≤ 4 * C * (k : ℝ) ^ 12 := by positivity
        nlinarith [Real.exp_pos (-(k : ℝ))]
    _ ≤ 2 / 5 := hdecay

/-! ### The rescaled, unconditional prime-supply theorem -/

/-- `log X` for the rescaled endpoint. -/
private lemma log_rescaled (k : ℕ) :
    Real.log ((2 ^ (4 * k ^ 12) : ℕ) : ℝ) = (4 * (k : ℝ) ^ 12) * Real.log 2 := by
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

private lemma sqrt_log_rescaled (k : ℕ) :
    Real.sqrt (Real.log ((2 ^ (4 * k ^ 12) : ℕ) : ℝ))
      = 2 * (k : ℝ) ^ 6 * Real.sqrt (Real.log 2) := by
  rw [log_rescaled]
  rw [show (4 * (k : ℝ) ^ 12) * Real.log 2 = (2 * (k : ℝ) ^ 6) ^ 2 * Real.log 2 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **The unconditional rescaled supply.**  For every large killed-window height `k` there is
a single excised conductor `P` (either `1`, or a prime), chosen *before* the modulus and the
residue, such that every modulus `B ≤ 2^(k⁴)` coprime to `P` and every reduced residue `u`
satisfy the AGP conclusion at the rescaled endpoint `X = 2^(4k¹²)`.

This is `AGP`'s conclusion with `AGP`'s quantifier order, on the range the *proved* analytic
input covers; the `D > log X` clause of `AGP` is simply not asked for, because the consumer
never needed it. -/
theorem exists_rescaled_prime_supply :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ P : ℕ, (P = 1 ∨ P.Prime) ∧
        ∀ B u : ℕ, 1 ≤ B → B ≤ 2 ^ (k ^ 4) → Nat.Coprime u B → Nat.Coprime B P →
          ((2 ^ (4 * k ^ 12) : ℕ) : ℝ)
              / (2 * (B.totient : ℝ) * Real.log ((2 ^ (4 * k ^ 12) : ℕ) : ℝ))
            ≤ (((range (2 ^ (4 * k ^ 12) + 1)).filter
                  (fun z => z.Prime ∧ z % B = u % B)).card : ℝ) := by
  classical
  obtain ⟨η, C, hη, hη4, hC, hdist⟩ := exists_pointwise_exponential_distribution
  obtain ⟨x0, hx0⟩ := eventually_atTop.1
    (hdist.and (Erdos446.eventually_primeCounting_tenth_bounds.and (eventually_ge_atTop 3)))
  obtain ⟨k1, hk1⟩ := eventually_atTop.1
    ((eventually_rescaled_error_small hC hη).and (eventually_ge_atTop 1))
  refine ⟨max k1 (x0 + 1), fun k hk => ?_⟩
  have hkk1 : k1 ≤ k := le_trans (le_max_left _ _) hk
  have hkx0 : x0 + 1 ≤ k := le_trans (le_max_right _ _) hk
  obtain ⟨herr, hk1'⟩ := hk1 k hkk1
  set X : ℕ := 2 ^ (4 * k ^ 12) with hX
  have hkX : k ≤ X := by
    have h1 : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    have h2 : (2 : ℕ) ^ k ≤ X := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have : k ≤ k ^ 12 := Nat.le_self_pow (by norm_num) k
      omega
    omega
  have hXx0 : x0 ≤ X := by omega
  obtain ⟨hdistX, hpiX, hX3⟩ := hx0 X hXx0
  obtain ⟨P, hPcut, hPprime, hPbound⟩ := hdistX
  refine ⟨P, hPprime, fun B u hB1 hBU hcopuB hcopBP => ?_⟩
  -- `B` is inside the distribution level `⌊X^{1/3}⌋`
  have hBlevel : B ≤ Erdos4.FGKMT.powerDistributionLevel X := by
    refine Nat.le_floor ?_
    by_contra hcon
    push_neg at hcon
    have hcube : BoundedGaps.Maynard.vaughanCubeRoot X ^ 3 < (B : ℝ) ^ 3 := by
      refine pow_lt_pow_left₀ hcon (BoundedGaps.Maynard.vaughanCubeRoot_nonneg X) (by norm_num)
    rw [BoundedGaps.Maynard.vaughanCubeRoot_cube] at hcube
    have hBcube : (B : ℝ) ^ 3 ≤ (X : ℝ) := by
      have hnat : B ^ 3 ≤ X := by
        calc B ^ 3 ≤ (2 ^ (k ^ 4)) ^ 3 := Nat.pow_le_pow_left hBU 3
          _ = 2 ^ (3 * k ^ 4) := by rw [← pow_mul]; ring_nf
          _ ≤ X := by
              refine Nat.pow_le_pow_right (by norm_num) ?_
              have : k ^ 4 ≤ k ^ 12 := Nat.pow_le_pow_right (by omega) (by norm_num)
              omega
      exact_mod_cast hnat
    linarith
  have hkey := hPbound B u hB1 hBlevel hcopBP hcopuB
  -- notation
  set φ : ℝ := (B.totient : ℝ) with hφ
  set Λ : ℝ := Real.log ((X : ℕ) : ℝ) with hΛ
  have hφ0 : 0 < φ := by
    have h : 0 < B.totient := Nat.totient_pos.mpr (by omega)
    rw [hφ]; exact_mod_cast h
  have hXR : (0 : ℝ) < (X : ℝ) := by positivity
  have hΛpos : 0 < Λ := by
    rw [hΛ, hX, log_rescaled]
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1'
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  set E : ℝ := C * ((X : ℝ) * Real.exp (-(η / 2) * Real.sqrt Λ)) with hE
  -- the error is small relative to the main term
  have hEsmall : E * (φ * Λ) ≤ (2 / 5) * (X : ℝ) := by
    have hφB : φ ≤ (2 : ℝ) ^ (k ^ 4) := by
      have h1 : φ ≤ (B : ℝ) := by rw [hφ]; exact_mod_cast Nat.totient_le B
      have h2 : (B : ℝ) ≤ (2 : ℝ) ^ (k ^ 4) := by exact_mod_cast hBU
      linarith
    have hΛle : Λ ≤ 4 * (k : ℝ) ^ 12 := by
      rw [hΛ, hX, log_rescaled]
      have hl2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
      nlinarith [pow_nonneg (show (0:ℝ) ≤ (k:ℝ) by positivity) 12]
    have hsq : Real.sqrt Λ = 2 * (k : ℝ) ^ 6 * Real.sqrt (Real.log 2) := by
      rw [hΛ, hX]; exact sqrt_log_rescaled k
    rw [hE, hsq]
    set w : ℝ := -(η / 2) * (2 * (k : ℝ) ^ 6 * Real.sqrt (Real.log 2)) with hw
    have hexppos : (0 : ℝ) < Real.exp w := Real.exp_pos _
    have hprod : φ * Λ ≤ (2 : ℝ) ^ (k ^ 4) * (4 * (k : ℝ) ^ 12) :=
      mul_le_mul hφB hΛle hΛpos.le (by positivity)
    calc C * ((X : ℝ) * Real.exp w) * (φ * Λ)
        = (X : ℝ) * (C * Real.exp w * (φ * Λ)) := by ring
      _ ≤ (X : ℝ) * (C * Real.exp w * ((2 : ℝ) ^ (k ^ 4) * (4 * (k : ℝ) ^ 12))) := by
          refine mul_le_mul_of_nonneg_left ?_ hXR.le
          exact mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = (X : ℝ) * (C * (4 * (k : ℝ) ^ 12 * (2 : ℝ) ^ (k ^ 4) * Real.exp w)) := by ring
      _ ≤ (X : ℝ) * (2 / 5) := mul_le_mul_of_nonneg_left herr hXR.le
      _ = 2 / 5 * (X : ℝ) := by ring
  -- the main term
  have hbridge : (BoundedGaps.Maynard.primeCountTotal X : ℝ) = (X.primeCounting : ℝ) := rfl
  have hπ : (9 / 10 : ℝ) * ((X : ℝ) / Λ) ≤ (BoundedGaps.Maynard.primeCountTotal X : ℝ) := by
    rw [hbridge]; exact hpiX.1
  have hlow : (BoundedGaps.Maynard.primeCountTotal X : ℝ) / φ - E
      ≤ (BoundedGaps.Maynard.primeCountUpTo X B (u % B) : ℝ) := by
    have habs := abs_le.1 hkey
    linarith [habs.1]
  rw [← agpCount_eq_primeCountUpTo] at hlow
  set N : ℝ := ((((range (X + 1)).filter (fun z => z.Prime ∧ z % B = u % B)).card : ℕ) : ℝ)
    with hN
  rw [div_le_iff₀ (by positivity)]
  have m1 : (BoundedGaps.Maynard.primeCountTotal X : ℝ) * Λ - E * (φ * Λ) ≤ N * (φ * Λ) := by
    have h := mul_le_mul_of_nonneg_right hlow (show (0 : ℝ) ≤ φ * Λ by positivity)
    calc (BoundedGaps.Maynard.primeCountTotal X : ℝ) * Λ - E * (φ * Λ)
        = ((BoundedGaps.Maynard.primeCountTotal X : ℝ) / φ - E) * (φ * Λ) := by
          field_simp
      _ ≤ N * (φ * Λ) := h
  have m2 : (9 / 10 : ℝ) * (X : ℝ) ≤ (BoundedGaps.Maynard.primeCountTotal X : ℝ) * Λ := by
    have h := mul_le_mul_of_nonneg_right hπ hΛpos.le
    calc (9 / 10 : ℝ) * (X : ℝ) = (9 / 10 * ((X : ℝ) / Λ)) * Λ := by field_simp
      _ ≤ _ := h
  have hexpand : N * (2 * φ * Λ) = 2 * (N * (φ * Λ)) := by ring
  linarith

end NormalNumbers.JointLambert
