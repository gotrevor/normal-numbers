import NormalNumbers.TwoPointDelangeParity
import NormalNumbers.DelangeSlotPNT
import NormalNumbers.TwoPointMertensLower

/-!
# `M(N) = o(N)` from the quantitative PNT — the last hypothesis of the parity case

`TwoPointDelangeParity.lean` reduces `DelangeMean (1/2)` to `MoebiusMeanZero`, i.e. to
`M(N) = ∑_{n ≤ N} μ(n) = o(N)`.  This file **proves** `MoebiusMeanZero` — in fact the sharper
`M(N) = O(N / log N)` — from three things already in this tree:

* `ArithmeticFunction.sum_moebius_mul_log_eq` (mathlib): `∑_{d | n} μ(d) log d = −Λ(n)`, i.e.
  `(μ·log) * ζ = −Λ`, hence by Möbius inversion `μ(n) log n = −(μ * Λ)(n)`;
* `NormalNumbers.DelangeSlot.exists_sum_abs_deltaN_le` (repo, on `PNTPort.MediumPNT`):
  `∑_{k ≤ N} |ψ(⌊N/k⌋) − ⌊N/k⌋| ≤ C·N` — the quantitative PNT summed over the hyperbola;
* `log_factorial_ge` (repo): `log(N!) ≥ N log N − N`, so `∑_{n ≤ N} log(N/n) ≤ N`.

The argument: summing `μ(n) log n = −(μ * Λ)(n)` over `n ≤ N` and using `∑_{d≤N} μ(d)⌊N/d⌋ = 1`,

    |∑_{n ≤ N} μ(n) log n| = |1 + ∑_{d ≤ N} μ(d)·Δ(⌊N/d⌋)| ≤ 1 + C·N ,

while `M(N) log N − ∑_{n≤N} μ(n) log n = ∑_{n≤N} μ(n) log(N/n)` is `≤ N` in absolute value.  So
`|M(N)| log N ≤ 1 + (C+1)N`.

**Consequence**: `delangeMean_half` — `DelangeMean (1/2)` unconditionally, which the elementary
`‖phase t − 1‖ < 1` route provably cannot reach.
-/

open Finset Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace NormalNumbers.CastingOut

/-- `μ(n)·log n`, the kernel of the log-weighted Möbius sum. -/
noncomputable def moebiusLogA : ArithmeticFunction ℝ :=
  (μ : ArithmeticFunction ℝ).pmul ArithmeticFunction.log

lemma moebiusLogA_apply (n : ℕ) : moebiusLogA n = (μ n : ℝ) * Real.log n := by
  rw [moebiusLogA, ArithmeticFunction.pmul_apply, intCoe_apply, ArithmeticFunction.log_apply]

/-- `(μ·log) * ζ = −Λ` — mathlib's divisor-sum identity, packaged. -/
lemma moebiusLogA_mul_zeta : moebiusLogA * (ζ : ArithmeticFunction ℝ) = -Λ := by
  ext n
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.neg_apply]
  simpa [moebiusLogA_apply, ArithmeticFunction.log_apply] using
    (ArithmeticFunction.sum_moebius_mul_log_eq (n := n))

/-- **`μ(n) log n = −(μ * Λ)(n)`** by Möbius inversion. -/
theorem moebiusLogA_eq : moebiusLogA = -((μ : ArithmeticFunction ℝ) * Λ) := by
  have h : moebiusLogA * (ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)
      = (-Λ) * (μ : ArithmeticFunction ℝ) := by rw [moebiusLogA_mul_zeta]
  rw [mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one] at h
  rw [h]; ring

/-- `|μ(n)| ≤ 1` over `ℝ`. -/
lemma abs_moebius_real_le_one (d : ℕ) : |(μ d : ℝ)| ≤ 1 := by
  have h := ArithmeticFunction.abs_moebius_le_one (n := d)
  calc |(μ d : ℝ)| = ((|μ d| : ℤ) : ℝ) := by push_cast; ring
    _ ≤ 1 := by exact_mod_cast h

/-- The pointwise form of `μ * Λ`. -/
lemma moebiusLog_eq_sum_divisors (n : ℕ) :
    (μ n : ℝ) * Real.log n = -∑ d ∈ n.divisors, (μ d : ℝ) * Λ (n / d) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) moebiusLogA_eq
  simp only [ArithmeticFunction.neg_apply, ArithmeticFunction.mul_apply] at h
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun d e => ((μ : ArithmeticFunction ℝ) d) * (Λ : ArithmeticFunction ℝ) e)] at h
  rw [moebiusLogA_apply] at h
  simpa [intCoe_apply] using h

/-- `∑_{d | n} μ(d) = [n = 1]`. -/
lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℝ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  simpa [intCoe_apply] using h

/-- **`∑_{d ≤ N} μ(d)⌊N/d⌋ = 1`** for `N ≥ 1`. -/
theorem sum_moebius_mul_natDiv {N : ℕ} (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Ioc 0 N, (μ d : ℝ) * ((N / d : ℕ) : ℝ) = 1 := by
  have hconv := sum_conv_eq (fun d => (μ d : ℝ)) (fun _ => (1 : ℝ)) N
  have hright : ∀ d ∈ Finset.Ioc 0 N,
      ((μ d : ℝ)) * ∑ _e ∈ Finset.Ioc 0 (N / d), (1 : ℝ) = (μ d : ℝ) * ((N / d : ℕ) : ℝ) := by
    intro d _
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    simp
  have hleft : ∀ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors, (μ d : ℝ) * (1 : ℝ)
      = if n = 1 then 1 else 0 := by
    intro n _
    simpa using sum_moebius_divisors n
  rw [← Finset.sum_congr rfl hright, ← hconv, Finset.sum_congr rfl hleft,
    Finset.sum_ite_eq' (Finset.Ioc 0 N) 1 (fun _ => (1 : ℝ))]
  simp only [Finset.mem_Ioc]
  rw [if_pos ⟨by omega, hN⟩]

/-- The log-weighted Möbius sum is `O(N)`. -/
theorem exists_sum_moebiusLog_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ) * Real.log n| ≤ 1 + C * N := by
  obtain ⟨C, hC0, hC⟩ := NormalNumbers.DelangeSlot.exists_sum_abs_deltaN_le
  refine ⟨C, hC0, fun N hN => ?_⟩
  -- the hyperbola form
  have hconv := sum_conv_eq (fun d => (μ d : ℝ)) (fun e => (Λ e : ℝ)) N
  have hleft : ∀ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors, (μ d : ℝ) * Λ (n / d)
      = -((μ n : ℝ) * Real.log n) := by
    intro n _
    rw [moebiusLog_eq_sum_divisors n]
    ring
  have hsum : ∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ) * Real.log n
      = -∑ d ∈ Finset.Ioc 0 N, (μ d : ℝ) * NormalNumbers.DelangeSlot.psiN (N / d) := by
    have h1 := Finset.sum_congr rfl hleft
    rw [hconv, Finset.sum_neg_distrib] at h1
    simp only [NormalNumbers.DelangeSlot.psiN]
    linarith [h1]
  -- split `ψ = id + Δ`
  have hsplit : ∀ d ∈ Finset.Ioc 0 N,
      (μ d : ℝ) * NormalNumbers.DelangeSlot.psiN (N / d)
        = (μ d : ℝ) * ((N / d : ℕ) : ℝ)
          + (μ d : ℝ) * NormalNumbers.DelangeSlot.deltaN (N / d) := by
    intro d _
    rw [NormalNumbers.DelangeSlot.deltaN]
    ring
  have hmu : ∀ d : ℕ, |(μ d : ℝ)| ≤ 1 := abs_moebius_real_le_one
  have htail : |∑ d ∈ Finset.Ioc 0 N, (μ d : ℝ) * NormalNumbers.DelangeSlot.deltaN (N / d)|
      ≤ C * N := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun d _ => ?_)) (hC N)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hmu d)
  rw [hsum, abs_neg, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    sum_moebius_mul_natDiv hN]
  calc |1 + ∑ d ∈ Finset.Ioc 0 N, (μ d : ℝ) * NormalNumbers.DelangeSlot.deltaN (N / d)|
      ≤ |(1 : ℝ)| + |∑ d ∈ Finset.Ioc 0 N, (μ d : ℝ) * NormalNumbers.DelangeSlot.deltaN (N / d)| :=
        abs_add_le _ _
    _ ≤ 1 + C * N := by rw [abs_one]; linarith [htail]

/-- `∑_{n ≤ N} log(N/n) ≤ N`, from `log(N!) ≥ N log N − N`. -/
lemma sum_log_div_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (Real.log N - Real.log n) ≤ (N : ℝ) := by
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext m; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hIoc, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have h := log_factorial_ge N
  have hcard : ((N + 1 - 1 : ℕ) : ℝ) = (N : ℝ) := by push_cast; ring
  rw [hcard]
  linarith

/-- **`|M(N)| log N ≤ 1 + (C+1)N`** — the quantitative Mertens bound. -/
theorem exists_abs_moebiusSum_log_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |(moebiusSum N : ℝ)| * Real.log N ≤ 1 + C * N := by
  obtain ⟨C, hC0, hC⟩ := exists_sum_moebiusLog_le
  refine ⟨C + 1, by linarith, fun N hN => ?_⟩
  have hMR : (moebiusSum N : ℝ) = ∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ) := by
    rw [moebiusSum]; push_cast; ring
  have hgap : |(moebiusSum N : ℝ) * Real.log N - ∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ) * Real.log n|
      ≤ (N : ℝ) := by
    have hrw : (moebiusSum N : ℝ) * Real.log N - ∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ) * Real.log n
        = ∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ) * (Real.log N - Real.log n) := by
      rw [hMR, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [hrw]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun n hn => ?_) (sum_log_div_le N)
    simp only [Finset.mem_Ioc] at hn
    have hlog : 0 ≤ Real.log N - Real.log n := by
      have h1 : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
      have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
      have := Real.log_le_log h2 h1
      linarith
    rw [abs_mul, abs_of_nonneg hlog]
    exact mul_le_of_le_one_left hlog (abs_moebius_real_le_one n)
  have h1 := hC N hN
  have h2 : |(moebiusSum N : ℝ) * Real.log N|
      ≤ |∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ) * Real.log n| + (N : ℝ) := by
    have := abs_sub_abs_le_abs_sub ((moebiusSum N : ℝ) * Real.log N)
      (∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ) * Real.log n)
    linarith [hgap]
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have habs : |(moebiusSum N : ℝ)| * Real.log N = |(moebiusSum N : ℝ) * Real.log N| := by
    rw [abs_mul, abs_of_nonneg hlogN]
  rw [habs]
  calc |(moebiusSum N : ℝ) * Real.log N|
      ≤ |∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ) * Real.log n| + (N : ℝ) := h2
    _ ≤ (1 + C * N) + (N : ℝ) := by linarith
    _ = 1 + (C + 1) * N := by ring

/-- **`M(N) = o(N)`: `MoebiusMeanZero` is a THEOREM of this repo.** -/
theorem moebiusMeanZero : MoebiusMeanZero := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_moebiusSum_log_le
  rw [MoebiusMeanZero, tendsto_zero_iff_abs_tendsto_zero]
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (𝓝 0) := hlog.inv_tendsto_atTop
  have hmaj : Tendsto (fun N : ℕ => (C + 1) * (Real.log N)⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul (C + 1)
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _) ?_ hmaj
  filter_upwards [Filter.eventually_ge_atTop 3] with N hN
  simp only [Function.comp_apply]
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hkey := hC N hN1
  rw [abs_div, Nat.abs_cast]
  rw [div_le_iff₀ (by linarith)]
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hstep : |(moebiusSum N : ℝ)| ≤ (1 + C * N) / Real.log N := by
    rw [le_div_iff₀ hlogpos]
    linarith
  calc |(moebiusSum N : ℝ)| ≤ (1 + C * N) / Real.log N := hstep
    _ ≤ ((C + 1) * N) / Real.log N := by
        have : 1 + C * (N : ℝ) ≤ (C + 1) * (N : ℝ) := by nlinarith
        exact div_le_div_of_nonneg_right this hlogpos.le
    _ = (C + 1) * (Real.log N)⁻¹ * N := by field_simp

/-- **`DelangeMean (1/2)`, unconditionally.**  The parity case of Delange's theorem, in kernel,
out of reach of the `‖phase t − 1‖ < 1` route. -/
theorem delangeMean_half : DelangeMean (1 / 2 : ℝ) :=
  delangeMean_half_of_moebius moebiusMeanZero

end NormalNumbers.CastingOut
