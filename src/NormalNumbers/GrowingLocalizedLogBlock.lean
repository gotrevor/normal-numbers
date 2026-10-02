/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.GrowingLocalizedLogExponent
import NormalNumbers.GrowingLocalizedLogCost
import NormalNumbers.GrowingLocalizedLogTail

/-!
# N8: one clean block

`block_bound`: at a clean time `n₀` followed by `H` steps with no index of `S`, the block sum
`Σ_{t<H} e(a R_{n₀+t})` is a Korobov sum `Σ e(A 2^t/q)` with `q = den(a R_{n₀})`.  The modulus
`q` is odd, its primes are `≤ Z`, and `3^K/|a| ≤ q ≤ n₀^{π(Z)}`.  So Vandehey at a self-chosen
depth `k ≤ π(Z) log n₀/log H + 2` gives
`‖Σ‖ ≤ 2 + (A_k+B_k) H^{1−2^{−k−4}} (1 + π(Z) log n₀)`, with `P` the odd primes `≤ Z`.
-/

namespace NormalNumbers.GrowingLocalizedLog

open Finset NormalNumbers.Literature.VandeheyDiff NormalNumbers.G4

/-- The odd primes `≤ Z`. -/
def oddPrimes (Z : ℕ) : Finset ℕ := (Nat.primesLE Z).filter (· ≠ 2)

lemma sum_range_eq_sum_Icc (f : ℕ → ℂ) (H : ℕ) :
    ∑ t ∈ range H, f t + f H = f 0 + ∑ n ∈ Icc 1 H, f n := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega)]
    linear_combination ih

theorem block_bound (hV : VandeheyThm51) {S : ℕ → Prop} {Z n₀ H : ℕ} (hc : CleanAt S Z n₀)
    (h3 : 3 ≤ Z) (hn : 1 ≤ n₀) (hS1 : S (3 ^ Nat.log 3 n₀)) (hS2 : S (2 * 3 ^ Nat.log 3 n₀))
    (hfree : ∀ j, n₀ < j → j < n₀ + H → ¬ S j) (a : ℤ) (ha : a ≠ 0)
    (hH : 2 ≤ H) (hq2 : 2 * a.natAbs ≤ 3 ^ Nat.log 3 n₀)
    (hHq : (H : ℝ) ≤ (((3 ^ Nat.log 3 n₀ : ℕ) : ℝ) / a.natAbs) ^ 4) :
    ∃ k : ℕ, (k : ℝ) ≤ Z.primeCounting * Real.log n₀ / Real.log H + 2 ∧
      ‖∑ t ∈ range H, ePhase ((a : ℝ) * (Rs S (n₀ + t) : ℝ))‖ ≤
        2 + ((constPair 2 (oddPrimes Z) k).1 + (constPair 2 (oddPrimes Z) k).2) *
          (H : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) * (1 + Z.primeCounting * Real.log n₀) := by
  obtain ⟨hden, h3K⟩ := den_bounds hc h3 hn hS1 hS2 a ha
  set r : ℚ := (a : ℚ) * Rs S n₀ with hr
  set q := r.den
  set A := r.num
  set K := Nat.log 3 n₀
  have hab : (0 : ℝ) < a.natAbs := by exact_mod_cast Int.natAbs_pos.2 ha
  -- `q ≥ 2`
  have hq2' : 2 ≤ q := by
    by_contra hlt; push Not at hlt
    have : q * a.natAbs ≤ 1 * a.natAbs := Nat.mul_le_mul_right _ (by omega)
    have := Int.natAbs_pos.2 ha
    omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  -- primes of `q`
  have hqP : ∀ p, p.Prime → p ∣ q → p ∈ oddPrimes Z := by
    intro p hp hpq
    obtain ⟨h1, h2⟩ := prime_dvd_oddD hp (hpq.trans hden)
    exact mem_oddPrimes.2 ⟨hp, h1, h2⟩
  have hP : ∀ p ∈ oddPrimes Z, p.Prime ∧ Nat.Coprime p 2 := by
    intro p hp
    obtain ⟨hpp, -, hp2⟩ := mem_oddPrimes.1 hp
    exact ⟨hpp, (Nat.coprime_primes hpp Nat.prime_two).2 hp2⟩
  have hcop : IsCoprime A (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.2 r.reduced
  -- `log H ≤ 4 log q`
  have hqlow : ((3 ^ K : ℕ) : ℝ) / a.natAbs ≤ q := by
    rw [div_le_iff₀ hab]; exact_mod_cast h3K
  have hLq : Real.log H ≤ 4 * Real.log q := by
    have hH0 : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
    rw [show (4 : ℝ) * Real.log q = ((4 : ℕ) : ℝ) * Real.log q by norm_num, ← Real.log_pow]
    apply Real.log_le_log hH0
    refine hHq.trans (pow_le_pow_left₀ ?_ hqlow 4)
    positivity
  obtain ⟨k, hk, hbound⟩ := vandehey_window_bound hV 2 le_rfl (oddPrimes Z) hP q hq2' hqP A hcop
    H hH hLq
  -- `log q ≤ π(Z) log n₀`
  have hqup : Real.log q ≤ Z.primeCounting * Real.log n₀ := by
    have h1 : q ≤ n₀ ^ Z.primeCounting :=
      (Nat.le_of_dvd (oddD_pos Z n₀) hden).trans (oddD_le Z n₀ hn)
    have h1' : (q : ℝ) ≤ (n₀ : ℝ) ^ Z.primeCounting := by exact_mod_cast h1
    calc Real.log q ≤ Real.log ((n₀ : ℝ) ^ Z.primeCounting) := Real.log_le_log hq0 h1'
      _ = _ := by rw [Real.log_pow]
  have hlogH : 0 < Real.log H := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  refine ⟨k, hk.trans (by gcongr), ?_⟩
  -- the block sum is the Korobov sum
  have hrq : (r : ℝ) = (A : ℝ) / q := by
    rw [← Rat.num_div_den r]; push_cast; rfl
  set g : ℕ → ℂ := fun t => ePhase ((A : ℝ) * (2 : ℝ) ^ t / q)
  have hterm : ∀ t ∈ range H, ePhase ((a : ℝ) * (Rs S (n₀ + t) : ℝ)) = g t := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [Rs_shift S n₀ t (fun j h1 h2 => hfree j h1 (by omega))]
    simp only [g]
    congr 1
    have : (a : ℝ) * ((2 ^ t * Rs S n₀ : ℚ) : ℝ) = (2 : ℝ) ^ t * (r : ℝ) := by
      rw [hr]; push_cast; ring
    rw [this, hrq]; ring
  rw [Finset.sum_congr rfl hterm]
  have hsplit := sum_range_eq_sum_Icc g H
  have heq : ∑ t ∈ range H, g t = g 0 + ∑ n ∈ Icc 1 H, g n - g H := by
    rw [← hsplit]; ring
  have hg : ∀ t, ‖g t‖ = 1 := fun t => norm_ePhase _
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hexp : (1 + Real.log q) ^ ((2 : ℝ) ^ (-(k : ℝ))) ≤ 1 + Z.primeCounting * Real.log n₀ := by
    have h1 : (1 + Real.log q) ^ ((2 : ℝ) ^ (-(k : ℝ))) ≤ (1 + Real.log q) ^ (1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
    rw [Real.rpow_one] at h1; linarith
  have hAB := constPair_nonneg 2 (oddPrimes Z) k
  have hHpow : 0 ≤ (H : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) := by positivity
  have hb' : ‖∑ n ∈ Icc 1 H, g n‖ ≤ ((constPair 2 (oddPrimes Z) k).1 +
      (constPair 2 (oddPrimes Z) k).2) * (H : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) *
      (1 + Z.primeCounting * Real.log n₀) := by
    have hb2 := hbound
    simp only [Nat.cast_ofNat] at hb2
    refine hb2.trans ?_
    exact mul_le_mul_of_nonneg_left hexp (mul_nonneg (add_nonneg hAB.1 hAB.2) hHpow)
  rw [heq]
  calc ‖g 0 + ∑ n ∈ Icc 1 H, g n - g H‖ ≤ ‖g 0‖ + ‖∑ n ∈ Icc 1 H, g n‖ + ‖g H‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr; exact norm_add_le _ _
    _ ≤ _ := by rw [hg, hg]; linarith

end NormalNumbers.GrowingLocalizedLog
