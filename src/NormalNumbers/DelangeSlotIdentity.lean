import NormalNumbers.DelangeSlotBasic

/-!
# The Levin–Fainleib / von-Mangoldt identity for `h = z ^ ω_{>P}`

This is the exact algebraic backbone of the elementary route to the Delange slot
(`DESIGN-2026-09-24-delange-route.md`).  Writing `S N = ∑_{n ≤ N} h n` we prove, with **no
error terms and no analysis**:

* `sum_divisorAntidiagonal_swap` — the general Dirichlet swap
  `∑_{n ≤ N} ∑_{d·m = n} F d m = ∑_{d ≤ N} ∑_{m ≤ N/d} F d m` (mathlib only has the version
  specialised to a convolution `f * g`, which does not apply: `h` is *not* multiplicative across
  a non-coprime factorisation);
* `sum_h_mul_log` — `∑_{n ≤ N} h n log n = ∑_{d ≤ N} Λ d · ∑_{m ≤ N/d} h (d·m)`;
* `sum_h_shift_large` / `sum_h_shift_small` — evaluation of the inner sum at a prime power
  `d = p ^ j`:  it is `z · S (N/d) - (z-1) · (sum over multiples of p)` when `P < p`, and
  exactly `S (N/d)` when `p ≤ P`.

Chaining these gives `∑_{n≤N} h n log n = z ∑_{d≤N} Λ d · S (N/d) + E` with `E` a sum of two
explicitly-bounded pieces; that is the identity the analytic step consumes.
-/

open Finset ArithmeticFunction

namespace NormalNumbers.DelangeSlot

/-- `h z P n = z ^ ω_{>P}(n)`, the multiplicative function of the slot. -/
noncomputable def hfun (z : ℂ) (P n : ℕ) : ℂ := z ^ omegaLarge P n

/-- `S z P N = ∑_{1 ≤ n ≤ N} h n`, the partial sum whose smallness is the theorem. -/
noncomputable def Ssum (z : ℂ) (P N : ℕ) : ℂ := ∑ n ∈ Ioc 0 N, hfun z P n

@[simp] lemma hfun_one (z : ℂ) (P : ℕ) : hfun z P 1 = 1 := by simp [hfun]

lemma norm_hfun_le {z : ℂ} (hz : ‖z‖ = 1) (P n : ℕ) : ‖hfun z P n‖ = 1 := by
  simp [hfun, norm_pow, hz]

/-- `‖S z P N‖ ≤ N` for unimodular `z`. -/
lemma norm_Ssum_le {z : ℂ} (hz : ‖z‖ = 1) (P N : ℕ) : ‖Ssum z P N‖ ≤ N := by
  refine (norm_sum_le _ _).trans ?_
  simp [norm_hfun_le hz]

/-- **Dirichlet swap.**  Summing a general kernel over all factorisations `d * m = n ≤ N`. -/
theorem sum_divisorAntidiagonal_swap {R : Type*} [AddCommMonoid R] (F : ℕ → ℕ → R) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2
      = ∑ d ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / d), F d m := by
  classical
  have step1 : ∑ n ∈ Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2
      = ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 ≤ N, F x.1 x.2 := by
    trans ∑ n ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n, F x.1 x.2
    · refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
    · simp_rw [sum_filter]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ ↦ (by simp_all)
  rw [step1, sum_filter, sum_product]
  refine sum_congr rfl fun n hn ↦ ?_
  simp only [sum_ite, not_le, sum_const_zero, add_zero]
  congr 1
  ext m
  have hn1 : 0 < n := (mem_Ioc.1 hn).1
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨hm0, _⟩, hle⟩
    exact ⟨hm0, (Nat.le_div_iff_mul_le hn1).2 (by lia)⟩
  · rintro ⟨hm0, hle⟩
    have h2 := (Nat.le_div_iff_mul_le hn1).1 hle
    exact ⟨⟨hm0, le_trans (Nat.le_mul_of_pos_left m hn1) (by lia)⟩, by lia⟩

/-- **The von-Mangoldt identity.** -/
theorem sum_hfun_mul_log (z : ℂ) (P N : ℕ) :
    ∑ n ∈ Ioc 0 N, hfun z P n * (Real.log n : ℂ)
      = ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * ∑ m ∈ Ioc 0 (N / d), hfun z P (d * m) := by
  classical
  have key : ∀ n ∈ Ioc 0 N, hfun z P n * (Real.log n : ℂ)
      = ∑ x ∈ n.divisorsAntidiagonal, (Λ x.1 : ℂ) * hfun z P (x.1 * x.2) := by
    intro n hn
    rw [Nat.sum_divisorsAntidiagonal (f := fun d m => (Λ d : ℂ) * hfun z P (d * m))]
    have : ∀ d ∈ n.divisors, (Λ d : ℂ) * hfun z P (d * (n / d)) = (Λ d : ℂ) * hfun z P n := by
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    rw [sum_congr rfl this, ← sum_mul, ← Complex.ofReal_sum, vonMangoldt_sum]
    ring
  rw [sum_congr rfl key, sum_divisorAntidiagonal_swap
      (F := fun d m => (Λ d : ℂ) * hfun z P (d * m)) N]
  exact sum_congr rfl fun d _ ↦ (mul_sum _ _ _).symm


/-- The tail sum over multiples of `p`: `T p X = ∑_{m ≤ X, p ∣ m} h m`. -/
noncomputable def Tsum (z : ℂ) (P p X : ℕ) : ℂ :=
  ∑ m ∈ (Ioc 0 X).filter (fun m => p ∣ m), hfun z P m

lemma norm_Tsum_le {z : ℂ} (hz : ‖z‖ = 1) (P p X : ℕ) : ‖Tsum z P p X‖ ≤ (X / p : ℕ) := by
  classical
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_hfun_le hz, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast le_of_eq (Nat.Ioc_filter_dvd_card_eq_div X p)

/-- **Shift at a large prime.**  `p > P`: inserting `p^j` multiplies by `z` unless `p ∣ m`. -/
lemma sum_hfun_shift_large {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ≠ 0) (z : ℂ) {P : ℕ}
    (hP : P < p) (X : ℕ) :
    ∑ m ∈ Ioc 0 X, hfun z P (p ^ j * m) = z * Ssum z P X - (z - 1) * Tsum z P p X := by
  classical
  have hterm : ∀ m ∈ Ioc 0 X, hfun z P (p ^ j * m)
      = z * hfun z P m - (if p ∣ m then (z - 1) * hfun z P m else 0) := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (mem_Ioc.1 hm).1; lia
    rw [hfun, omegaLarge_prime_pow_mul hp hj hm0 P]
    by_cases hpm : p ∣ m
    · simp [hpm, hfun]; ring
    · simp [hpm, hP, hfun, pow_succ]; ring
  rw [sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, Ssum, Tsum,
    ← Finset.sum_filter, ← Finset.mul_sum]

/-- **Shift at a small prime.**  `p ≤ P`: inserting `p^j` changes nothing. -/
lemma sum_hfun_shift_small {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ≠ 0) (z : ℂ) {P : ℕ}
    (hP : ¬ P < p) (X : ℕ) :
    ∑ m ∈ Ioc 0 X, hfun z P (p ^ j * m) = Ssum z P X := by
  classical
  refine sum_congr rfl fun m hm ↦ ?_
  have hm0 : m ≠ 0 := by have := (mem_Ioc.1 hm).1; lia
  rw [hfun, omegaLarge_prime_pow_mul hp hj hm0 P]
  simp [hP, hfun]

end NormalNumbers.DelangeSlot
