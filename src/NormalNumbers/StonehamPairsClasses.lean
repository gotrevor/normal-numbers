/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamPairsResultant

/-!
# Multiplicative classes for Stoneham pairs

This file isolates the global arithmetic behind the distinct-class branch of the literal
Bailey--Borwein pair argument.  A common prime fixes a normalization of the two factorization
vectors.  If every other coordinate has the same cross ratio, unique factorization makes positive
powers of the two bases equal.  Hence multiplicatively independent bases have a prime coordinate
whose normalized slope differs.
-/

namespace NormalNumbers.StonehamPairsNormal

/-- Two positive integral bases lie in the same multiplicative class when positive powers agree. -/
def StonehamPairMulDep (c₁ c₂ : ℕ) : Prop :=
  ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ c₁ ^ m = c₂ ^ n

/-- If a common prime coordinate makes the two factorization vectors cross-proportional at every
coordinate, then the bases lie in the same multiplicative class.  This is the exact finite
factorization form of the class dichotomy needed before analytic rate separation. -/
theorem stonehamPairMulDep_of_factorization_cross_eq
    (c₁ c₂ p : ℕ) (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0)
    (hp : p.Prime) (hpc₁ : p ∣ c₁) (hpc₂ : p ∣ c₂)
    (hcross : ∀ q : ℕ,
      c₂.factorization p * c₁.factorization q =
        c₁.factorization p * c₂.factorization q) :
    StonehamPairMulDep c₁ c₂ := by
  have hp₁ : 0 < c₁.factorization p := by
    exact Nat.pos_of_ne_zero (by simp [Nat.factorization_eq_zero_iff, hp, hpc₁, hc₁0])
  have hp₂ : 0 < c₂.factorization p := by
    exact Nat.pos_of_ne_zero (by simp [Nat.factorization_eq_zero_iff, hp, hpc₂, hc₂0])
  refine ⟨c₂.factorization p, c₁.factorization p, hp₂, hp₁, ?_⟩
  apply Nat.eq_of_factorization_eq (pow_ne_zero _ hc₁0) (pow_ne_zero _ hc₂0)
  intro q
  simpa [Nat.factorization_pow, mul_comm] using hcross q

/-- At any common prime, multiplicatively independent bases have a second prime coordinate at
which their factorization vectors have different cross ratios. -/
theorem exists_factorization_cross_ne_of_not_stonehamPairMulDep
    (c₁ c₂ p : ℕ) (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0)
    (hp : p.Prime) (hpc₁ : p ∣ c₁) (hpc₂ : p ∣ c₂)
    (hdep : ¬ StonehamPairMulDep c₁ c₂) :
    ∃ q : ℕ,
      c₂.factorization p * c₁.factorization q ≠
        c₁.factorization p * c₂.factorization q := by
  by_contra h
  push Not at h
  exact hdep (stonehamPairMulDep_of_factorization_cross_eq
    c₁ c₂ p hc₁0 hc₂0 hp hpc₁ hpc₂ h)

/-- A coordinate witnessing failure of cross-proportionality is necessarily a prime divisor of at
least one base.  Thus the witness produced above belongs to the finite denominator-prime set. -/
theorem prime_dvd_mul_of_factorization_cross_ne
    (c₁ c₂ p q : ℕ)
    (hcross : c₂.factorization p * c₁.factorization q ≠
      c₁.factorization p * c₂.factorization q) :
    q.Prime ∧ q ∣ c₁ * c₂ := by
  have hq : q.Prime := by
    by_contra hnot
    simp [Nat.factorization_eq_zero_of_not_prime _ hnot] at hcross
  refine ⟨hq, ?_⟩
  by_contra hnot
  have hq₁ : ¬ q ∣ c₁ := fun h => hnot (dvd_mul_of_dvd_left h c₂)
  have hq₂ : ¬ q ∣ c₂ := fun h => hnot (dvd_mul_of_dvd_right h c₁)
  simp [Nat.factorization_eq_zero_of_not_dvd hq₁,
    Nat.factorization_eq_zero_of_not_dvd hq₂] at hcross

/-- Full finite class witness: from one common prime of two distinct multiplicative classes, obtain
a second denominator prime whose normalized factorization coordinate differs. -/
theorem exists_prime_factorization_cross_ne_of_not_stonehamPairMulDep
    (c₁ c₂ p : ℕ) (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0)
    (hp : p.Prime) (hpc₁ : p ∣ c₁) (hpc₂ : p ∣ c₂)
    (hdep : ¬ StonehamPairMulDep c₁ c₂) :
    ∃ q : ℕ, q.Prime ∧ q ∣ c₁ * c₂ ∧
      c₂.factorization p * c₁.factorization q ≠
        c₁.factorization p * c₂.factorization q := by
  obtain ⟨q, hq⟩ := exists_factorization_cross_ne_of_not_stonehamPairMulDep
    c₁ c₂ p hc₁0 hc₂0 hp hpc₁ hpc₂ hdep
  exact ⟨q, (prime_dvd_mul_of_factorization_cross_ne c₁ c₂ p q hq).1,
    (prime_dvd_mul_of_factorization_cross_ne c₁ c₂ p q hq).2, hq⟩

/-- Two non-proportional factorization coordinates force a genuine logarithmic slope difference
at one of them.  This is the bridge from the finite class witness to separation of the entered
Stoneham depths `factorization * stonehamK`. -/
theorem factorization_logSlope_ne_or_of_cross_ne
    (c₁ c₂ p q : ℕ) (hc₁ : 2 ≤ c₁) (_hc₂ : 2 ≤ c₂)
    (hcross : c₂.factorization p * c₁.factorization q ≠
      c₁.factorization p * c₂.factorization q) :
    (c₁.factorization p : ℝ) * Real.log c₂ ≠
        (c₂.factorization p : ℝ) * Real.log c₁ ∨
      (c₁.factorization q : ℝ) * Real.log c₂ ≠
        (c₂.factorization q : ℝ) * Real.log c₁ := by
  by_contra h
  push Not at h
  rcases h with ⟨hp, hq⟩
  have hlog₁ : Real.log (c₁ : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hc₁))
  apply hcross
  have hpq := congrArg (fun x : ℝ => x * c₁.factorization q) hp
  have hqp := congrArg (fun x : ℝ => x * c₁.factorization p) hq
  have hreal : (c₂.factorization p : ℝ) * c₁.factorization q =
      (c₁.factorization p : ℝ) * c₂.factorization q := by
    apply mul_right_cancel₀ hlog₁
    nlinarith
  exact_mod_cast hreal

/-- Distinct multiplicative classes have unequal normalized factorization slopes at some prime in
the support of the two bases.  This is the global slope lemma requested by Lemma 3': it includes
both the exclusive-prime case and overlapping prime support. -/
theorem exists_prime_logSlope_ne_of_not_stonehamPairMulDep
    (c₁ c₂ : ℕ) (hc₁ : 2 ≤ c₁) (hc₂ : 2 ≤ c₂)
    (hdep : ¬ StonehamPairMulDep c₁ c₂) :
    ∃ p : ℕ, p.Prime ∧ p ∣ c₁ * c₂ ∧
      (c₁.factorization p : ℝ) * Real.log c₂ ≠
        (c₂.factorization p : ℝ) * Real.log c₁ := by
  let p := c₁.minFac
  have hc₁0 : c₁ ≠ 0 := by omega
  have hc₂0 : c₂ ≠ 0 := by omega
  have hp : p.Prime := by
    dsimp only [p]
    exact Nat.minFac_prime (by omega)
  have hpc₁ : p ∣ c₁ := by
    dsimp only [p]
    exact Nat.minFac_dvd c₁
  by_cases hpc₂ : p ∣ c₂
  · obtain ⟨q, hqprime, hqdiv, hcross⟩ :=
      exists_prime_factorization_cross_ne_of_not_stonehamPairMulDep
        c₁ c₂ p hc₁0 hc₂0 hp hpc₁ hpc₂ hdep
    rcases factorization_logSlope_ne_or_of_cross_ne c₁ c₂ p q hc₁ hc₂ hcross with
      hslope | hslope
    · exact ⟨p, hp, dvd_mul_of_dvd_left hpc₁ c₂, hslope⟩
    · exact ⟨q, hqprime, hqdiv, hslope⟩
  · refine ⟨p, hp, dvd_mul_of_dvd_left hpc₁ c₂, ?_⟩
    rw [Nat.factorization_eq_zero_of_not_dvd hpc₂, Nat.cast_zero, zero_mul]
    exact mul_ne_zero
      (by exact_mod_cast (Nat.pos_of_ne_zero (by
        simp [Nat.factorization_eq_zero_iff, hp, hpc₁, hc₁0])).ne')
      (ne_of_gt (Real.log_pos (by exact_mod_cast hc₂)))

/-- The integral entry depth `Nat.log c n` differs from the real logarithmic depth by less than
one base digit.  This bounded-error estimate is the quantitative input for turning an unequal
logarithmic slope into a depth gap growing linearly in `Real.log n`. -/
theorem natLog_mul_log_base_error
    (c n : ℕ) (hc : 2 ≤ c) (hn : 1 ≤ n) :
    0 ≤ Real.log n - (Nat.log c n : ℝ) * Real.log c ∧
      Real.log n - (Nat.log c n : ℝ) * Real.log c < Real.log c := by
  have hn0 : n ≠ 0 := by omega
  have hpow : c ^ Nat.log c n ≤ n := Nat.pow_log_le_self c hn0
  have hpow' : n < c ^ (Nat.log c n + 1) :=
    Nat.lt_pow_succ_log_self (by omega) n
  have hpowR : ((c ^ Nat.log c n : ℕ) : ℝ) ≤ n := by exact_mod_cast hpow
  have hpowR' : (n : ℝ) < (c ^ (Nat.log c n + 1) : ℕ) := by exact_mod_cast hpow'
  have hpowRcast : (c : ℝ) ^ Nat.log c n ≤ n := by
    simpa only [Nat.cast_pow] using hpowR
  have hpowRcast' : (n : ℝ) < (c : ℝ) ^ (Nat.log c n + 1) := by
    simpa only [Nat.cast_pow] using hpowR'
  have hlow := Real.log_le_log (by positivity : (0 : ℝ) < c ^ Nat.log c n) hpowRcast
  have hupp := Real.strictMonoOn_log (by positivity : (0 : ℝ) < n)
    (by positivity : (0 : ℝ) < c ^ (Nat.log c n + 1)) hpowRcast'
  rw [Real.log_pow] at hlow
  rw [Real.log_pow] at hupp
  push_cast at hupp
  constructor <;> nlinarith

end NormalNumbers.StonehamPairsNormal
