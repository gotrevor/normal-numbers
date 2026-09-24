import NormalNumbers.TwoPointKataiCS

/-!
# Turán–Kubilius for the truncated prime-divisor count

The second obligation of `KataiQuantSharp`: the number of primes `≤ w` dividing `n` concentrates
around `L(w) = Σ_{p≤w} 1/p`.

Working over `n ∈ (0, N]` the two moments are exact sums of counting functions:

    Σ_n ω_w(n)   = Σ_{p ≤ w} ⌊N/p⌋ ,
    Σ_n ω_w(n)²  = Σ_{p, q ≤ w} #{n ≤ N : p ∣ n ∧ q ∣ n}
                 = Σ_{p ≠ q} ⌊N/pq⌋ + Σ_p ⌊N/p⌋ ,

using that distinct primes are coprime.  Since `⌊N/p⌋ ≤ N/p` and `⌊N/p⌋ ≥ N/p − 1`, and
`Σ_{p≠q} 1/pq ≤ L(w)²`, expanding the square gives the clean bound

    Σ_{n ≤ N} (ω_w(n) − L(w))²  ≤  N·L(w) + 2·L(w)·π(w) ,

with no hidden constants — and hence `≤ 2·N·L(w)` as soon as `2π(w) ≤ N`, which the Kátai
hypothesis `w² ≤ N` supplies.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- `ω_w(n)`: the number of primes `≤ w` dividing `n`. -/
noncomputable def kataiOmega (w n : ℕ) : ℕ := ((primesLe w).filter (fun p => p ∣ n)).card

lemma kataiOmega_eq_sum (w n : ℕ) :
    (kataiOmega w n : ℝ) = ∑ p ∈ primesLe w, if p ∣ n then (1 : ℝ) else 0 := by
  classical
  rw [kataiOmega, Finset.card_filter]
  push_cast
  rfl

/-- First moment. -/
lemma sum_kataiOmega (w N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (kataiOmega w n : ℝ) = ∑ p ∈ primesLe w, ((N / p : ℕ) : ℝ) := by
  classical
  simp only [kataiOmega_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    Nat.Ioc_filter_dvd_card_eq_div]

/-- Second moment, as a double sum of joint counts. -/
lemma sum_kataiOmega_sq (w N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (kataiOmega w n : ℝ) ^ 2
      = ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
          ((((Finset.Ioc 0 N).filter (fun n => p ∣ n ∧ q ∣ n)).card : ℕ) : ℝ) := by
  classical
  have hstep : ∀ n : ℕ, (kataiOmega w n : ℝ) ^ 2
      = ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
          (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) := by
    intro n
    rw [sq, kataiOmega_eq_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;> simp [hp, hq]
  rw [Finset.sum_congr rfl fun n _ => hstep n, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- For distinct primes the joint count is the count of multiples of `pq`. -/
lemma joint_count_eq (p q N : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ((Finset.Ioc 0 N).filter (fun n => p ∣ n ∧ q ∣ n)).card = N / (p * q) := by
  classical
  have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have : (Finset.Ioc 0 N).filter (fun n => p ∣ n ∧ q ∣ n)
      = (Finset.Ioc 0 N).filter (fun n => p * q ∣ n) := by
    refine Finset.filter_congr fun n _ => ?_
    constructor
    · rintro ⟨h1, h2⟩; exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hco h1 h2
    · intro h
      exact ⟨dvd_trans (Dvd.intro q rfl) h, dvd_trans (Dvd.intro_left p rfl) h⟩
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

lemma self_count_eq (p N : ℕ) :
    ((Finset.Ioc 0 N).filter (fun n => p ∣ n ∧ p ∣ n)).card = N / p := by
  classical
  simp only [and_self]
  rw [Nat.Ioc_filter_dvd_card_eq_div]

/-! ### The comparison of `⌊N/p⌋` with `N/p` -/

lemma cast_div_le (N p : ℕ) : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le

lemma sub_one_le_cast_div (N p : ℕ) (hp : 0 < p) : (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h1 : p * (N / p) + N % p = N := Nat.div_add_mod N p
  have h2 : N % p < p := Nat.mod_lt _ hp
  have h3 : N ≤ p * (N / p) + p := by omega
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h4 : (N : ℝ) ≤ (p : ℝ) * ((N / p : ℕ) : ℝ) + p := by exact_mod_cast h3
  rw [sub_le_iff_le_add, div_le_iff₀ hp']
  nlinarith

/-! ### The variance bound -/

/-- **Turán–Kubilius, with explicit constants.** -/
theorem turanKubilius_raw (w N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ((kataiOmega w n : ℝ) - kataiPrimeRecip w) ^ 2
      ≤ (N : ℝ) * kataiPrimeRecip w
        + 2 * kataiPrimeRecip w * ((primesLe w).card : ℝ) := by
  classical
  set L := kataiPrimeRecip w with hL
  set A := primesLe w with hA
  have hppos : ∀ p ∈ A, 0 < p := fun p hp => (prime_of_mem_primesLe hp).pos
  have hLnn : 0 ≤ L := Finset.sum_nonneg fun p _ => by positivity
  -- expand the square
  have hexpand : ∑ n ∈ Finset.Ioc 0 N, ((kataiOmega w n : ℝ) - L) ^ 2
      = (∑ n ∈ Finset.Ioc 0 N, (kataiOmega w n : ℝ) ^ 2)
        - 2 * L * (∑ n ∈ Finset.Ioc 0 N, (kataiOmega w n : ℝ))
        + ((Finset.Ioc 0 N).card : ℝ) * L ^ 2 := by
    rw [Finset.sum_congr rfl (fun n _ => by ring :
      ∀ n ∈ Finset.Ioc 0 N, ((kataiOmega w n : ℝ) - L) ^ 2
        = (kataiOmega w n : ℝ) ^ 2 - 2 * L * (kataiOmega w n : ℝ) + L ^ 2)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul]
  have hcard : ((Finset.Ioc 0 N).card : ℝ) = (N : ℝ) := by simp
  -- first moment lower bound
  have hM1 : (N : ℝ) * L - ((primesLe w).card : ℝ)
      ≤ ∑ n ∈ Finset.Ioc 0 N, (kataiOmega w n : ℝ) := by
    rw [sum_kataiOmega]
    have hterm : ∀ p ∈ A, (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) :=
      fun p hp => sub_one_le_cast_div N p (hppos p hp)
    calc (N : ℝ) * L - ((primesLe w).card : ℝ)
        = ∑ p ∈ A, ((N : ℝ) / p - 1) := by
          rw [Finset.sum_sub_distrib, hL, kataiPrimeRecip, Finset.mul_sum]
          simp [hA, div_eq_mul_inv]
      _ ≤ ∑ p ∈ A, ((N / p : ℕ) : ℝ) := Finset.sum_le_sum hterm
  -- second moment upper bound
  have hM2 : (∑ n ∈ Finset.Ioc 0 N, (kataiOmega w n : ℝ) ^ 2)
      ≤ (N : ℝ) * L + (N : ℝ) * L ^ 2 := by
    rw [sum_kataiOmega_sq]
    have hterm : ∀ p ∈ A, ∑ q ∈ A,
        ((((Finset.Ioc 0 N).filter (fun n => p ∣ n ∧ q ∣ n)).card : ℕ) : ℝ)
        ≤ (N : ℝ) / p + ∑ q ∈ A, ((N : ℝ) / p) * (1 / q) := by
      intro p hp
      have hsplit : ∀ q ∈ A,
          ((((Finset.Ioc 0 N).filter (fun n => p ∣ n ∧ q ∣ n)).card : ℕ) : ℝ)
          ≤ (if p = q then (N : ℝ) / p else 0) + ((N : ℝ) / p) * (1 / q) := by
        intro q hq
        have hqpos : 0 < q := hppos q hq
        have hppos' : 0 < p := hppos p hp
        by_cases hpq : p = q
        · subst hpq
          rw [if_pos rfl, self_count_eq]
          have := cast_div_le N p
          have : (0:ℝ) ≤ ((N : ℝ) / p) * (1 / p) := by positivity
          linarith [cast_div_le N p]
        · rw [if_neg hpq, zero_add,
            joint_count_eq p q N (prime_of_mem_primesLe hp) (prime_of_mem_primesLe hq) hpq]
          have h1 : ((N / (p * q) : ℕ) : ℝ) ≤ (N : ℝ) / ((p * q : ℕ) : ℝ) := cast_div_le _ _
          have h2 : (N : ℝ) / ((p * q : ℕ) : ℝ) = ((N : ℝ) / p) * (1 / q) := by
            push_cast; field_simp
          linarith [h1, h2.le, h2.ge]
      calc ∑ q ∈ A, ((((Finset.Ioc 0 N).filter (fun n => p ∣ n ∧ q ∣ n)).card : ℕ) : ℝ)
          ≤ ∑ q ∈ A, ((if p = q then (N : ℝ) / p else 0) + ((N : ℝ) / p) * (1 / q)) :=
            Finset.sum_le_sum hsplit
        _ = (N : ℝ) / p + ∑ q ∈ A, ((N : ℝ) / p) * (1 / q) := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq A p (fun _ => (N : ℝ) / p)]
            simp [hp]
    calc ∑ p ∈ A, ∑ q ∈ A,
          ((((Finset.Ioc 0 N).filter (fun n => p ∣ n ∧ q ∣ n)).card : ℕ) : ℝ)
        ≤ ∑ p ∈ A, ((N : ℝ) / p + ∑ q ∈ A, ((N : ℝ) / p) * (1 / q)) := Finset.sum_le_sum hterm
      _ = (N : ℝ) * L + (N : ℝ) * L ^ 2 := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [hL, kataiPrimeRecip, Finset.mul_sum]
            exact Finset.sum_congr rfl fun p _ => by rw [mul_one_div]
          · have : ∑ p ∈ A, ∑ q ∈ A, ((N : ℝ) / p) * (1 / q)
                = (∑ p ∈ A, (N : ℝ) / p) * (∑ q ∈ A, (1 : ℝ) / q) := by
              rw [Finset.sum_mul_sum]
            rw [this, hL, kataiPrimeRecip]
            have hsum : ∑ p ∈ A, (N : ℝ) / p = (N : ℝ) * ∑ p ∈ A, (1 : ℝ) / p := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun p _ => by rw [mul_one_div]
            rw [hsum, hA]
            ring
  rw [hexpand, hcard]
  nlinarith [hM1, hM2, hLnn, Nat.cast_nonneg (α := ℝ) ((primesLe w).card)]


/-- **Turán–Kubilius.**  Once `2π(w) ≤ N` — which `w² ≤ N` supplies, since `π(w) ≤ w` — the
variance is at most `2·N·L(w)`. -/
theorem turanKubilius (w N : ℕ) (hN : 2 * (primesLe w).card ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, ((kataiOmega w n : ℝ) - kataiPrimeRecip w) ^ 2
      ≤ 2 * (N : ℝ) * kataiPrimeRecip w := by
  have hraw := turanKubilius_raw w N
  have hLnn : 0 ≤ kataiPrimeRecip w := Finset.sum_nonneg fun p _ => by positivity
  have hcast : 2 * (((primesLe w).card : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  nlinarith [hraw, hLnn, hcast]

/-- The `ℓ¹` form, which is what the Kátai argument consumes: the mean of `|ω_w − L|` is at most
`√(2 L(w))`. -/
theorem turanKubilius_abs (w N : ℕ) (hN : 2 * (primesLe w).card ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, |(kataiOmega w n : ℝ) - kataiPrimeRecip w|
      ≤ (N : ℝ) * Real.sqrt (2 * kataiPrimeRecip w) := by
  have hLnn : 0 ≤ kataiPrimeRecip w := Finset.sum_nonneg fun p _ => by positivity
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Ioc 0 N)
    (f := fun n => |(kataiOmega w n : ℝ) - kataiPrimeRecip w|)
  have hcard : ((Finset.Ioc 0 N).card : ℝ) = (N : ℝ) := by simp
  have habs : ∀ n : ℕ, |(kataiOmega w n : ℝ) - kataiPrimeRecip w| ^ 2
      = ((kataiOmega w n : ℝ) - kataiPrimeRecip w) ^ 2 := fun n => sq_abs _
  rw [hcard, Finset.sum_congr rfl (fun n _ => habs n)] at hcs
  have hbound := turanKubilius w N hN
  have hnn : 0 ≤ ∑ n ∈ Finset.Ioc 0 N, |(kataiOmega w n : ℝ) - kataiPrimeRecip w| :=
    Finset.sum_nonneg fun n _ => abs_nonneg _
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hsq : (∑ n ∈ Finset.Ioc 0 N, |(kataiOmega w n : ℝ) - kataiPrimeRecip w|) ^ 2
      ≤ ((N : ℝ) * Real.sqrt (2 * kataiPrimeRecip w)) ^ 2 := by
    have hs : Real.sqrt (2 * kataiPrimeRecip w) ^ 2 = 2 * kataiPrimeRecip w :=
      Real.sq_sqrt (by positivity)
    rw [mul_pow, hs]
    nlinarith [hcs, hbound, hNnn]
  have hrhs : 0 ≤ (N : ℝ) * Real.sqrt (2 * kataiPrimeRecip w) := by positivity
  nlinarith [hsq, hnn, hrhs]

end NormalNumbers.CastingOut
