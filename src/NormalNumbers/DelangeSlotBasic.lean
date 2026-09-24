import Mathlib

/-!
# `omegaLarge`: combinatorics of the large-prime omega

Support file for `DelangeSlot.lean`.  `omegaLarge P m` counts the distinct prime factors of `m`
exceeding `P`.  The two facts the Delange slot needs are:

* `omegaLarge_mul_of_coprime` — additivity on coprime arguments (so `z ^ omegaLarge P ·` is a
  multiplicative function of modulus one);
* `omegaLarge_prime_pow_mul` — the *one-prime insertion* rule
  `omegaLarge P (p ^ j * m) = omegaLarge P m + (if P < p ∧ ¬ p ∣ m then 1 else 0)`,
  which is the combinatorial engine of the Levin–Fainleib / von-Mangoldt identity
  `∑_{n ≤ N} h n * log n = z * ∑_{d ≤ N} Λ d * S (N / d) + O_P(N)` (see
  `DESIGN-2026-09-24-delange-route.md`).
-/

open Finset

namespace NormalNumbers.DelangeSlot

/-- `ω_{>P}(m)`: the number of distinct prime factors of `m` exceeding `P`. -/
def omegaLarge (P m : ℕ) : ℕ := (m.primeFactors.filter (fun p => P < p)).card

@[simp] lemma omegaLarge_zero (P : ℕ) : omegaLarge P 0 = 0 := by simp [omegaLarge]

@[simp] lemma omegaLarge_one (P : ℕ) : omegaLarge P 1 = 0 := by simp [omegaLarge]

lemma omegaLarge_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.Coprime a b)
    (P : ℕ) : omegaLarge P (a * b) = omegaLarge P a + omegaLarge P b := by
  classical
  have hdisj : Disjoint (a.primeFactors.filter (fun p => P < p))
      (b.primeFactors.filter (fun p => P < p)) :=
    (Nat.Coprime.disjoint_primeFactors h).mono (filter_subset _ _) (filter_subset _ _)
  simp only [omegaLarge, Nat.primeFactors_mul ha hb, filter_union]
  exact card_union_of_disjoint hdisj

/-- Inserting a prime power: `ω_{>P}` grows by one exactly when the prime is large and new. -/
lemma omegaLarge_prime_pow_mul {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ≠ 0) {m : ℕ} (hm : m ≠ 0)
    (P : ℕ) :
    omegaLarge P (p ^ j * m) = omegaLarge P m + (if P < p ∧ ¬ p ∣ m then 1 else 0) := by
  classical
  have hpow : (p ^ j) ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hpf : (p ^ j * m).primeFactors = insert p m.primeFactors := by
    rw [Nat.primeFactors_mul hpow hm, Nat.primeFactors_pow _ hj, hp.primeFactors]
    ext q; simp
  rw [omegaLarge, hpf, filter_insert]
  by_cases hPp : P < p
  · simp only [hPp, if_true]
    by_cases hpm : p ∣ m
    · have : p ∈ m.primeFactors.filter (fun q => P < q) := by
        simp [Nat.mem_primeFactors, hp, hpm, hm, hPp]
      rw [insert_eq_self.2 this]
      simp [omegaLarge, hpm]
    · have hnot : p ∉ m.primeFactors.filter (fun q => P < q) := by
        simp [Nat.mem_primeFactors, hpm]
      rw [card_insert_of_notMem hnot]
      simp [omegaLarge, hpm]
  · simp [hPp, omegaLarge]

end NormalNumbers.DelangeSlot
