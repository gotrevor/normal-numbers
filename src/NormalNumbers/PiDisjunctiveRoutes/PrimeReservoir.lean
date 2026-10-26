/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.Disjunctive
import NormalNumbers.PiBBP

/-!
# Route 2: fresh BBP prime denominators

Route 2 of three experimental routes to disjunctivity of π.
See `NormalNumbers.PiDisjunctiveRoutes` for the shared framing and evidence tiers.
-/

namespace NormalNumbers.PiDisjunctiveRoutes

open Set

/-- The part of the BBP rational head carried by prime denominators > 4n.
Such a denominator occurs only once in the four denominator families below
8n.  The odd families are 8j+1 (coefficient 4) and 8j+5 (coefficient -1).
All other terms remain in `bbpResidual`; nothing is discarded. -/
noncomputable def bbpPrimeReservoir (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (16 : ℝ) ^ (n - j) *
    ((if Nat.Prime (8 * j + 1) ∧ 4 * n < 8 * j + 1 then
        4 / (8 * (j : ℝ) + 1) else 0) -
     (if Nat.Prime (8 * j + 5) ∧ 4 * n < 8 * j + 5 then
        1 / (8 * (j : ℝ) + 5) else 0))

noncomputable def bbpResidual (n : ℕ) : ℝ :=
  (16 : ℝ) ^ n * piPartial n - bbpPrimeReservoir n

/-- The same BBP head as an exact rational, for denominator arithmetic. -/
def bbpRationalHead (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (16 : ℚ) ^ (n - j) *
    (4 / (8 * (j : ℚ) + 1) - 2 / (8 * (j : ℚ) + 4) -
      1 / (8 * (j : ℚ) + 5) - 1 / (8 * (j : ℚ) + 6))

/-- BBP numerators indexed by the residue r of the denominator 8j+r. -/
def bbpCoeff (r : ℕ) : ℤ :=
  if r = 1 then 4 else if r = 4 then -2 else if r = 5 then -1 else if r = 6 then -1 else 0

lemma bbpRationalHead_eq_sum_product (n : ℕ) :
    bbpRationalHead n = ∑ x ∈ Finset.range n ×ˢ ({1, 4, 5, 6} : Finset ℕ),
      (16 : ℚ) ^ (n - x.1) * ((bbpCoeff x.2 : ℚ) / ((8 * x.1 + x.2 : ℕ) : ℚ)) := by
  rw [Finset.sum_product, bbpRationalHead]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Finset.sum_insert, bbpCoeff]
  ring

lemma padicNorm_bbpFrac_le {p m : ℕ} [Fact p.Prime] (c : ℤ) (k : ℕ) (hm : ¬ p ∣ m) :
    padicNorm p ((16 : ℚ) ^ k * ((c : ℚ) / (m : ℚ))) ≤ 1 := by
  rw [padicNorm.mul, padicNorm.div, (padicNorm.nat_eq_one_iff m).2 hm, div_one]
  have h1 : padicNorm p ((16 : ℚ) ^ k) ≤ 1 := by
    have := padicNorm.of_nat (p := p) (16 ^ k); push_cast at this; exact this
  exact mul_le_one₀ h1 (padicNorm.nonneg _) (padicNorm.of_int c)

lemma padicNorm_le_one_of_not_dvd_den {p : ℕ} [Fact p.Prime] (q : ℚ) (h : ¬ p ∣ q.den) :
    padicNorm p q ≤ 1 := by
  rw [← Rat.num_div_den q, padicNorm.div, (padicNorm.nat_eq_one_iff _).2 h, div_one]
  exact padicNorm.of_int _

/-- Frozen elementary argument, now Lean-proved (p-adic norm).
A prime in this strip divides exactly one displayed denominator (all are
< 8n); its numerator is 4 or -1 times a power of 16, prime to p.  All
other terms are p-integral, so the pole survives in the reduced rational.
This certifies an arithmetic source, NOT independence modulo one. -/
@[blueprint (title := "Fresh BBP prime denominators survive reduction of the whole head")]
theorem fresh_prime_dvd_head_den {n p : ℕ} (hp : Nat.Prime p)
    (hlo : 4 * n < p) (hhi : p < 8 * n) (hclass : p % 8 = 1 ∨ p % 8 = 5) :
    p ∣ (bbpRationalHead n).den := by
  have := Fact.mk hp
  by_contra hden
  have hle := padicNorm_le_one_of_not_dvd_den _ hden
  set s := Finset.range n ×ˢ ({1, 4, 5, 6} : Finset ℕ)
  set F : ℕ × ℕ → ℚ := fun x =>
    (16 : ℚ) ^ (n - x.1) * ((bbpCoeff x.2 : ℚ) / ((8 * x.1 + x.2 : ℕ) : ℚ))
  have hx0 : (p / 8, p % 8) ∈ s := by
    simp only [s, Finset.mem_product, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  rw [bbpRationalHead_eq_sum_product, ← Finset.add_sum_erase _ _ hx0] at hle
  have hrest : padicNorm p (∑ x ∈ s.erase (p / 8, p % 8), F x) ≤ 1 := by
    refine padicNorm.sum_le' (hF := fun x hx => ?_) (ht := zero_le_one)
    apply padicNorm_bbpFrac_le
    simp only [s, Finset.mem_erase, Finset.mem_product, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton, ne_eq, Prod.ext_iff] at hx
    rintro ⟨c, hc⟩
    rcases c with _ | _ | c
    · omega
    · omega
    · have : 2 * p ≤ p * (c + 1 + 1) := by nlinarith
      omega
  have hpow : padicNorm p ((16 : ℚ) ^ (n - p / 8)) = 1 := by
    have := (padicNorm.nat_eq_one_iff (p := p) (16 ^ (n - p / 8))).2 (by
      intro h
      have h2 : p ∣ 2 ^ (4 * (n - p / 8)) := by rwa [pow_mul]
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
      omega)
    push_cast at this; exact this
  have hcoef : padicNorm p (bbpCoeff (p % 8) : ℚ) = 1 := by
    rw [padicNorm.int_eq_one_iff]
    rcases hclass with h | h <;> rw [h] <;> simp [bbpCoeff]
    · intro hd
      have h4 : p ∣ 4 := Int.natCast_dvd_natCast.1 (by exact_mod_cast hd)
      have := Nat.le_of_dvd (by norm_num) h4
      omega
    · intro hd
      have h1 : (p : ℤ) ∣ 1 := by simpa using hd
      have := Int.le_of_dvd one_pos h1
      have := hp.one_lt
      omega
  have hspec : padicNorm p (F (p / 8, p % 8)) = p := by
    simp only [F]
    rw [Nat.div_add_mod, padicNorm.mul, padicNorm.div, hpow, hcoef,
      padicNorm.padicNorm_p_of_prime]
    simp
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  rw [padicNorm.add_eq_max_of_ne (by rw [hspec]; linarith), hspec] at hle
  linarith [le_max_left (p : ℚ) (padicNorm p (∑ x ∈ s.erase (p / 8, p % 8), F x))]

/-- Exact split; the residual retains the whole unselected rational head. -/
theorem bbp_split (n : ℕ) :
    bbpPrimeReservoir n + bbpResidual n = (16 : ℝ) ^ n * piPartial n := by
  simp [bbpResidual]

/-- Every open rectangle in the two-torus is visited arbitrarily late.
Confidence in truth: 70%, speculative arithmetic decoupling, untested.
This is stronger than support of the sum.  Separate uniform marginals do
not suffice: a rational telescoping control can lock the sum on a diagonal.
There is no conditioning on the exact residual, which could encode n. -/
@[blueprint (title := "Fresh BBP prime denominators have joint support with the residual")]
def PiPrimeReservoirSupport : Prop :=
  ∀ a c d e : ℝ, 0 ≤ a → a < c → c ≤ 1 →
    0 ≤ d → d < e → e ≤ 1 → ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧
      Int.fract (bbpPrimeReservoir n) ∈ Ioo a c ∧
      Int.fract (bbpResidual n) ∈ Ioo d e

/-- Frozen transfer, Lean-proved.
Choose a rectangle whose sum modulo one lies strictly inside the desired
cylinder.  Hit it at n large enough that the BBP tail O(n^-2) is smaller
than the boundary margin.  The exact split then gives a genuine π hit. -/
theorem pi_disjunctive_of_primeReservoirSupport (hπ : PiBBP)
    (h : PiPrimeReservoirSupport) : IsDisjunctive 16 Real.pi := by
  intro a c ha hac hc
  set e := (c - a) / 8 with he
  have he0 : 0 < e := by rw [he]; linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (32 / (3 * e))
  obtain ⟨n, hNn, ⟨hP1, hP2⟩, ⟨hR1, hR2⟩⟩ :=
    h (a / 2 + e) (a / 2 + 2 * e) (a / 2 + e) (a / 2 + 2 * e)
      (by linarith) (by linarith) (by rw [he]; linarith)
      (by linarith) (by linarith) (by rw [he]; linarith) N
  have hT0 := piTail_ge hπ n
  have hT1 := piTail_le hπ n
  have hn : (32 / (3 * e) : ℝ) < n := lt_of_lt_of_le hN (by exact_mod_cast hNn)
  have hsmall : 64 / (3 * (8 * (n : ℝ) + 1) ^ 2) < 2 * e := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 32 / (3 * e) * (3 * e) = 32 := by field_simp
    have h2 : (n : ℝ) * (3 * e) > 32 := by nlinarith
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hpos : (0 : ℝ) < 3 / (16 * ((n : ℝ) + 1) ^ 2) := by positivity
  refine ⟨n, ?_⟩
  have hsplit : Real.pi * (16 : ℝ) ^ n =
      ((⌊bbpPrimeReservoir n⌋ + ⌊bbpResidual n⌋ : ℤ) : ℝ) +
        (Int.fract (bbpPrimeReservoir n) + Int.fract (bbpResidual n) +
          16 ^ n * piTail n) := by
    have := bbp_split n
    push_cast
    rw [Int.fract, Int.fract, piTail]
    linarith [this, show Real.pi * 16 ^ n = 16 ^ n * Real.pi by ring,
      show (16 : ℝ) ^ n * (Real.pi - piPartial n) = 16 ^ n * Real.pi - 16 ^ n * piPartial n
        by ring]
  have hfr : orbit 16 Real.pi n = Int.fract (bbpPrimeReservoir n) +
      Int.fract (bbpResidual n) + 16 ^ n * piTail n := by
    rw [orbit, Int.fract_eq_iff]
    refine ⟨by linarith, by rw [he] at *; linarith,
      ⌊bbpPrimeReservoir n⌋ + ⌊bbpResidual n⌋, ?_⟩
    push_cast at hsplit ⊢
    linarith
  rw [hfr]
  constructor <;> [linarith; (rw [he] at *; linarith)]

/-- The fresh-prime convention is tested on hand-checkable known answers. -/
example : 5 ∣ (bbpRationalHead 1).den := by decide +kernel
example : 13 ∣ (bbpRationalHead 2).den := by decide +kernel
example : 17 ∣ (bbpRationalHead 3).den := by decide +kernel

end NormalNumbers.PiDisjunctiveRoutes
