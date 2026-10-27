/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Multiplicativity of power-divisor counts

For coprime inputs, the number of divisors whose `r`th power still divides
the input is multiplicative.  The proof uses the unique factorization of a
divisor of a coprime product into one divisor from each factor.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Finset

private theorem pow_mul_dvd_iff_of_coprime
    {m n x y r : ℕ} (hcop : m.Coprime n)
    (hx : x ∣ m) (hy : y ∣ n) :
    (x * y) ^ r ∣ m * n ↔ x ^ r ∣ m ∧ y ^ r ∣ n := by
  constructor
  · intro h
    have hpow : x ^ r * y ^ r ∣ m * n := by
      simpa [mul_pow] using h
    have hxpowMul : x ^ r ∣ m * n :=
      dvd_trans (dvd_mul_right (x ^ r) (y ^ r)) hpow
    have hxn : (x ^ r).Coprime n :=
      (hcop.coprime_dvd_left hx).pow_left r
    have hxpow : x ^ r ∣ m := hxn.dvd_of_dvd_mul_right hxpowMul
    have hypowMul : y ^ r ∣ m * n :=
      dvd_trans (dvd_mul_left (y ^ r) (x ^ r)) (by simpa [mul_comm] using hpow)
    have hym : (y ^ r).Coprime m :=
      (hcop.coprime_dvd_right hy).symm.pow_left r
    have hypow : y ^ r ∣ n := hym.dvd_of_dvd_mul_left hypowMul
    exact ⟨hxpow, hypow⟩
  · rintro ⟨hxpow, hypow⟩
    have hxy : x.Coprime y := (hcop.coprime_dvd_left hx).coprime_dvd_right hy
    have hpowcop : (x ^ r).Coprime (y ^ r) := (hxy.pow_left r).pow_right r
    have hdvd : x ^ r * y ^ r ∣ m * n :=
      hpowcop.mul_dvd_of_dvd_of_dvd
        (dvd_trans hxpow (dvd_mul_right m n))
        (dvd_trans hypow (dvd_mul_left n m))
    simpa [mul_pow] using hdvd

/-- The count of `r`th-power divisors is multiplicative on coprime inputs. -/
theorem powerDivisorCard_mul (r : ℕ) (_hr : 1 ≤ r) (m n : ℕ)
    (hcop : m.Coprime n) :
    ((m * n).divisors.filter (fun d => d ^ r ∣ m * n)).card =
      (m.divisors.filter (fun d => d ^ r ∣ m)).card *
        (n.divisors.filter (fun d => d ^ r ∣ n)).card := by
  classical
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  let s : Finset (ℕ × ℕ) := m.divisors ×ˢ n.divisors
  let pred : ℕ × ℕ → Prop := fun z => (z.1 * z.2) ^ r ∣ m * n
  have hleft :
      ((m * n).divisors.filter (fun d => d ^ r ∣ m * n)).card =
        (s.filter pred).card := by
    rw [Nat.Coprime.divisors_mul hcop, Finset.filter_map, Finset.card_map]
    change #((s.attach).filter (fun z => pred z.val)) = #(s.filter pred)
    have hattach := Finset.filter_attach pred s
    simpa only [Finset.card_map, Finset.card_attach] using congrArg Finset.card hattach
  have hfilter :
      s.filter pred =
        m.divisors.filter (fun x => x ^ r ∣ m) ×ˢ
          n.divisors.filter (fun y => y ^ r ∣ n) := by
    ext z
    simp only [s, pred, mem_filter, mem_product]
    constructor
    · rintro ⟨⟨hxdiv, hydiv⟩, hp⟩
      have hx : z.1 ∣ m := Nat.dvd_of_mem_divisors hxdiv
      have hy : z.2 ∣ n := Nat.dvd_of_mem_divisors hydiv
      obtain ⟨hxp, hyp⟩ := (pow_mul_dvd_iff_of_coprime hcop hx hy).mp hp
      exact ⟨⟨hxdiv, hxp⟩, ⟨hydiv, hyp⟩⟩
    · rintro ⟨⟨hxdiv, hxp⟩, ⟨hydiv, hyp⟩⟩
      have hx : z.1 ∣ m := Nat.dvd_of_mem_divisors hxdiv
      have hy : z.2 ∣ n := Nat.dvd_of_mem_divisors hydiv
      exact ⟨⟨hxdiv, hydiv⟩, (pow_mul_dvd_iff_of_coprime hcop hx hy).mpr ⟨hxp, hyp⟩⟩
  rw [hleft, hfilter, Finset.card_product]

end NormalNumbers.ArithmeticDisjunctivity
