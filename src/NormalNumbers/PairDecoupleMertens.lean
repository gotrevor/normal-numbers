/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PairDecoupleElliott
import NormalNumbers.G4MediumPrimes

/-!
# The MEAN of `ω` along an arithmetic progression

The truncation depth of `PairDecoupleElliott` is currently pinned by the *pointwise* bound
`ω(m) ≤ log₂ m`, which forces `K(R) ≍ log_b log R`.  The correct input is the *mean*
`Σ_{m ≤ X} ω(m) ≪ X log log X`, which buys `K(R) ≍ log_b log log R` and so turns the leaf
`MultiElliott` into a `log log log R`-point statement.

This file proves the mean bound in the form the leaf needs — along the arithmetic progression
`i ↦ a·i + e`, uniformly in the offset `e`:

`∑_{i<R} ω(a i + e) ≤ R·(∑_{p ≤ y} 1/p) + π(y) + R·ω(a) + R·log_y(aR+e)`.

The three error terms are: the `+1` per prime in the count of `i` in a residue class
(`card_filter_dvd_le`); the primes dividing the modulus `a`, which can divide *every* term and
are counted by `ω(a)` (a constant for us, since `a = p·Q` with `p, Q` fixed); and the primes
above the cut `y`, of which each single term has at most `log_y` many
(`card_largePrimeFactors_le`).  Feeding `sum_inv_primes_Ioc_le` (dyadic Chebyshev, already in the
tree) into the first term at `y = R` gives the `log log R` shape — `sum_omegaNat_AP_le_logLog`.
-/

open Finset NormalNumbers.CastingOut

namespace NormalNumbers.PairDecouple

/-! ### Counting the terms of a progression in a residue class -/

/-- **A prime coprime to the modulus hits at most `R/p + 1` terms.**  The solutions of
`p ∣ a i + e` in `i < R` are a single residue class mod `p`, so at most one lies in each block
`[kp, (k+1)p)`; the map `i ↦ i / p` is injective on them. -/
lemma card_filter_dvd_le (p a e R : ℕ) (hp : p.Prime) (hpa : ¬ p ∣ a) :
    #{i ∈ range R | p ∣ a * i + e} ≤ R / p + 1 := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn (t := range (R / p + 1)) (fun i => i / p) ?_ ?_) ?_
  · intro i hi
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range, Finset.mem_coe] at hi ⊢
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hi.1.le)
  · intro i hi j hj hij
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hi hj
    -- `p ∣ a (i − j)` and `p ∤ a`, so `p ∣ i − j`; but `i, j` share a block, so `|i − j| < p`.
    have key : ∀ u v : ℕ, u / p = v / p → p ∣ a * u + e → p ∣ a * v + e → v ≤ u → u = v := by
      intro u v huv hu hv hvu
      have hdvd : p ∣ a * (u - v) := by
        have : p ∣ (a * u + e) - (a * v + e) := Nat.dvd_sub hu hv
        have heq : (a * u + e) - (a * v + e) = a * (u - v) := by
          rw [Nat.mul_sub]; omega
        rwa [heq] at this
      have hdv : p ∣ u - v := ((Nat.Prime.dvd_mul hp).mp hdvd).resolve_left hpa
      have hlt : u - v < p := by
        have hu' := Nat.div_add_mod u p
        have hv' := Nat.div_add_mod v p
        have hmu := Nat.mod_lt u hp.pos
        have hmv := Nat.mod_lt v hp.pos
        rw [huv] at hu'
        omega
      have : u - v = 0 := by
        rcases Nat.eq_zero_or_pos (u - v) with h | h
        · exact h
        · exact absurd (Nat.le_of_dvd h hdv) (by omega)
      omega
    rcases le_total j i with h | h
    · exact key i j hij hi.2 hj.2 h
    · exact (key j i hij.symm hj.2 hi.2 h).symm
  · simp

/-- A prime dividing the modulus can divide every term. -/
lemma card_filter_dvd_le_card (p a e R : ℕ) :
    #{i ∈ range R | p ∣ a * i + e} ≤ R := by
  exact le_trans (Finset.card_filter_le _ _) (by simp)

/-! ### The primes above the cut -/

/-- **At most `log_y m` prime factors exceed `y`.**  Their product divides `m` and each exceeds
`y`, so `y ^ card ≤ m`. -/
lemma card_largePrimeFactors_le (m y : ℕ) (hm : m ≠ 0) (hy : 2 ≤ y) :
    #{p ∈ m.primeFactors | ¬ p ≤ y} ≤ Nat.log y m := by
  classical
  set S := {p ∈ m.primeFactors | ¬ p ≤ y} with hS
  refine Nat.le_log_of_pow_le (by omega) ?_
  have hprod : ∏ p ∈ S, p ∣ m :=
    dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
      (Nat.prod_primeFactors_dvd m)
  have h1 : y ^ #S ≤ ∏ p ∈ S, p := by
    refine Finset.pow_card_le_prod _ _ _ ?_
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    omega
  exact h1.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hprod)

/-! ### The small primes, summed over the progression -/

/-- `ω(m)` splits at the cut `y`, and the small part is counted by divisibility tests over
`primesBelow (y+1)`. -/
lemma omegaNat_le_split (m y : ℕ) (hm : m ≠ 0) (hy : 2 ≤ y) :
    omegaNat m ≤ #{p ∈ Nat.primesBelow (y + 1) | p ∣ m} + Nat.log y m := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := m.primeFactors) (p := fun p => p ≤ y)
  have hsub : {p ∈ m.primeFactors | p ≤ y} ⊆ {p ∈ Nat.primesBelow (y + 1) | p ∣ m} := by
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
    rw [Finset.mem_filter, Nat.mem_primesBelow]
    exact ⟨⟨by omega, hp.1.1⟩, hp.1.2.1⟩
  have h1 := Finset.card_le_card hsub
  have h2 := card_largePrimeFactors_le m y hm hy
  rw [omegaNat]
  omega

/-! ### The mean bound -/

/-- Double counting: the small prime factors of the terms of a progression, summed. -/
lemma sum_card_filter_dvd (a e R y : ℕ) :
    ∑ i ∈ range R, #{p ∈ Nat.primesBelow (y + 1) | p ∣ a * i + e}
      = ∑ p ∈ Nat.primesBelow (y + 1), #{i ∈ range R | p ∣ a * i + e} := by
  classical
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- **The mean of `ω` along an arithmetic progression.**  For every cut `y ≥ 2`,

`∑_{i<R} ω(a i + e) ≤ R·∑_{p ≤ y} 1/p + π(y) + R·ω(a) + R·log_y(a R + e)`.

The three error terms after the main one are the rounding in the residue count, the primes
dividing the modulus `a` (a constant for a fixed progression), and the primes above the cut. -/
theorem sum_omegaNat_AP_le (a e R y : ℕ) (ha : a ≠ 0) (he : 0 < e) (hy : 2 ≤ y) :
    ∑ i ∈ range R, (omegaNat (a * i + e) : ℝ)
      ≤ (R : ℝ) * (∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ)⁻¹)
        + (#(Nat.primesBelow (y + 1)) : ℝ)
        + (R : ℝ) * (omegaNat a : ℝ)
        + (R : ℝ) * (Nat.log y (a * R + e) : ℝ) := by
  classical
  set PB := Nat.primesBelow (y + 1) with hPB
  -- Step 1: pointwise split
  have hstep : ∀ i ∈ range R, (omegaNat (a * i + e) : ℝ)
      ≤ (#{p ∈ PB | p ∣ a * i + e} : ℝ) + (Nat.log y (a * R + e) : ℝ) := by
    intro i hi
    have hiR : i < R := Finset.mem_range.mp hi
    have hne : a * i + e ≠ 0 := by omega
    have h1 := omegaNat_le_split (a * i + e) y hne hy
    have h2 : Nat.log y (a * i + e) ≤ Nat.log y (a * R + e) :=
      Nat.log_mono_right (by nlinarith [Nat.mul_le_mul_left a hiR.le])
    have : omegaNat (a * i + e) ≤ #{p ∈ PB | p ∣ a * i + e} + Nat.log y (a * R + e) := by
      rw [hPB]; omega
    exact_mod_cast this
  have hsum1 : ∑ i ∈ range R, (omegaNat (a * i + e) : ℝ)
      ≤ (∑ i ∈ range R, (#{p ∈ PB | p ∣ a * i + e} : ℝ)) + (R : ℝ) * (Nat.log y (a * R + e) : ℝ) := by
    calc ∑ i ∈ range R, (omegaNat (a * i + e) : ℝ)
        ≤ ∑ i ∈ range R, ((#{p ∈ PB | p ∣ a * i + e} : ℝ) + (Nat.log y (a * R + e) : ℝ)) :=
          Finset.sum_le_sum hstep
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Step 2: swap
  have hswap : ∑ i ∈ range R, (#{p ∈ PB | p ∣ a * i + e} : ℝ)
      = ∑ p ∈ PB, (#{i ∈ range R | p ∣ a * i + e} : ℝ) := by
    have := sum_card_filter_dvd a e R y
    rw [← hPB] at this
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
  -- Step 3: the per-prime bound
  have hper : ∀ p ∈ PB, (#{i ∈ range R | p ∣ a * i + e} : ℝ)
      ≤ (R : ℝ) * (p : ℝ)⁻¹ + 1 + (if p ∣ a then (R : ℝ) else 0) := by
    intro p hp
    rw [hPB, Nat.mem_primesBelow] at hp
    by_cases hpa : p ∣ a
    · simp only [hpa, if_pos]
      have h := card_filter_dvd_le_card p a e R
      have : (#{i ∈ range R | p ∣ a * i + e} : ℝ) ≤ (R : ℝ) := by exact_mod_cast h
      have hp0 : (0 : ℝ) < (p : ℝ) := by
        have := hp.2.pos; exact_mod_cast this
      have : (0 : ℝ) ≤ (R : ℝ) * (p : ℝ)⁻¹ := by positivity
      linarith [show (#{i ∈ range R | p ∣ a * i + e} : ℝ) ≤ (R : ℝ) by exact_mod_cast h]
    · simp only [hpa, if_neg, not_false_eq_true]
      have h := card_filter_dvd_le p a e R hp.2 hpa
      have hcast : (#{i ∈ range R | p ∣ a * i + e} : ℝ) ≤ ((R / p : ℕ) : ℝ) + 1 := by
        exact_mod_cast h
      have hdiv : ((R / p : ℕ) : ℝ) ≤ (R : ℝ) / (p : ℝ) := Nat.cast_div_le
      have : (R : ℝ) / (p : ℝ) = (R : ℝ) * (p : ℝ)⁻¹ := by rw [div_eq_mul_inv]
      linarith [hcast, hdiv]
  have hsum2 : ∑ p ∈ PB, (#{i ∈ range R | p ∣ a * i + e} : ℝ)
      ≤ (R : ℝ) * (∑ p ∈ PB, (p : ℝ)⁻¹) + (#PB : ℝ) + (R : ℝ) * (omegaNat a : ℝ) := by
    calc ∑ p ∈ PB, (#{i ∈ range R | p ∣ a * i + e} : ℝ)
        ≤ ∑ p ∈ PB, ((R : ℝ) * (p : ℝ)⁻¹ + 1 + (if p ∣ a then (R : ℝ) else 0)) :=
          Finset.sum_le_sum hper
      _ = (R : ℝ) * (∑ p ∈ PB, (p : ℝ)⁻¹) + (#PB : ℝ) + (R : ℝ) * (#{p ∈ PB | p ∣ a} : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.sum_filter]
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := by
          have hsub : {p ∈ PB | p ∣ a} ⊆ a.primeFactors := by
            intro p hp
            rw [Finset.mem_filter, hPB, Nat.mem_primesBelow] at hp
            rw [Nat.mem_primeFactors]
            exact ⟨hp.1.2, hp.2, ha⟩
          have : (#{p ∈ PB | p ∣ a} : ℝ) ≤ (omegaNat a : ℝ) := by
            have := Finset.card_le_card hsub
            rw [omegaNat]; exact_mod_cast this
          have hR : (0 : ℝ) ≤ (R : ℝ) := by positivity
          nlinarith
  linarith [hsum1, hswap ▸ hsum1, hsum2]

/-! ### The `log log` shape

Feeding the tree's dyadic Chebyshev bound (`G4.sum_inv_primes_Ioc_le`) into the main term at the
cut `y = R`. -/

open NormalNumbers.G4 in
/-- **Mertens, upper, in the form the truncation needs.**  `∑_{p ≤ R} 1/p ≤ 4 log log₂ R + 5`. -/
theorem sum_inv_primesBelow_le_logLog (R : ℕ) (hR : 2 ≤ R) :
    ∑ p ∈ Nat.primesBelow (R + 1), (p : ℝ)⁻¹ ≤ 4 * Real.log (Nat.log 2 R) + 5 := by
  classical
  have hsplit : ∑ p ∈ Nat.primesBelow (R + 1), (p : ℝ)⁻¹
      = ∑ p ∈ {p ∈ Nat.primesBelow (R + 1) | 2 < p}, (p : ℝ)⁻¹
        + ∑ p ∈ {p ∈ Nat.primesBelow (R + 1) | ¬ 2 < p}, (p : ℝ)⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hdy := sum_inv_primes_Ioc_le (R := 2) (Y := R) le_rfl hR
  have hlog2 : Nat.log 2 2 = 1 := by simpa using Nat.log_pow (by norm_num : 1 < 2) 1
  rw [hlog2] at hdy
  simp only [Nat.cast_one, Real.log_one, sub_zero] at hdy
  have hB : ∑ p ∈ {p ∈ Nat.primesBelow (R + 1) | ¬ 2 < p}, (p : ℝ)⁻¹ ≤ 1 / 2 := by
    have hsub2 : {p ∈ Nat.primesBelow (R + 1) | ¬ 2 < p} ⊆ ({2} : Finset ℕ) := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
      have := hp.1.2.two_le
      rw [Finset.mem_singleton]; omega
    calc ∑ p ∈ {p ∈ Nat.primesBelow (R + 1) | ¬ 2 < p}, (p : ℝ)⁻¹
        ≤ ∑ p ∈ ({2} : Finset ℕ), (p : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun p _ _ => by positivity)
      _ = 1 / 2 := by norm_num
  linarith

lemma card_primesBelow_le (n : ℕ) : #(Nat.primesBelow n) ≤ n := by
  classical
  calc #(Nat.primesBelow n) ≤ #(range n) :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := Finset.card_range n

/-- **The mean of `ω` along a progression is `O(log log R)`** — the input that lets the
truncation depth of `PairDecoupleElliott` drop from `log_b log R` to `log_b log log R`. -/
theorem sum_omegaNat_AP_le_logLog (a e R : ℕ) (ha : a ≠ 0) (he : 0 < e) (hR : 2 ≤ R) :
    ∑ i ∈ range R, (omegaNat (a * i + e) : ℝ)
      ≤ (R : ℝ) * (4 * Real.log (Nat.log 2 R) + 5 + (omegaNat a : ℝ)
          + (Nat.log R (a * R + e) : ℝ)) + ((R : ℝ) + 1) := by
  have h1 := sum_omegaNat_AP_le a e R R ha he hR
  have h2 := sum_inv_primesBelow_le_logLog R hR
  have h3 : (#(Nat.primesBelow (R + 1)) : ℝ) ≤ (R : ℝ) + 1 := by
    have := card_primesBelow_le (R + 1)
    have : (#(Nat.primesBelow (R + 1)) : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
  nlinarith [h1, h2, h3]

end NormalNumbers.PairDecouple
