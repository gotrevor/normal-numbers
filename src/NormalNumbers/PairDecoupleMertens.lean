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

/-! ### From `ω` to `omegaTail`

The carry `omegaTail b N = Σ_{k≥0} ω(N+1+k) b^{−(k+1)}` is a geometric average of shifts of `ω`,
so the mean bound transfers term by term: the shift `k` costs only `+k` in the `log_R` term, and
`Σ_k k·b^{−(k+1)} ≤ 1`. -/

private lemma tsum_half_succ' : ∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + 1) = 1 := by
  have hgeo := tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)
  calc ∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + 1)
      = ∑' k : ℕ, (1/2 : ℝ) * ((1 : ℝ) / 2) ^ k := tsum_congr fun k => by ring
    _ = (1/2 : ℝ) * ∑' k : ℕ, ((1 : ℝ) / 2) ^ k := tsum_mul_left
    _ = 1 := by rw [hgeo]; norm_num

private lemma tsum_half_succ_mul' : ∑' k : ℕ, (k : ℝ) * ((1 : ℝ) / 2) ^ (k + 1) = 1 := by
  have h := tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := (1:ℝ)/2)
    (by rw [Real.norm_eq_abs]; norm_num)
  calc ∑' k : ℕ, (k : ℝ) * ((1 : ℝ) / 2) ^ (k + 1)
      = ∑' k : ℕ, (1/2 : ℝ) * ((k : ℝ) * ((1 : ℝ) / 2) ^ k) := tsum_congr fun k => by ring
    _ = (1/2 : ℝ) * ∑' k : ℕ, (k : ℝ) * ((1 : ℝ) / 2) ^ k := tsum_mul_left
    _ = 1 := by rw [h]; norm_num

private lemma summable_affine_half (A B : ℝ) :
    Summable (fun k : ℕ => (A + B * (k : ℝ)) * ((1 : ℝ) / 2) ^ (k + 1)) := by
  have hsum1 : Summable (fun k : ℕ => A * ((1 : ℝ) / 2) ^ (k + 1)) := by
    refine Summable.mul_left _ ?_
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1) |>.congr fun k => rfl
  have hsum2 : Summable (fun k : ℕ => (k : ℝ) * ((1 : ℝ) / 2) ^ (k + 1)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by rw [Real.norm_eq_abs]; norm_num : ‖(1:ℝ)/2‖ < 1)
    have h2 := h.mul_left ((1:ℝ)/2)
    refine h2.congr fun k => ?_
    rw [pow_one]; ring
  refine (hsum1.add (hsum2.mul_left B)).congr fun k => ?_
  ring

private lemma tsum_affine_half (A B : ℝ) :
    ∑' k : ℕ, (A + B * (k : ℝ)) * ((1 : ℝ) / 2) ^ (k + 1) = A + B := by
  have hsum1 : Summable (fun k : ℕ => A * ((1 : ℝ) / 2) ^ (k + 1)) := by
    refine Summable.mul_left _ ?_
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1) |>.congr fun k => rfl
  have hsum2 : Summable (fun k : ℕ => (k : ℝ) * ((1 : ℝ) / 2) ^ (k + 1)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by rw [Real.norm_eq_abs]; norm_num : ‖(1:ℝ)/2‖ < 1)
    have h2 := h.mul_left ((1:ℝ)/2)
    refine h2.congr fun k => ?_
    rw [pow_one]; ring
  calc ∑' k : ℕ, (A + B * (k : ℝ)) * ((1 : ℝ) / 2) ^ (k + 1)
      = ∑' k : ℕ, (A * ((1 : ℝ) / 2) ^ (k + 1)
          + B * ((k : ℝ) * ((1 : ℝ) / 2) ^ (k + 1))) := tsum_congr fun k => by ring
    _ = (∑' k : ℕ, A * ((1 : ℝ) / 2) ^ (k + 1))
          + ∑' k : ℕ, B * ((k : ℝ) * ((1 : ℝ) / 2) ^ (k + 1)) :=
        (hsum1.tsum_add (hsum2.mul_left B))
    _ = A + B := by
        rw [tsum_mul_left, tsum_mul_left, tsum_half_succ', tsum_half_succ_mul']; ring

/-- The shift costs only `+k` in the `log_R` term. -/
private lemma natLog_shift_le (R X k : ℕ) (hR : 2 ≤ R) (hX : X ≠ 0) :
    Nat.log R (X + k) ≤ Nat.log R X + k := by
  set L := Nat.log R X with hL
  have h1 : X < R ^ (L + 1) := Nat.lt_pow_succ_log_self (by omega) X
  have h2 : X + k ≤ X * 2 ^ k := by
    have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    have hX1 : 1 ≤ X := by omega
    calc X + k ≤ X * (k + 1) := by nlinarith
      _ ≤ X * 2 ^ k := Nat.mul_le_mul_left X hk
  have h3 : X * 2 ^ k ≤ X * R ^ k := by
    exact Nat.mul_le_mul_left X (Nat.pow_le_pow_left hR k)
  have h4 : X + k < R ^ (L + 1 + k) := by
    calc X + k ≤ X * R ^ k := h2.trans h3
      _ < R ^ (L + 1) * R ^ k := by
          exact (Nat.mul_lt_mul_right (by positivity)).mpr h1
      _ = R ^ (L + 1 + k) := by rw [← pow_add]
  have := Nat.log_lt_of_lt_pow (show X + k ≠ 0 by omega) h4
  omega

/-- **The mean of the carry `omegaTail` along an arithmetic progression is `O(R log log R)`.** -/
theorem sum_omegaTail_AP_le (b a e R : ℕ) (hb : 2 ≤ b) (ha : a ≠ 0) (hR : 2 ≤ R) :
    ∑ i ∈ range R, NormalNumbers.CastingOut.omegaTail b (a * i + e)
      ≤ (R : ℝ) * (4 * Real.log (Nat.log 2 R) + 5 + (omegaNat a : ℝ)
            + (Nat.log R (a * R + e + 1) : ℝ)) + 2 * (R : ℝ) + 1 := by
  classical
  set M0 : ℝ := 4 * Real.log (Nat.log 2 R) + 5 + (omegaNat a : ℝ)
    + (Nat.log R (a * R + e + 1) : ℝ) with hM0
  set A : ℝ := (R : ℝ) * M0 + (R : ℝ) + 1 with hA
  -- interchange the finite sum with the series
  have hswap : ∑ i ∈ range R, NormalNumbers.CastingOut.omegaTail b (a * i + e)
      = ∑' k : ℕ, ∑ i ∈ range R,
          (omegaNat (a * i + e + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1) := by
    rw [Summable.tsum_finsetSum
      (fun i _ => NormalNumbers.CastingOut.summable_omegaTail b hb (a * i + e))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [NormalNumbers.CastingOut.omegaTail]
  rw [hswap]
  -- the majorant
  have hterm : ∀ k : ℕ, (∑ i ∈ range R, (omegaNat (a * i + e + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1))
      ≤ (A + (R : ℝ) * (k : ℝ)) * ((1 : ℝ) / 2) ^ (k + 1) := by
    intro k
    have hmean := sum_omegaNat_AP_le_logLog a (e + 1 + k) R ha (by omega) hR
    have hlog : Nat.log R (a * R + (e + 1 + k)) ≤ Nat.log R (a * R + e + 1) + k := by
      have := natLog_shift_le R (a * R + e + 1) k hR (by omega)
      have heq : a * R + (e + 1 + k) = (a * R + e + 1) + k := by omega
      rw [heq]; exact this
    have hlogR : (Nat.log R (a * R + (e + 1 + k)) : ℝ) ≤ (Nat.log R (a * R + e + 1) : ℝ) + k := by
      have : ((Nat.log R (a * R + (e + 1 + k)) : ℕ) : ℝ)
          ≤ ((Nat.log R (a * R + e + 1) + k : ℕ) : ℝ) := by exact_mod_cast hlog
      push_cast at this; linarith
    have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
    have hnum : ∑ i ∈ range R, (omegaNat (a * i + (e + 1 + k)) : ℝ) ≤ A + (R : ℝ) * (k : ℝ) := by
      rw [hA, hM0]
      nlinarith [hmean, hlogR]
    have hcongr : ∑ i ∈ range R, (omegaNat (a * i + e + 1 + k) : ℝ)
        = ∑ i ∈ range R, (omegaNat (a * i + (e + 1 + k)) : ℝ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      omega
    have hden : (0 : ℝ) < (b : ℝ) ^ (k + 1) := by
      have : (0 : ℝ) < (b : ℝ) := by
        have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
        linarith
      positivity
    have hpow : ((1 : ℝ) / 2) ^ (k + 1) = 1 / (2 : ℝ) ^ (k + 1) := by
      rw [div_pow, one_pow]
    have hden2 : (2 : ℝ) ^ (k + 1) ≤ (b : ℝ) ^ (k + 1) := by
      refine pow_le_pow_left₀ (by norm_num) ?_ _
      exact_mod_cast hb
    have hnn : 0 ≤ ∑ i ∈ range R, (omegaNat (a * i + e + 1 + k) : ℝ) :=
      Finset.sum_nonneg fun i _ => by positivity
    rw [← Finset.sum_div, hcongr, hpow]
    have hApos : 0 ≤ A + (R : ℝ) * (k : ℝ) := by
      have hnn' : 0 ≤ ∑ i ∈ range R, (omegaNat (a * i + (e + 1 + k)) : ℝ) :=
        Finset.sum_nonneg fun i _ => by positivity
      linarith [hnum, hnn']
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
    calc (∑ i ∈ range R, (omegaNat (a * i + (e + 1 + k)) : ℝ)) / (b : ℝ) ^ (k + 1)
        ≤ (A + (R : ℝ) * (k : ℝ)) / (b : ℝ) ^ (k + 1) := by gcongr
      _ ≤ (A + (R : ℝ) * (k : ℝ)) * (1 / (2 : ℝ) ^ (k + 1)) := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le h2pos hden2) hApos
  have hsumL : Summable (fun k : ℕ =>
      ∑ i ∈ range R, (omegaNat (a * i + e + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)) := by
    exact summable_sum (fun i _ => NormalNumbers.CastingOut.summable_omegaTail b hb (a * i + e))
  have hle := Summable.tsum_le_tsum hterm hsumL (summable_affine_half A (R : ℝ))
  refine hle.trans (le_of_eq ?_)
  rw [tsum_affine_half A (R : ℝ), hA]
  ring

/-! ### The asymptotic form

For `R` past the parameters of the progression the `log_R` term is bounded by `3`, because
`aR + e + 1 ≤ R² + R ≤ R³`.  So the mean of the carry along a progression is eventually
`R·(4 log log₂ R + C)` with `C` depending only on the modulus. -/

private lemma natLog_le_three (R a e : ℕ) (hR : a + e + 2 ≤ R) : Nat.log R (a * R + e + 1) ≤ 3 := by
  have hR2 : 2 ≤ R := by omega
  have hle : a * R + e + 1 ≤ R * R + R := by
    have h1 : a * R ≤ R * R := Nat.mul_le_mul_right R (by omega)
    omega
  have hlt : a * R + e + 1 < R ^ 4 := by
    have h2 : R * R + R < R ^ 4 := by
      have h3 : R ^ 4 = R * R * (R * R) := by ring
      have h4 : R * R + R ≤ R * R * 2 := by nlinarith
      have hRR : 4 ≤ R * R := by nlinarith
      have h5 : R * R * 2 < R * R * (R * R) := by nlinarith
      omega
    omega
  have := Nat.log_lt_of_lt_pow (show a * R + e + 1 ≠ 0 by omega) hlt
  omega

/-- **The mean of the carry along a progression, in closed form.**  Once `R` exceeds the
parameters of the progression the only `R`-dependence left is `log log R`.  Stated with the
hypothesis `a + e + 2 ≤ R` rather than as a filter statement, because in the application the
offset `e` carries the truncation depth `K(R)` and so moves with `R`. -/
theorem sum_omegaTail_AP_le' (b a e R : ℕ) (hb : 2 ≤ b) (ha : a ≠ 0) (hR : a + e + 2 ≤ R) :
    ∑ i ∈ range R, NormalNumbers.CastingOut.omegaTail b (a * i + e)
      ≤ (R : ℝ) * (4 * Real.log (Nat.log 2 R) + 11 + (omegaNat a : ℝ)) := by
  have hR2 : 2 ≤ R := by omega
  have h := sum_omegaTail_AP_le b a e R hb ha hR2
  have hlog : (Nat.log R (a * R + e + 1) : ℝ) ≤ 3 := by
    have := natLog_le_three R a e hR
    exact_mod_cast this
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
  nlinarith [h, hlog, hR1]

/-- The filter form, for a truncation depth that does not move with `R`. -/
theorem sum_omegaTail_AP_le_eventually (b a e : ℕ) (hb : 2 ≤ b) (ha : a ≠ 0) :
    ∀ᶠ R : ℕ in Filter.atTop, ∑ i ∈ range R,
        NormalNumbers.CastingOut.omegaTail b (a * i + e)
      ≤ (R : ℝ) * (4 * Real.log (Nat.log 2 R) + 11 + (omegaNat a : ℝ)) := by
  filter_upwards [Filter.eventually_ge_atTop (a + e + 2)] with R hRge
  exact sum_omegaTail_AP_le' b a e R hb ha hRge

/-! ### The summed phase comparison

`PairDecoupleElliott`'s comparison spends a *uniform* bound `E` on `|X i − Y i|`; the mean input
needs the sum instead.  This is the same proof with the last step left unsummed. -/

lemma abs_norm_sum_phase_sub_le_sum (t : ℝ) (R : ℕ) (X Y : ℕ → ℝ) :
    |‖∑ i ∈ range R, phase (t * X i)‖ - ‖∑ i ∈ range R, phase (t * Y i)‖|
      ≤ 4 * Real.pi * |t| * ∑ i ∈ range R, |X i - Y i| := by
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (norm_phase_sub_phase_le _ _).trans ?_
  rw [show t * X i - t * Y i = t * (X i - Y i) by ring, abs_mul]
  ring_nf
  exact le_refl _

end NormalNumbers.PairDecouple
