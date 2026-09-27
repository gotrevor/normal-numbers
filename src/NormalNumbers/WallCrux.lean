/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The finite engine behind Wall's crux

`NormalNumbers.WallRational` reduces Wall's theorem to one statement: for `x` normal in
base `b` and `gcd(B,b) = 1`, the long-division state `r n = (b^n M + ⌊b^n x⌋) mod B` is
asymptotically uniform on `ℤ/B` and asymptotically independent of the digits of `x` from
position `n` on.

The attack is a shift average.  Pick `T` with `b^T ≡ 1 (mod B)`; then
`divState_shift` collapses to `r (n + T k) ≡ r n + (value of the digit block x[n, n+Tk))`,
so averaging over `k < K` replaces the unbounded-prefix quantity `r n` by a *fixed depth*
`T*K` block statistic, which `tendsto_blockAverage` evaluates.  What is left is a purely
finite estimate: a random walk on `ℤ/B` whose steps are the base-`q` digits of a uniform
`w < q^K` (`q = b^T`) equidistributes at rate `O(K^{-1/2})` in `L¹`, jointly with a tag
read off one chunk.

This file is that finite estimate, stated with no reference to normality.  The key
arithmetic input is `q ≡ 1 (mod B)`: it makes the value of a base-`q` numeral congruent
to the sum of its base-`q` digits, so the walk position after `k` steps is literally
`w / q^(K-k) mod B`, the leading-`k`-chunk value.

## Main statement

* `walk_L1_bound` : `(q^K)⁻¹ ∑_{w < q^K} |Psi w - #S/(q*B)| ≤ √(30/K)`.
-/

namespace WallCrux

open Finset

/-! ### Splitting a range along a radix -/

/-- Base-`d` splitting of a range sum. -/
theorem sum_range_mul_split {M : Type*} [AddCommMonoid M] (d : ℕ) (f : ℕ → M) (a : ℕ) :
    ∑ u ∈ range (a * d), f u = ∑ s ∈ range a, ∑ t ∈ range d, f (s * d + t) := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hd : (a + 1) * d = a * d + d := by ring
      rw [hd, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Summing a function of the quotient `w / d` over `w < a*d` counts each fiber `d` times. -/
theorem sum_range_div_fiber {M : Type*} [AddCommMonoid M] (d a : ℕ) (hd : 0 < d)
    (f : ℕ → M) :
    ∑ w ∈ range (a * d), f (w / d) = ∑ s ∈ range a, (d : ℕ) • f s := by
  rw [sum_range_mul_split d (fun w => f (w / d)) a]
  refine Finset.sum_congr rfl fun s _ => ?_
  have : ∀ t ∈ range d, f ((s * d + t) / d) = f s := by
    intro t ht
    have htd : t < d := Finset.mem_range.1 ht
    have : (s * d + t) / d = s := by
      rw [mul_comm, Nat.mul_add_div hd, Nat.div_eq_of_lt htd, Nat.add_zero]
    rw [this]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range]

/-! ### Counting a residue class in an initial segment -/

/-- Two-sided real control on natural division. -/
theorem nat_div_bounds (x B : ℕ) (hB : 0 < B) :
    (B : ℝ) * ((x / B : ℕ) : ℝ) ≤ (x : ℝ) ∧
      (x : ℝ) < (B : ℝ) * ((x / B : ℕ) : ℝ) + B := by
  have hdm := Nat.div_add_mod x B
  have hml := Nat.mod_lt x hB
  have h1 : B * (x / B) ≤ x := by
    generalize hQ : B * (x / B) = Q at hdm
    omega
  have h2 : x < B * (x / B) + B := by
    generalize hQ : B * (x / B) = Q at hdm
    omega
  refine ⟨?_, ?_⟩
  · have : ((B * (x / B) : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  · have : (x : ℝ) < ((B * (x / B) + B : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this; linarith

/-- Exact count of a residue class below `M`.  `e` is `B - 1 - m`. -/
theorem card_filter_mod_eq (B m e : ℕ) (hme : m + e + 1 = B) (M : ℕ) :
    ((range M).filter fun s => s % B = m).card = (M + e) / B := by
  have hB : 0 < B := by omega
  induction M with
  | zero =>
      simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty, Nat.zero_add]
      exact (Nat.div_eq_of_lt (by omega)).symm
  | succ M ih =>
      have hr : M % B < B := Nat.mod_lt _ hB
      have hkey : (B ∣ M + e + 1) ↔ M % B = m := by
        have h0 : (M % B + e + 1) % B = (M + e + 1) % B :=
          ((Nat.mod_modEq M B).add_right e).add_right 1
        constructor
        · intro hd
          have hd' : B ∣ M % B + e + 1 := by
            rw [Nat.dvd_iff_mod_eq_zero, h0, ← Nat.dvd_iff_mod_eq_zero]; exact hd
          obtain ⟨k, hk⟩ := hd'
          have hk2 : B * k < B * 2 := by omega
          have : k < 2 := Nat.lt_of_mul_lt_mul_left hk2
          interval_cases k <;> omega
        · intro hm
          have : M % B + e + 1 = B := by omega
          have hd' : B ∣ M % B + e + 1 := by rw [this]
          rw [Nat.dvd_iff_mod_eq_zero, ← h0, ← Nat.dvd_iff_mod_eq_zero]; exact hd'
      have hstep : (M + 1 + e) / B = (M + e) / B + (if M % B = m then 1 else 0) := by
        have h1 : M + 1 + e = (M + e) + 1 := by ring
        rw [h1, Nat.succ_div]
        congr 1
        by_cases h : M % B = m
        · rw [if_pos (hkey.2 h), if_pos h]
        · rw [if_neg (fun hd => h (hkey.1 hd)), if_neg h]
      rw [Finset.range_add_one, Finset.filter_insert, hstep]
      by_cases h : M % B = m
      · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih, if_pos h]
      · rw [if_neg h, ih, if_neg h, Nat.add_zero]

/-- The count of a shifted residue class below `M` is within `1` of `M / B`. -/
theorem card_filter_addmod_approx (B ρ j M : ℕ) (hB : 0 < B) (hj : j < B) :
    |((((range M).filter fun s => (s + ρ) % B = j).card : ℝ)) - (M : ℝ) / B| ≤ 1 := by
  classical
  set m := (j + (B - ρ % B)) % B with hm
  have hp : ρ % B < B := Nat.mod_lt _ hB
  have hmB : m < B := Nat.mod_lt _ hB
  have hmp : (m + ρ) % B = j := by
    have e1 : (m + ρ) ≡ (j + (B - ρ % B)) + ρ [MOD B] :=
      Nat.ModEq.add_right ρ (Nat.mod_modEq _ _)
    have e2 : (j + (B - ρ % B)) + ρ ≡ (j + (B - ρ % B)) + ρ % B [MOD B] :=
      Nat.ModEq.add_left _ (Nat.mod_modEq _ _).symm
    have e3 : (j + (B - ρ % B)) + ρ % B = j + B := by omega
    have e4 : (j + B) % B = j % B := Nat.add_mod_right j B
    have : (m + ρ) % B = (j + B) % B := by
      have := (e1.trans e2)
      rw [e3] at this
      exact this
    rw [this, e4, Nat.mod_eq_of_lt hj]
  have hiff : ∀ s : ℕ, ((s + ρ) % B = j) ↔ (s % B = m) := by
    intro s
    constructor
    · intro h
      have : (s + ρ) ≡ (m + ρ) [MOD B] := by
        show (s + ρ) % B = (m + ρ) % B
        rw [h, hmp]
      have := this.add_right_cancel' ρ
      calc s % B = m % B := this
        _ = m := Nat.mod_eq_of_lt hmB
    · intro h
      have : (s + ρ) ≡ (m + ρ) [MOD B] :=
        Nat.ModEq.add_right ρ (by show s % B = m % B; rw [h, Nat.mod_eq_of_lt hmB])
      show (s + ρ) % B = j
      rw [show (s + ρ) % B = (m + ρ) % B from this, hmp]
  have hset : ((range M).filter fun s => (s + ρ) % B = j)
      = ((range M).filter fun s => s % B = m) := by
    apply Finset.filter_congr
    intro s _
    simp [hiff s]
  rw [hset, card_filter_mod_eq B m (B - 1 - m) (by omega) M]
  set d := (M + (B - 1 - m)) / B with hd
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  obtain ⟨h1', h2'⟩ := nat_div_bounds (M + (B - 1 - m)) B hB
  rw [← hd] at h1' h2'
  push_cast at h1' h2'
  have he : B - 1 - m < B := by omega
  have he' : ((B - 1 - m : ℕ) : ℝ) < B := by exact_mod_cast he
  have he0 : (0 : ℝ) ≤ ((B - 1 - m : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3 : (d : ℝ) - (M : ℝ) / B = ((B : ℝ) * d - M) / B := by
    field_simp
  rw [h3, abs_div, abs_of_pos hB', div_le_one hB', abs_le]
  constructor <;> linarith

/-! ### The walk indicators -/

variable (q B : ℕ)

/-- The `k`-th indicator of the shift average: after `k` steps the walk sits at `j`, and
the tag read off chunk `k` lies in `S`. -/
noncomputable def chi (q B : ℕ) (S : Finset ℕ) (ρ j K k w : ℕ) : ℝ :=
  if (w / q ^ (K - k) + ρ) % B = j ∧ (w / q ^ (K - 1 - k)) % q ∈ S then 1 else 0

/-- The shift average. -/
noncomputable def Psi (q B : ℕ) (S : Finset ℕ) (ρ j K w : ℕ) : ℝ :=
  (K : ℝ)⁻¹ * ∑ k ∈ range K, chi q B S ρ j K k w

theorem chi_nonneg (S : Finset ℕ) (ρ j K k w : ℕ) : 0 ≤ chi q B S ρ j K k w := by
  unfold chi; split <;> norm_num

theorem chi_le_one (S : Finset ℕ) (ρ j K k w : ℕ) : chi q B S ρ j K k w ≤ 1 := by
  unfold chi; split <;> norm_num

theorem chi_sq (S : Finset ℕ) (ρ j K k w : ℕ) :
    chi q B S ρ j K k w * chi q B S ρ j K k w = chi q B S ρ j K k w := by
  unfold chi; split <;> norm_num

theorem chi_factor (S : Finset ℕ) (ρ j K k w : ℕ) :
    chi q B S ρ j K k w
      = (if (w / q ^ (K - k) + ρ) % B = j then (1 : ℝ) else 0)
        * (if (w / q ^ (K - 1 - k)) % q ∈ S then (1 : ℝ) else 0) := by
  unfold chi
  by_cases h1 : (w / q ^ (K - k) + ρ) % B = j <;>
    by_cases h2 : (w / q ^ (K - 1 - k)) % q ∈ S <;> simp [h1, h2]

/-- Counting the tag set inside one chunk. -/
theorem sum_tag (S : Finset ℕ) (hS : S ⊆ range q) :
    ∑ t ∈ range q, (if t ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
  classical
  rw [Finset.sum_ite_mem, Finset.sum_const, Finset.inter_eq_right.2 hS]
  simp

/-- **Exact first moment.** -/
theorem sum_chi_eq (S : Finset ℕ) (hS : S ⊆ range q) (hq : 2 ≤ q) (ρ j K k : ℕ)
    (hk : k < K) :
    ∑ w ∈ range (q ^ K), chi q B S ρ j K k w
      = ((q : ℝ) ^ (K - k - 1)) *
          ((((range (q ^ k)).filter fun s => (s + ρ) % B = j).card : ℝ) * (S.card : ℝ)) := by
  classical
  have hq0 : 0 < q := by omega
  set e := K - k - 1 with he
  have hKk : K - k = e + 1 := by omega
  have hKk1 : K - 1 - k = e := by omega
  have hKsplit : K = (k + 1) + e := by omega
  -- step 1: chi factors through `u = w / q^e`
  set φ : ℕ → ℝ := fun u =>
    (if (u / q + ρ) % B = j then (1 : ℝ) else 0) * (if u % q ∈ S then (1 : ℝ) else 0)
    with hφ
  have hchi : ∀ w, chi q B S ρ j K k w = φ (w / q ^ e) := by
    intro w
    rw [chi_factor, hKk, hKk1, hφ]
    congr 2
    · rw [pow_succ, ← Nat.div_div_eq_div_mul]
  -- step 2: fiber sum
  have hpow : q ^ K = q ^ (k + 1) * q ^ e := by rw [hKsplit, pow_add]
  have hfib : ∑ w ∈ range (q ^ K), chi q B S ρ j K k w
      = ((q : ℝ) ^ e) * ∑ u ∈ range (q ^ (k + 1)), φ u := by
    rw [Finset.sum_congr rfl (fun w _ => hchi w), hpow,
      sum_range_div_fiber (q ^ e) (q ^ (k + 1)) (Nat.pow_pos hq0) φ]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [nsmul_eq_mul]
    push_cast
    ring
  -- step 3: split the last chunk off
  have hsplit : ∑ u ∈ range (q ^ (k + 1)), φ u
      = (((range (q ^ k)).filter fun s => (s + ρ) % B = j).card : ℝ) * (S.card : ℝ) := by
    have hpk : q ^ (k + 1) = q ^ k * q := pow_succ q k
    rw [hpk, sum_range_mul_split q φ (q ^ k)]
    have hin : ∀ s ∈ range (q ^ k), ∑ t ∈ range q, φ (s * q + t)
        = (if (s + ρ) % B = j then (1 : ℝ) else 0) * (S.card : ℝ) := by
      intro s _
      have : ∀ t ∈ range q, φ (s * q + t)
          = (if (s + ρ) % B = j then (1 : ℝ) else 0) * (if t ∈ S then (1 : ℝ) else 0) := by
        intro t ht
        have htq : t < q := Finset.mem_range.1 ht
        have hd : (s * q + t) / q = s := by
          rw [mul_comm, Nat.mul_add_div hq0, Nat.div_eq_of_lt htq, Nat.add_zero]
        have hm : (s * q + t) % q = t := by
          rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt htq]
        rw [hφ]
        simp only [hd, hm]
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_tag q S hS]
    rw [Finset.sum_congr rfl hin, ← Finset.sum_mul, Finset.sum_ite, Finset.sum_const,
      Finset.sum_const]
    simp
  rw [hfib, hsplit]

/-- **First moment.**  The mean of `chi k` over `w < q^K` is `#S/(q*B)` up to `q^{-k}`. -/
theorem chi_mean_approx (hq : 2 ≤ q) (hB : 0 < B) (hmod : q % B = 1 % B)
    (S : Finset ℕ) (hS : S ⊆ range q) (ρ j K k : ℕ) (hj : j < B) (hk : k < K) :
    |((q ^ K : ℝ))⁻¹ * (∑ w ∈ range (q ^ K), chi q B S ρ j K k w)
        - (S.card : ℝ) / (q * B)| ≤ ((q : ℝ) ^ k)⁻¹ := by
  classical
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by positivity
  have hqR' : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  set P : ℝ := (((range (q ^ k)).filter fun s => (s + ρ) % B = j).card : ℝ) with hP
  set c : ℝ := (S.card : ℝ) with hc
  set Q : ℝ := (q : ℝ) ^ k with hQ
  have hQpos : (0 : ℝ) < Q := by positivity
  have hcq : c ≤ q := by
    rw [hc]
    have := Finset.card_le_card hS
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hPa : |P - Q / B| ≤ 1 := by
    have h := card_filter_addmod_approx B ρ j (q ^ k) hB hj
    rw [← hP] at h
    have hcast : ((q ^ k : ℕ) : ℝ) = Q := by simp [hQ]
    rw [hcast] at h
    exact h
  rw [sum_chi_eq q B S hS hq ρ j K k hk]
  have hpowR : (q : ℝ) ^ K = ((q : ℝ) ^ (k + 1)) * ((q : ℝ) ^ (K - k - 1)) := by
    rw [← pow_add]; congr 1; omega
  have hexpr : ((q : ℝ) ^ K)⁻¹ * ((q : ℝ) ^ (K - k - 1) * (P * c))
      = (c / q) * (P / Q) := by
    rw [hpowR, hQ, pow_succ]
    field_simp
  rw [hexpr]
  have habs : |P / Q - 1 / B| ≤ 1 / Q := by
    have hd : P / Q - 1 / B = (P - Q / B) / Q := by field_simp
    rw [hd, abs_div, abs_of_pos hQpos]
    gcongr
  have hsplit : (c / q) * (P / Q) - c / (q * B) = (c / q) * (P / Q - 1 / B) := by
    rw [mul_sub, mul_one_div, div_div]
  rw [hsplit, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ c / q)]
  calc (c / q) * |P / Q - 1 / B| ≤ 1 * (1 / Q) := by
        gcongr
        · rw [div_le_one hqR]; exact hcq
    _ = Q⁻¹ := by rw [one_mul, one_div]

/-- The number of `z < n` with `z + ρ ≡ j (mod B)`. -/
noncomputable def resCard (B ρ j n : ℕ) : ℝ :=
  (((range n).filter fun z => (z + ρ) % B = j).card : ℝ)

theorem resCard_approx (B ρ j n : ℕ) (hB : 0 < B) (hj : j < B) :
    |resCard B ρ j n - (n : ℝ) / B| ≤ 1 :=
  card_filter_addmod_approx B ρ j n hB hj

theorem resCard_nonneg (B ρ j n : ℕ) : 0 ≤ resCard B ρ j n := by
  unfold resCard; positivity

/-- **Exact second moment, off-diagonal.**  This is where `q ≡ 1 (mod B)` is used: it makes
the value of a base-`q` numeral congruent to the sum of its base-`q` digits, so the walk
increment between chunk `k` and chunk `k'` is the sum of the intervening chunks. -/
theorem sum_chi_pair_eq (S : Finset ℕ) (hS : S ⊆ range q) (hq : 2 ≤ q) (hB : 0 < B)
    (hmod : q % B = 1 % B) (ρ j K k k' : ℕ) (hkk : k < k') (hk' : k' < K) :
    ∑ w ∈ range (q ^ K), chi q B S ρ j K k w * chi q B S ρ j K k' w
      = ((q : ℝ) ^ (K - k' - 1)) * ((S.card : ℝ) *
          ∑ s ∈ range (q ^ k), ∑ t ∈ range q,
            ((if (s + ρ) % B = j then (1 : ℝ) else 0) * (if t ∈ S then (1 : ℝ) else 0)
              * resCard B (s + t + ρ) j (q ^ (k' - k - 1)))) := by
  classical
  have hq0 : 0 < q := by omega
  set g := k' - k - 1 with hg
  set f := K - k' - 1 with hf
  have hKk' : K - k' = f + 1 := by omega
  have hKk'1 : K - 1 - k' = f := by omega
  have hKk : K - k = f + 1 + (g + 1) := by omega
  have hKk1 : K - 1 - k = f + (g + 1) := by omega
  -- Step A: the product factors through `u = w / q^f`
  set φ : ℕ → ℝ := fun u =>
    (if (u / q ^ (g + 2) + ρ) % B = j then (1 : ℝ) else 0)
      * (if (u / q ^ (g + 1)) % q ∈ S then (1 : ℝ) else 0)
      * ((if (u / q + ρ) % B = j then (1 : ℝ) else 0)
        * (if u % q ∈ S then (1 : ℝ) else 0)) with hφ
  have hchi : ∀ w, chi q B S ρ j K k w * chi q B S ρ j K k' w = φ (w / q ^ f) := by
    intro w
    rw [chi_factor, chi_factor, hKk, hKk1, hKk', hKk'1, hφ]
    have e1 : q ^ (f + 1 + (g + 1)) = q ^ f * q ^ (g + 2) := by
      rw [← pow_add]; congr 1; omega
    have e2 : q ^ (f + (g + 1)) = q ^ f * q ^ (g + 1) := by rw [← pow_add]
    have e3 : q ^ (f + 1) = q ^ f * q := by rw [pow_succ]
    rw [e1, e2, e3, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      ← Nat.div_div_eq_div_mul]
  -- Step B: fiber sum
  have hpow : q ^ K = q ^ (k' + 1) * q ^ f := by rw [← pow_add]; congr 1; omega
  have hfib : ∑ w ∈ range (q ^ K), chi q B S ρ j K k w * chi q B S ρ j K k' w
      = ((q : ℝ) ^ f) * ∑ u ∈ range (q ^ (k' + 1)), φ u := by
    rw [Finset.sum_congr rfl (fun w _ => hchi w), hpow,
      sum_range_div_fiber (q ^ f) (q ^ (k' + 1)) (Nat.pow_pos hq0) φ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [nsmul_eq_mul]
    push_cast
    ring
  rw [hfib]
  congr 1
  -- Step C: strip the last chunk `t'`
  set ψ : ℕ → ℝ := fun y =>
    (if (y / q ^ (g + 1) + ρ) % B = j then (1 : ℝ) else 0)
      * (if (y / q ^ g) % q ∈ S then (1 : ℝ) else 0)
      * (if (y + ρ) % B = j then (1 : ℝ) else 0) with hψ
  have hC : ∑ u ∈ range (q ^ (k' + 1)), φ u = (S.card : ℝ) * ∑ y ∈ range (q ^ k'), ψ y := by
    rw [pow_succ, sum_range_mul_split q φ (q ^ k'), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hin : ∀ t' ∈ range q, φ (y * q + t')
        = ψ y * (if t' ∈ S then (1 : ℝ) else 0) := by
      intro t' ht'
      have htq : t' < q := Finset.mem_range.1 ht'
      have hd : (y * q + t') / q = y := by
        rw [mul_comm, Nat.mul_add_div hq0, Nat.div_eq_of_lt htq, Nat.add_zero]
      have hm : (y * q + t') % q = t' := by
        rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt htq]
      have hd2 : (y * q + t') / q ^ (g + 1) = y / q ^ g := by
        have : q ^ (g + 1) = q * q ^ g := by rw [pow_succ]; ring
        rw [this, ← Nat.div_div_eq_div_mul, hd]
      have hd3 : (y * q + t') / q ^ (g + 2) = y / q ^ (g + 1) := by
        have : q ^ (g + 2) = q * q ^ (g + 1) := by rw [pow_succ, pow_succ]; ring
        rw [this, ← Nat.div_div_eq_div_mul, hd]
      rw [hφ, hψ]
      simp only [hd, hm, hd2, hd3]
      ring
    rw [Finset.sum_congr rfl hin, ← Finset.mul_sum, sum_tag q S hS]
    ring
  rw [hC]
  congr 1
  -- Step D/E: split `y` into leading chunks `s`, chunk `k` (= `t`), and free chunks `z`
  have hD : ∑ y ∈ range (q ^ k'), ψ y
      = ∑ m ∈ range (q ^ (k + 1)), ∑ z ∈ range (q ^ g), ψ (m * q ^ g + z) := by
    have : q ^ k' = q ^ (k + 1) * q ^ g := by rw [← pow_add]; congr 1; omega
    rw [this, sum_range_mul_split (q ^ g) ψ (q ^ (k + 1))]
  rw [hD]
  have hE : ∑ m ∈ range (q ^ (k + 1)), ∑ z ∈ range (q ^ g), ψ (m * q ^ g + z)
      = ∑ s ∈ range (q ^ k), ∑ t ∈ range q, ∑ z ∈ range (q ^ g),
          ψ ((s * q + t) * q ^ g + z) := by
    rw [pow_succ, sum_range_mul_split q (fun m => ∑ z ∈ range (q ^ g), ψ (m * q ^ g + z))
      (q ^ k)]
  rw [hE]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t ht => ?_
  have htq : t < q := Finset.mem_range.1 ht
  -- evaluate the three conditions
  have hq1 : q ≡ 1 [MOD B] := hmod
  have hqg : q ^ g ≡ 1 [MOD B] := by
    have := hq1.pow g
    simpa using this
  have hinner : ∀ z ∈ range (q ^ g), ψ ((s * q + t) * q ^ g + z)
      = (if (s + ρ) % B = j then (1 : ℝ) else 0) * (if t ∈ S then (1 : ℝ) else 0)
        * (if (z + (s + t + ρ)) % B = j then (1 : ℝ) else 0) := by
    intro z hz
    have hzg : z < q ^ g := Finset.mem_range.1 hz
    have hd1 : ((s * q + t) * q ^ g + z) / q ^ g = s * q + t := by
      rw [mul_comm ((s * q + t)) (q ^ g), Nat.mul_add_div (Nat.pow_pos hq0),
        Nat.div_eq_of_lt hzg, Nat.add_zero]
    have hd2 : ((s * q + t) * q ^ g + z) / q ^ (g + 1) = s := by
      have hp : q ^ (g + 1) = q ^ g * q := by rw [pow_succ]
      rw [hp, ← Nat.div_div_eq_div_mul, hd1, mul_comm, Nat.mul_add_div hq0,
        Nat.div_eq_of_lt htq, Nat.add_zero]
    have hm1 : (((s * q + t) * q ^ g + z) / q ^ g) % q = t := by
      rw [hd1, mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt htq]
    have hcong : ((s * q + t) * q ^ g + z + ρ) % B = (z + (s + t + ρ)) % B := by
      have h0 : (s * q + t) * q ^ g + z + ρ ≡ (s * 1 + t) * 1 + z + ρ [MOD B] :=
        ((((hq1.mul_left s).add_right t).mul hqg).add_right z).add_right ρ
      have h1 : (s * 1 + t) * 1 + z + ρ = z + (s + t + ρ) := by ring
      rw [h1] at h0
      exact h0
    rw [hψ]
    simp only [hd2, hm1, hcong]
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, resCard]
  congr 1
  simp [Finset.sum_boole]

/-- The real-arithmetic core of the off-diagonal estimate. -/
theorem pair_arith (QQ X G Y Bp c P Sig : ℝ) (hQQ : 1 ≤ QQ) (hX : 0 < X) (hG : 0 < G)
    (hY : 0 < Y) (hBp : 1 ≤ Bp) (hc0 : 0 ≤ c) (hcq : c ≤ QQ) (hP0 : 0 ≤ P) (hPX : P ≤ X)
    (hPa : |P / X - 1 / Bp| ≤ 1 / X) (hEb : |Sig - G / Bp * (P * c)| ≤ P * c) :
    |(X * G * QQ ^ 2 * Y)⁻¹ * (Y * (c * Sig)) - (c / (QQ * Bp)) ^ 2|
      ≤ 2 * (G⁻¹ + X⁻¹) := by
  have hQQ0 : (0 : ℝ) < QQ := by linarith
  have hBp0 : (0 : ℝ) < Bp := by linarith
  set E : ℝ := Sig - G / Bp * (P * c) with hE
  have hSigE : Sig = G / Bp * (P * c) + E := by rw [hE]; ring
  have hid : (X * G * QQ ^ 2 * Y)⁻¹ * (Y * (c * Sig)) - (c / (QQ * Bp)) ^ 2
      = c ^ 2 / (Bp * QQ ^ 2) * (P / X - 1 / Bp) + c * E / (X * G * QQ ^ 2) := by
    rw [hSigE]
    field_simp
    ring
  rw [hid]
  have hb1 : |c ^ 2 / (Bp * QQ ^ 2) * (P / X - 1 / Bp)| ≤ 1 / X := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ c ^ 2 / (Bp * QQ ^ 2))]
    have hfac : c ^ 2 / (Bp * QQ ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    have hmm := mul_le_mul hfac hPa (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    linarith
  have hb2 : |c * E / (X * G * QQ ^ 2)| ≤ 1 / G := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < X * G * QQ ^ 2), abs_mul,
      abs_of_nonneg hc0, div_le_div_iff₀ (by positivity) hG]
    have hPc : P * c ≤ X * QQ := mul_le_mul hPX hcq hc0 (le_of_lt hX)
    have h1 : c * |E| ≤ QQ * (X * QQ) := by
      have hEnn : (0:ℝ) ≤ |E| := abs_nonneg _
      calc c * |E| ≤ QQ * (P * c) :=
            mul_le_mul hcq hEb hEnn (by linarith)
        _ ≤ QQ * (X * QQ) := by nlinarith
    calc c * |E| * G ≤ QQ * (X * QQ) * G := by nlinarith [hG.le]
      _ = 1 * (X * G * QQ ^ 2) := by ring
  have h1 : (0:ℝ) < X⁻¹ := by positivity
  have h2 : (0:ℝ) < G⁻¹ := by positivity
  calc |c ^ 2 / (Bp * QQ ^ 2) * (P / X - 1 / Bp) + c * E / (X * G * QQ ^ 2)|
      ≤ |c ^ 2 / (Bp * QQ ^ 2) * (P / X - 1 / Bp)| + |c * E / (X * G * QQ ^ 2)| :=
        abs_add_le _ _
    _ ≤ 1 / X + 1 / G := by linarith
    _ ≤ 2 * (G⁻¹ + X⁻¹) := by rw [one_div, one_div]; linarith

/-- **Second moment, off-diagonal.** -/
theorem chi_pair_mean_approx (hq : 2 ≤ q) (hB : 0 < B) (hmod : q % B = 1 % B)
    (S : Finset ℕ) (hS : S ⊆ range q) (ρ j K k k' : ℕ) (hj : j < B)
    (hkk : k < k') (hk' : k' < K) :
    |((q ^ K : ℝ))⁻¹ * (∑ w ∈ range (q ^ K), chi q B S ρ j K k w * chi q B S ρ j K k' w)
        - ((S.card : ℝ) / (q * B)) ^ 2|
      ≤ 2 * (((q : ℝ) ^ (k' - k - 1))⁻¹ + ((q : ℝ) ^ k)⁻¹) := by
  classical
  have hq0 : 0 < q := by omega
  have hQQ1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hc0 : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
  have hcq : (S.card : ℝ) ≤ (q : ℝ) := by
    have := Finset.card_le_card hS
    rw [Finset.card_range] at this
    exact_mod_cast this
  set g := k' - k - 1 with hg
  set f := K - k' - 1 with hf
  set A : ℕ → ℝ := fun s => (if (s + ρ) % B = j then (1 : ℝ) else 0) with hA
  set T : ℕ → ℝ := fun t => (if t ∈ S then (1 : ℝ) else 0) with hT
  set R : ℕ → ℕ → ℝ := fun s t => resCard B (s + t + ρ) j (q ^ g) with hR
  have hA0 : ∀ s, 0 ≤ A s := by intro s; rw [hA]; dsimp only; split <;> norm_num
  have hT0 : ∀ t, 0 ≤ T t := by intro t; rw [hT]; dsimp only; split <;> norm_num
  have hPsum : ∑ s ∈ range (q ^ k), A s = resCard B ρ j (q ^ k) := by
    rw [resCard, hA, Finset.sum_boole]
  have hTsum : ∑ t ∈ range q, T t = (S.card : ℝ) := sum_tag q S hS
  have hPX : resCard B ρ j (q ^ k) ≤ (q : ℝ) ^ k := by
    rw [resCard]
    have h := Finset.card_filter_le (range (q ^ k)) (fun z => (z + ρ) % B = j)
    rw [Finset.card_range] at h
    calc ((((range (q ^ k)).filter fun z => (z + ρ) % B = j).card : ℝ))
        ≤ ((q ^ k : ℕ) : ℝ) := by exact_mod_cast h
      _ = (q : ℝ) ^ k := by push_cast; ring
  have hP0 : (0 : ℝ) ≤ resCard B ρ j (q ^ k) := resCard_nonneg _ _ _ _
  have hPa : |resCard B ρ j (q ^ k) / (q : ℝ) ^ k - 1 / B| ≤ 1 / (q : ℝ) ^ k := by
    have h := resCard_approx B ρ j (q ^ k) hB hj
    have hcast : ((q ^ k : ℕ) : ℝ) = (q : ℝ) ^ k := by push_cast; ring
    rw [hcast] at h
    have hXpos : (0 : ℝ) < (q : ℝ) ^ k := by positivity
    have hd : resCard B ρ j (q ^ k) / (q : ℝ) ^ k - 1 / B
        = (resCard B ρ j (q ^ k) - (q : ℝ) ^ k / B) / (q : ℝ) ^ k := by field_simp
    rw [hd, abs_div, abs_of_pos hXpos]
    gcongr
  -- the error bound on the double sum
  have hEb : |(∑ s ∈ range (q ^ k), ∑ t ∈ range q, (A s * T t * R s t))
      - (q : ℝ) ^ g / B * (resCard B ρ j (q ^ k) * (S.card : ℝ))|
      ≤ resCard B ρ j (q ^ k) * (S.card : ℝ) := by
    have hcomb : (∑ s ∈ range (q ^ k), ∑ t ∈ range q, (A s * T t * R s t))
        = (∑ s ∈ range (q ^ k), ∑ t ∈ range q, (A s * T t * (R s t - (q : ℝ) ^ g / B)))
          + (q : ℝ) ^ g / B * (resCard B ρ j (q ^ k) * (S.card : ℝ)) := by
      have h1 : ∀ s ∈ range (q ^ k), ∑ t ∈ range q, (A s * T t * R s t)
          = (∑ t ∈ range q, (A s * T t * (R s t - (q : ℝ) ^ g / B)))
            + (q : ℝ) ^ g / B * (A s * (S.card : ℝ)) := by
        intro s _
        rw [← hTsum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun t _ => by ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
      congr 1
      rw [← Finset.mul_sum, ← Finset.sum_mul, hPsum]
    have hdiff : (∑ s ∈ range (q ^ k), ∑ t ∈ range q, (A s * T t * R s t))
        - (q : ℝ) ^ g / B * (resCard B ρ j (q ^ k) * (S.card : ℝ))
        = ∑ s ∈ range (q ^ k), ∑ t ∈ range q, (A s * T t * (R s t - (q : ℝ) ^ g / B)) := by
      rw [hcomb]; ring
    rw [hdiff]
    calc |∑ s ∈ range (q ^ k), ∑ t ∈ range q, (A s * T t * (R s t - (q : ℝ) ^ g / B))|
        ≤ ∑ s ∈ range (q ^ k), |∑ t ∈ range q, (A s * T t * (R s t - (q : ℝ) ^ g / B))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range (q ^ k), ∑ t ∈ range q, A s * T t := by
          refine Finset.sum_le_sum fun s _ => ?_
          calc |∑ t ∈ range q, (A s * T t * (R s t - (q : ℝ) ^ g / B))|
              ≤ ∑ t ∈ range q, |A s * T t * (R s t - (q : ℝ) ^ g / B)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ t ∈ range q, A s * T t := by
                refine Finset.sum_le_sum fun t _ => ?_
                rw [abs_mul, abs_of_nonneg (mul_nonneg (hA0 s) (hT0 t))]
                have hr : |R s t - (q : ℝ) ^ g / B| ≤ 1 := by
                  rw [hR]
                  dsimp only
                  have h := resCard_approx B (s + t + ρ) j (q ^ g) hB hj
                  have hcast : ((q ^ g : ℕ) : ℝ) = (q : ℝ) ^ g := by push_cast; ring
                  rw [hcast] at h
                  exact h
                have hnn := mul_nonneg (hA0 s) (hT0 t)
                nlinarith
      _ = resCard B ρ j (q ^ k) * (S.card : ℝ) := by
          rw [← hPsum, ← hTsum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm
  rw [sum_chi_pair_eq q B S hS hq hB hmod ρ j K k k' hkk hk']
  have hpowK : (q : ℝ) ^ K = (q : ℝ) ^ k * (q : ℝ) ^ g * (q : ℝ) ^ 2 * (q : ℝ) ^ f := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [hpowK]
  exact pair_arith (q : ℝ) ((q : ℝ) ^ k) ((q : ℝ) ^ g) ((q : ℝ) ^ f) (B : ℝ)
    (S.card : ℝ) (resCard B ρ j (q ^ k)) _ hQQ1 (by positivity) (by positivity)
    (by positivity) hBR hc0 hcq hP0 hPX hPa hEb

/-! ### Geometric sums -/

theorem geom_bound (r : ℝ) (h0 : 0 ≤ r) (hr : r ≤ 1 / 2) (K : ℕ) :
    ∑ k ∈ range K, r ^ k ≤ 2 := by
  have hne : r ≠ 1 := by intro h; rw [h] at hr; norm_num at hr
  rw [geom_sum_eq hne]
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have h2 : r ^ K ≥ 0 := pow_nonneg h0 _
  have hrn : r - 1 ≠ 0 := by intro h; apply hne; linarith
  have heq : (r ^ K - 1) / (r - 1) = (1 - r ^ K) / (1 - r) := by
    rw [div_eq_div_iff hrn (by linarith : (1:ℝ) - r ≠ 0)]
    ring
  rw [heq, div_le_iff₀ h1]
  nlinarith

/-- A geometric sum along any injective exponent map is bounded by `2`. -/
theorem sum_geom_inj (r : ℝ) (h0 : 0 ≤ r) (hr : r ≤ 1 / 2) (s : Finset ℕ) (e : ℕ → ℕ)
    (hinj : ∀ a ∈ s, ∀ b ∈ s, e a = e b → a = b) : ∑ a ∈ s, r ^ (e a) ≤ 2 := by
  classical
  have h1 : ∑ a ∈ s, r ^ (e a) = ∑ m ∈ s.image e, r ^ m := (Finset.sum_image hinj).symm
  set N := (s.image e).sup id + 1 with hN
  have hsub : s.image e ⊆ range N := by
    intro m hm
    have := Finset.le_sup (f := id) hm
    simp only [id] at this
    exact Finset.mem_range.2 (by omega)
  calc ∑ a ∈ s, r ^ (e a) = ∑ m ∈ s.image e, r ^ m := h1
    _ ≤ ∑ m ∈ range N, r ^ m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg h0 _
    _ ≤ 2 := geom_bound r h0 hr N

/-! ### The L² and L¹ bounds -/

/-- Row bound for the second-moment matrix: for a fixed `k`, the row sum of
`|M k k' - τ²|` is `O(1) + 2K r^k`. -/
theorem inner_sum_bound (r : ℝ) (hr0 : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (K k : ℕ)
    (F : ℕ → ℕ → ℝ) (τ2 : ℝ)
    (hdiag : |F k k - τ2| ≤ 2)
    (hlt : ∀ k', k < k' → k' < K → |F k k' - τ2| ≤ 2 * (r ^ (k' - k - 1) + r ^ k))
    (hgt : ∀ k', k' < k → |F k k' - τ2| ≤ 2 * (r ^ (k - k' - 1) + r ^ k')) :
    ∑ k' ∈ range K, |F k k' - τ2| ≤ 14 + 2 * (K : ℝ) * r ^ k := by
  classical
  have hptw : ∀ k' ∈ range K, |F k k' - τ2|
      ≤ (if k' < k then 2 * r ^ (k - k' - 1) else 0)
        + (if k' < k then 2 * r ^ k' else 0)
        + (if k = k' then (2 : ℝ) else 0)
        + (if k < k' then 2 * r ^ (k' - k - 1) else 0)
        + (if k < k' then 2 * r ^ k else 0) := by
    intro k' hk'
    have hk'K : k' < K := Finset.mem_range.1 hk'
    have hnn1 : (0:ℝ) ≤ 2 * r ^ (k - k' - 1) := by positivity
    have hnn2 : (0:ℝ) ≤ 2 * r ^ k' := by positivity
    have hnn4 : (0:ℝ) ≤ 2 * r ^ (k' - k - 1) := by positivity
    have hnn5 : (0:ℝ) ≤ 2 * r ^ k := by positivity
    rcases Nat.lt_trichotomy k' k with h | h | h
    · have hb := hgt k' h
      have e2 : ¬ (k = k') := by omega
      have e3 : ¬ (k < k') := by omega
      rw [if_pos h, if_pos h, if_neg e2, if_neg e3, if_neg e3]
      linarith
    · subst h
      simp only [lt_self_iff_false, if_false, zero_add, add_zero, if_true, ite_true,
        eq_self_iff_true]
      linarith
    · have hb := hlt k' h hk'K
      have e1 : ¬ (k' < k) := by omega
      have e2 : ¬ (k = k') := by omega
      rw [if_neg e1, if_neg e1, if_neg e2, if_pos h, if_pos h]
      linarith
  have hstep := Finset.sum_le_sum hptw
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter] at hstep
  have b1 : ∑ k' ∈ (range K).filter (fun k' => k' < k), 2 * r ^ (k - k' - 1) ≤ 4 := by
    rw [← Finset.mul_sum]
    have := sum_geom_inj r hr0 hrhalf ((range K).filter (fun k' => k' < k))
      (fun a => k - a - 1) (by
        intro a ha b hb hab
        simp only [Finset.mem_filter] at ha hb
        omega)
    linarith
  have b2 : ∑ k' ∈ (range K).filter (fun k' => k' < k), 2 * r ^ k' ≤ 4 := by
    rw [← Finset.mul_sum]
    have := sum_geom_inj r hr0 hrhalf ((range K).filter (fun k' => k' < k))
      (fun a => a) (by intro a _ b _ hab; exact hab)
    linarith
  have b3 : ∑ _k' ∈ (range K).filter (fun k' => k = k'), (2 : ℝ) ≤ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((range K).filter (fun k' => k = k')).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      omega
    have hcR : (((range K).filter (fun k' => k = k')).card : ℝ) ≤ 1 := by exact_mod_cast hc
    nlinarith
  have b4 : ∑ k' ∈ (range K).filter (fun k' => k < k'), 2 * r ^ (k' - k - 1) ≤ 4 := by
    rw [← Finset.mul_sum]
    have := sum_geom_inj r hr0 hrhalf ((range K).filter (fun k' => k < k'))
      (fun a => a - k - 1) (by
        intro a ha b hb hab
        simp only [Finset.mem_filter] at ha hb
        omega)
    linarith
  have b5 : ∑ _k' ∈ (range K).filter (fun k' => k < k'), 2 * r ^ k ≤ 2 * (K : ℝ) * r ^ k := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((range K).filter (fun k' => k < k')).card ≤ K :=
      le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])
    have hcR : (((range K).filter (fun k' => k < k')).card : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hc
    have hrk : (0:ℝ) ≤ r ^ k := by positivity
    nlinarith
  linarith

/-- The numeric endgame: the centered second moment of a shift average is `O(1/K)` once
the first and second moments are controlled. -/
theorem l2_from_moments (r : ℝ) (hr0 : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (K : ℕ) (hK : 0 < K)
    (m : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hm : ∀ k ∈ range K, |m k - τ| ≤ r ^ k)
    (hsymm : ∀ k k', M k k' = M k' k)
    (hdiag : ∀ k, |M k k - τ ^ 2| ≤ 2)
    (hpair : ∀ k k', k < k' → k' < K → |M k k' - τ ^ 2| ≤ 2 * (r ^ (k' - k - 1) + r ^ k)) :
    (K : ℝ)⁻¹ ^ 2 * (∑ k ∈ range K, ∑ k' ∈ range K, M k k')
      - (2 * τ * (K : ℝ)⁻¹) * (∑ k ∈ range K, m k) + τ ^ 2 ≤ 30 / K := by
  classical
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKR
  -- centered form
  have hcen : (K : ℝ)⁻¹ ^ 2 * (∑ k ∈ range K, ∑ k' ∈ range K, M k k')
        - (2 * τ * (K : ℝ)⁻¹) * (∑ k ∈ range K, m k) + τ ^ 2
      = (K : ℝ)⁻¹ ^ 2 * (∑ k ∈ range K, ∑ k' ∈ range K, (M k k' - τ ^ 2))
        - (2 * τ * (K : ℝ)⁻¹) * (∑ k ∈ range K, (m k - τ)) := by
    have h1 : ∑ k ∈ range K, ∑ k' ∈ range K, (M k k' - τ ^ 2)
        = (∑ k ∈ range K, ∑ k' ∈ range K, M k k') - (K : ℝ) ^ 2 * τ ^ 2 := by
      have hin : ∀ k, ∑ k' ∈ range K, (M k k' - τ ^ 2)
          = (∑ k' ∈ range K, M k k') - (K : ℝ) * τ ^ 2 := by
        intro k
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.sum_congr rfl (fun k _ => hin k), Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      ring
    have h2 : ∑ k ∈ range K, (m k - τ) = (∑ k ∈ range K, m k) - (K : ℝ) * τ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h1, h2]
    field_simp
    ring
  rw [hcen]
  have hinner : ∀ k ∈ range K, ∑ k' ∈ range K, |M k k' - τ ^ 2| ≤ 14 + 2 * (K : ℝ) * r ^ k := by
    intro k hk
    have hkK : k < K := Finset.mem_range.1 hk
    refine inner_sum_bound r hr0 hrhalf K k M (τ ^ 2) (hdiag k) (fun k' h h' => hpair k k' h h')
      (fun k' h => ?_)
    rw [hsymm k k']
    exact hpair k' k h hkK
  have hA : |∑ k ∈ range K, ∑ k' ∈ range K, (M k k' - τ ^ 2)| ≤ 18 * (K : ℝ) := by
    calc |∑ k ∈ range K, ∑ k' ∈ range K, (M k k' - τ ^ 2)|
        ≤ ∑ k ∈ range K, |∑ k' ∈ range K, (M k k' - τ ^ 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range K, (14 + 2 * (K : ℝ) * r ^ k) :=
          Finset.sum_le_sum fun k hk =>
            le_trans (Finset.abs_sum_le_sum_abs _ _) (hinner k hk)
      _ ≤ 18 * (K : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← Finset.mul_sum]
          have hg := geom_bound r hr0 hrhalf K
          nlinarith
  have hBq : |∑ k ∈ range K, (m k - τ)| ≤ 2 := by
    calc |∑ k ∈ range K, (m k - τ)| ≤ ∑ k ∈ range K, |m k - τ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range K, r ^ k := Finset.sum_le_sum hm
      _ ≤ 2 := geom_bound r hr0 hrhalf K
  have hKi : (0:ℝ) < (K : ℝ)⁻¹ := by positivity
  have h1 : (K : ℝ)⁻¹ ^ 2 * (∑ k ∈ range K, ∑ k' ∈ range K, (M k k' - τ ^ 2))
      ≤ (K : ℝ)⁻¹ ^ 2 * (18 * (K : ℝ)) := by
    have hle := le_abs_self (∑ k ∈ range K, ∑ k' ∈ range K, (M k k' - τ ^ 2))
    have hp : (0:ℝ) ≤ (K : ℝ)⁻¹ ^ 2 := by positivity
    nlinarith
  have h2 : -((2 * τ * (K : ℝ)⁻¹) * (∑ k ∈ range K, (m k - τ))) ≤ (2 * 1 * (K : ℝ)⁻¹) * 2 := by
    have hn := neg_abs_le (∑ k ∈ range K, (m k - τ))
    have hp : (0:ℝ) ≤ 2 * τ * (K : ℝ)⁻¹ := by positivity
    nlinarith
  have hlast : (K : ℝ)⁻¹ ^ 2 * (18 * (K : ℝ)) + (2 * 1 * (K : ℝ)⁻¹) * 2 ≤ 30 / K := by
    have he : (K : ℝ)⁻¹ ^ 2 * (18 * (K : ℝ)) = 18 * (K : ℝ)⁻¹ := by field_simp
    rw [he, div_eq_mul_inv]
    nlinarith
  linarith

/-- **L² bound.** -/
theorem walk_L2_bound (hq : 2 ≤ q) (hB : 0 < B) (hmod : q % B = 1 % B)
    (S : Finset ℕ) (hS : S ⊆ range q) (ρ j K : ℕ) (hj : j < B) (hK : 0 < K) :
    ((q ^ K : ℝ))⁻¹ * ∑ w ∈ range (q ^ K),
        (Psi q B S ρ j K w - (S.card : ℝ) / (q * B)) ^ 2 ≤ 30 / K := by
  classical
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by positivity
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  set r : ℝ := (q : ℝ)⁻¹ with hrdef
  have hr0 : (0 : ℝ) ≤ r := by rw [hrdef]; positivity
  have hrhalf : r ≤ 1 / 2 := by
    rw [hrdef, inv_le_comm₀ hqR (by norm_num)]
    linarith
  have hrpow : ∀ n : ℕ, ((q : ℝ) ^ n)⁻¹ = r ^ n := by intro n; rw [hrdef, inv_pow]
  set Z : ℝ := (q : ℝ) ^ K with hZdef
  have hZ : (0 : ℝ) < Z := by rw [hZdef]; positivity
  have hZcast : ((q ^ K : ℕ) : ℝ) = Z := by rw [hZdef]; push_cast; ring
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  set τ : ℝ := (S.card : ℝ) / (q * B) with hτ
  have hτ0 : (0 : ℝ) ≤ τ := by rw [hτ]; positivity
  have hcq : (S.card : ℝ) ≤ (q : ℝ) := by
    have := Finset.card_le_card hS
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hτ1 : τ ≤ 1 := by
    rw [hτ, div_le_one (by positivity)]
    nlinarith
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  set m : ℕ → ℝ := fun k => Z⁻¹ * ∑ w ∈ range (q ^ K), chi q B S ρ j K k w with hmdef
  set M : ℕ → ℕ → ℝ :=
    fun k k' => Z⁻¹ * ∑ w ∈ range (q ^ K), chi q B S ρ j K k w * chi q B S ρ j K k' w
    with hMdef
  have hpt : ∀ w, (Psi q B S ρ j K w - τ) ^ 2
      = (K : ℝ)⁻¹ ^ 2 * (∑ k ∈ range K, ∑ k' ∈ range K,
            chi q B S ρ j K k w * chi q B S ρ j K k' w)
        - (2 * τ * (K : ℝ)⁻¹) * (∑ k ∈ range K, chi q B S ρ j K k w) + τ ^ 2 := by
    intro w
    have hsq : (∑ k ∈ range K, chi q B S ρ j K k w) ^ 2
        = ∑ k ∈ range K, ∑ k' ∈ range K,
            chi q B S ρ j K k w * chi q B S ρ j K k' w := by
      rw [sq, Finset.sum_mul_sum]
    rw [Psi, ← hsq]
    ring
  set Tr : ℝ := ∑ w ∈ range (q ^ K), ∑ k ∈ range K, ∑ k' ∈ range K,
      chi q B S ρ j K k w * chi q B S ρ j K k' w with hTr
  set Db : ℝ := ∑ w ∈ range (q ^ K), ∑ k ∈ range K, chi q B S ρ j K k w with hDb
  have hsum : ∑ w ∈ range (q ^ K), (Psi q B S ρ j K w - τ) ^ 2
      = (K : ℝ)⁻¹ ^ 2 * Tr - (2 * τ * (K : ℝ)⁻¹) * Db + Z * τ ^ 2 := by
    rw [Finset.sum_congr rfl (fun w _ => hpt w), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, hZcast, hTr, hDb]
  have hD1 : Z⁻¹ * Tr = ∑ k ∈ range K, ∑ k' ∈ range K, M k k' := by
    have hswap1 : Tr = ∑ k ∈ range K, ∑ k' ∈ range K, ∑ w ∈ range (q ^ K),
          chi q B S ρ j K k w * chi q B S ρ j K k' w := by
      rw [hTr, Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
    rw [hswap1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
  have hD2 : Z⁻¹ * Db = ∑ k ∈ range K, m k := by
    rw [hDb, Finset.sum_comm, Finset.mul_sum]
  have hexp : Z⁻¹ * ∑ w ∈ range (q ^ K), (Psi q B S ρ j K w - τ) ^ 2
      = (K : ℝ)⁻¹ ^ 2 * (∑ k ∈ range K, ∑ k' ∈ range K, M k k')
        - (2 * τ * (K : ℝ)⁻¹) * (∑ k ∈ range K, m k) + τ ^ 2 := by
    rw [hsum, ← hD1, ← hD2]
    field_simp
  -- moment inputs
  have hmk : ∀ k ∈ range K, |m k - τ| ≤ r ^ k := by
    intro k hk
    have hkK : k < K := Finset.mem_range.1 hk
    have h := chi_mean_approx q B hq hB hmod S hS ρ j K k hj hkK
    rw [← hrpow k]
    exact h
  have hMsym : ∀ k k', M k k' = M k' k := by
    intro k k'
    rw [hMdef]
    dsimp only
    congr 1
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have hMlt : ∀ k k', k < k' → k' < K →
      |M k k' - τ ^ 2| ≤ 2 * (r ^ (k' - k - 1) + r ^ k) := by
    intro k k' hkk hk'
    have h := chi_pair_mean_approx q B hq hB hmod S hS ρ j K k k' hj hkk hk'
    rw [← hrpow (k' - k - 1), ← hrpow k]
    exact h
  have hmk1 : ∀ k, |m k| ≤ 1 := by
    intro k
    rw [hmdef]
    dsimp only
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < Z⁻¹)]
    have hs0 : (0 : ℝ) ≤ ∑ w ∈ range (q ^ K), chi q B S ρ j K k w :=
      Finset.sum_nonneg fun w _ => chi_nonneg q B S ρ j K k w
    have hsZ : ∑ w ∈ range (q ^ K), chi q B S ρ j K k w ≤ Z := by
      calc ∑ w ∈ range (q ^ K), chi q B S ρ j K k w
          ≤ ∑ _w ∈ range (q ^ K), (1 : ℝ) :=
            Finset.sum_le_sum fun w _ => chi_le_one q B S ρ j K k w
        _ = Z := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, hZcast]
    rw [abs_of_nonneg hs0, inv_mul_le_one₀ hZ]
    exact hsZ
  have hMdiag : ∀ k, |M k k - τ ^ 2| ≤ 2 := by
    intro k
    have heq : M k k = m k := by
      rw [hMdef, hmdef]
      dsimp only
      congr 1
      exact Finset.sum_congr rfl fun w _ => chi_sq q B S ρ j K k w
    rw [heq]
    have h1 := hmk1 k
    have h3 : (0 : ℝ) ≤ τ ^ 2 := by positivity
    have h2 : τ ^ 2 ≤ 1 := by nlinarith
    calc |m k - τ ^ 2| ≤ |m k| + |τ ^ 2| := abs_sub _ _
      _ ≤ 1 + 1 := by rw [abs_of_nonneg h3]; linarith
      _ = 2 := by norm_num
  rw [hexp]
  exact l2_from_moments r hr0 hrhalf K hK m M τ hτ0 hτ1 hmk hMsym hMdiag hMlt

/-- **The finite engine.**  The shift average of the walk indicator is within
`√(30/K)` of its mean value `#S/(q B)`, in `L¹` over a uniform `w < q^K`, uniformly in
the starting state `ρ` and the target state `j`. -/
theorem walk_L1_bound (hq : 2 ≤ q) (hB : 0 < B) (hmod : q % B = 1 % B)
    (S : Finset ℕ) (hS : S ⊆ range q) (ρ j K : ℕ) (hj : j < B) (hK : 0 < K) :
    ((q ^ K : ℝ))⁻¹ * ∑ w ∈ range (q ^ K), |Psi q B S ρ j K w - (S.card : ℝ) / (q * B)|
      ≤ Real.sqrt (30 / K) := by
  classical
  have hq0 : 0 < q := by omega
  have hZ : (0 : ℝ) < (q : ℝ) ^ K := by positivity
  have hZcast : ((q ^ K : ℕ) : ℝ) = (q : ℝ) ^ K := by push_cast; ring
  set τ : ℝ := (S.card : ℝ) / (q * B) with hτ
  set A : ℝ := ∑ w ∈ range (q ^ K), |Psi q B S ρ j K w - τ| with hA
  have hA0 : (0 : ℝ) ≤ A := Finset.sum_nonneg fun w _ => abs_nonneg _
  have hnn : (0 : ℝ) ≤ ((q : ℝ) ^ K)⁻¹ * A := by positivity
  have hcs : A ^ 2 ≤ ((q : ℝ) ^ K) * ∑ w ∈ range (q ^ K), (Psi q B S ρ j K w - τ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := range (q ^ K))
      (f := fun w => |Psi q B S ρ j K w - τ|)
    rw [Finset.card_range, hZcast] at h
    have hsq : ∀ w, |Psi q B S ρ j K w - τ| ^ 2 = (Psi q B S ρ j K w - τ) ^ 2 := by
      intro w; rw [sq_abs]
    rw [Finset.sum_congr rfl (fun w _ => hsq w)] at h
    exact h
  have hL2 := walk_L2_bound q B hq hB hmod S hS ρ j K hj hK
  rw [← hτ] at hL2
  have hsq2 : (((q : ℝ) ^ K)⁻¹ * A) ^ 2 ≤ 30 / K := by
    have hstep : (((q : ℝ) ^ K)⁻¹ * A) ^ 2
        = ((q : ℝ) ^ K)⁻¹ * (((q : ℝ) ^ K)⁻¹ * A ^ 2) := by ring
    rw [hstep]
    have hinner : ((q : ℝ) ^ K)⁻¹ * A ^ 2
        ≤ ∑ w ∈ range (q ^ K), (Psi q B S ρ j K w - τ) ^ 2 := by
      rw [inv_mul_le_iff₀ hZ]
      exact hcs
    calc ((q : ℝ) ^ K)⁻¹ * (((q : ℝ) ^ K)⁻¹ * A ^ 2)
        ≤ ((q : ℝ) ^ K)⁻¹ * ∑ w ∈ range (q ^ K), (Psi q B S ρ j K w - τ) ^ 2 := by
          have : (0:ℝ) ≤ ((q : ℝ) ^ K)⁻¹ := by positivity
          exact mul_le_mul_of_nonneg_left hinner this
      _ ≤ 30 / K := hL2
  calc ((q : ℝ) ^ K)⁻¹ * A = Real.sqrt ((((q : ℝ) ^ K)⁻¹ * A) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (30 / K) := Real.sqrt_le_sqrt hsq2

end WallCrux
