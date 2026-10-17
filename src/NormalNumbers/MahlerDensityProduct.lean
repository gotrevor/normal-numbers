/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerLowerBoundBackground
import NormalNumbers.AdderEscape
import Architect

/-!
# Positive-frequency product blocks fail universally

Mahler's ternary Liouville number has long zero stretches before every factorial burst.
For a fixed multiplier `m`, sample the digit frequencies immediately before those bursts:
the new stretch is all zero, so the number of `1` digits is at most the preceding factorial,
while the sampled prefix has length asymptotic to the next factorial.  Consequently digit
`1` has lower density zero in every multiple of the same irrational number.

This refutes the universal positive-lower-density strengthening of the product-block route.
-/

namespace NormalNumbers.Mahler

open Filter
open scoped Nat

/-- Some multiplier in `S` puts every base-`g` digit at positive lower density. -/
def IsDensityProductBlock (g : ℕ) (S : Finset ℕ) (X : ℝ) : Prop :=
  ∃ m ∈ S, ∀ d < g, 0 < Filter.liminf (fun n : ℕ =>
    (countOccurrences [d] ((List.range n).map (digitOf g (Int.fract ((m : ℝ) * X)))) : ℝ) / n)
    Filter.atTop

/-- Reopen condition for the product-block wall: a finite ternary multiplier set works after
restricting to irrational numbers of exponent two (expressed by failure of every
`LiouvilleWith p` condition above exponent two). -/
def DensityProductBlockExponentTwo : Prop :=
  ∃ S : Finset ℕ, ∀ X : ℝ, Irrational X →
    (∀ p : ℝ, 2 < p → ¬ LiouvilleWith p X) → IsDensityProductBlock 3 S X

private lemma self_le_three_pow (m : ℕ) : m ≤ 3 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ]
      have hp : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
      omega

lemma digitOf_bgLiouville_eq_zero_of_factorial_interval
    (m j i : ℕ) (hm : 1 ≤ m) (hj : m + 3 ≤ j)
    (hi₀ : j ! ≤ i) (hi₁ : i < (j + 1)! - (m + 1)) :
    digitOf 3 (Int.fract ((m : ℝ) * bgLiouville 3 0 1)) i = 0 := by
  have hthreshold : (m + 3)! ≤ i :=
    (Nat.factorial_le hj).trans hi₀
  obtain ⟨j', d, _hj', hj'₀, hj'₁, hdist, hd, hcell⟩ :=
    orbit_bg_mem_with_distance 3 1 0 1 m m (by norm_num) le_rfl (by norm_num)
      hm le_rfl (by simpa using self_le_three_pow m) i hthreshold
  have hiF : i < (j + 1)! := lt_of_lt_of_le hi₁ (Nat.sub_le _ _)
  have hj'eq : j' = j := by
    apply le_antisymm
    · by_contra h
      have hfac : (j + 1)! ≤ j' ! := Nat.factorial_le (by omega)
      omega
    · by_contra h
      have hfac : (j' + 1)! ≤ j ! := Nat.factorial_le (by omega)
      omega
  subst j'
  have hsubpos : 0 < (j + 1)! - (m + 1) := lt_of_le_of_lt (Nat.zero_le i) hi₁
  have hmF : m + 1 ≤ (j + 1)! := (Nat.sub_pos_iff_lt.mp hsubpos).le
  have hdist' : m + 2 ≤ d := by
    have hcancel := Nat.sub_add_cancel hmF
    omega
  have hm_pow : m < 3 ^ d := by
    have hstep : m < 3 ^ (m + 1) := by
      rw [pow_succ]
      have hp : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
      have hmle := self_le_three_pow m
      omega
    exact hstep.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hres : bgResidue 3 0 1 m d = m := by
    simp [bgResidue, Nat.mod_eq_of_lt hm_pow]
  have hm_pow' : m + 1 ≤ 3 ^ (d - 1) := by
    have hstep : m < 3 ^ (m + 1) := by
      rw [pow_succ]
      have hp : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
      have hmle := self_le_three_pow m
      omega
    exact hstep.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hnat : (m + 1) * 3 ≤ 3 ^ d := by
    have hpow : 3 ^ d = 3 ^ (d - 1) * 3 := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    rw [hpow]
    exact Nat.mul_le_mul_right 3 hm_pow'
  have hratio : ((m : ℝ) + 1) / (3 : ℝ) ^ d ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 3 ^ d) (by norm_num : (0 : ℝ) < 3)]
    norm_num
    exact_mod_cast hnat
  have horbit : orbit 3 ((m : ℝ) * bgLiouville 3 0 1) i < 1 / 3 := by
    rw [hres] at hcell
    exact hcell.2.trans_le hratio
  have hfloor : ⌊(3 : ℝ) * orbit 3 ((m : ℝ) * bgLiouville 3 0 1) i⌋ = (0 : ℤ) := by
    rw [Int.floor_eq_iff]
    have horbit0 := (orbit_mem_Ico 3 ((m : ℝ) * bgLiouville 3 0 1) i).1
    constructor <;> norm_num <;> nlinarith
  have hdigit := NormalNumbers.Adder.digitOf_eq_floor_orbit 3 (by norm_num)
    ((m : ℝ) * bgLiouville 3 0 1) i
  norm_num at hdigit
  rw [hfloor] at hdigit
  exact_mod_cast hdigit

private lemma count_one_le_factorial (m j : ℕ) (hm : 1 ≤ m) (hj : m + 3 ≤ j) :
    countOccurrences [1]
      ((List.range ((j + 1)! - (m + 1))).map
        (digitOf 3 (Int.fract ((m : ℝ) * bgLiouville 3 0 1)))) ≤ j ! := by
  rw [countOccurrences_range_map]
  calc
    _ ≤ (Finset.range (j !)).card := Finset.card_le_card (by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range, List.length_singleton] at hi
      simp only [Finset.mem_range]
      by_contra hnot
      have hi₀ : j ! ≤ i := by omega
      have hi₁ : i < (j + 1)! - (m + 1) := by omega
      have hz := digitOf_bgLiouville_eq_zero_of_factorial_interval m j i hm hj hi₀ hi₁
      have hone : digitOf 3 (Int.fract ((m : ℝ) * bgLiouville 3 0 1)) i = 1 := by
        have := hi.2.2 0 (by simp)
        simpa [MatchesAt] using this
      omega)
    _ = j ! := Finset.card_range _

private lemma count_one_le_length (s : ℕ → ℕ) (n : ℕ) :
    countOccurrences [1] ((List.range n).map s) ≤ n := by
  rw [countOccurrences_range_map]
  calc
    _ ≤ (Finset.range n).card := Finset.card_le_card (by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range, List.length_singleton] at hi
      simp only [Finset.mem_range]
      omega)
    _ = n := Finset.card_range _

lemma not_pos_liminf_digit_one_bgLiouville (m : ℕ) :
    ¬ 0 < Filter.liminf (fun n : ℕ =>
      (countOccurrences [1] ((List.range n).map
        (digitOf 3 (Int.fract ((m : ℝ) * bgLiouville 3 0 1)))) : ℝ) / n) Filter.atTop := by
  let f : ℕ → ℝ := fun n =>
    (countOccurrences [1] ((List.range n).map
      (digitOf 3 (Int.fract ((m : ℝ) * bgLiouville 3 0 1)))) : ℝ) / n
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hf1 : ∀ n, f n ≤ 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [f]
    · have hc := count_one_le_length
          (digitOf 3 (Int.fract ((m : ℝ) * bgLiouville 3 0 1))) n
      have hcR : (countOccurrences [1] ((List.range n).map
          (digitOf 3 (Int.fract ((m : ℝ) * bgLiouville 3 0 1)))) : ℝ) ≤ n := by
        exact_mod_cast hc
      dsimp only [f]
      rw [div_le_iff₀ (by exact_mod_cast hn)]
      simpa using hcR
  have hbdd : IsBoundedUnder (· ≥ ·) atTop f :=
    isBoundedUnder_of_eventually_ge (a := 0) (Eventually.of_forall hf0)
  have hcob : IsCoboundedUnder (· ≥ ·) atTop f :=
    isCoboundedUnder_ge_of_eventually_le atTop (x := 1) (Eventually.of_forall hf1)
  have hlim : Filter.liminf f atTop ≤ 0 := by
    apply (Filter.liminf_le_iff hcob hbdd).2
    intro y hy
    apply frequently_atTop.2
    intro A
    rcases eq_or_ne m 0 with rfl | hm0
    · refine ⟨A, le_rfl, ?_⟩
      have hdig : ∀ i, digitOf 3 (Int.fract ((0 : ℝ) * bgLiouville 3 0 1)) i = 0 := by
        intro i
        simp [digitOf]
      have hcount : countOccurrences [1]
          ((List.range A).map (digitOf 3 (Int.fract ((0 : ℝ) * bgLiouville 3 0 1)))) = 0 := by
        rw [countOccurrences_range_map]
        simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_range,
          List.length_singleton]
        intro i _ hi
        have hone := hi.2 0 (by simp)
        simp only [List.getD_cons_zero, Nat.add_zero] at hone
        rw [hdig i] at hone
        norm_num at hone
      have hfA : f A = 0 := by
        dsimp only [f]
        have hcount' : countOccurrences [1]
            ((List.range A).map (digitOf 3 0)) = 0 := by simpa using hcount
        simp [hcount']
      rw [hfA]
      exact hy
    · have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
      obtain ⟨J, hJ⟩ := exists_nat_gt (1 / y)
      let j := max (max (m + 3) A) J
      have hjm : m + 3 ≤ j := le_trans (le_max_left _ _) (le_max_left _ _)
      have hjA : A ≤ j := le_trans (le_max_right _ _) (le_max_left _ _)
      have hjJ : J ≤ j := le_max_right _ _
      have hjpos : 0 < j := by omega
      have hjfac : j ≤ j ! := Nat.self_le_factorial j
      have hmf : m + 1 ≤ j ! := by omega
      have hqbound : j * (j !) ≤ (j + 1)! - (m + 1) := by
        have hsub := Nat.sub_le_sub_left hmf ((j + 1)!)
        have hleft : (j + 1)! - j ! = j * (j !) := by
          calc
            (j + 1)! - j ! = (j * (j !) + j !) - j ! := by
              congr 1
              rw [Nat.factorial_succ]
              ring
            _ = j * (j !) := Nat.add_sub_cancel _ _
        rw [hleft] at hsub
        exact hsub
      let q := (j + 1)! - (m + 1)
      have hAq : A ≤ q := by
        have hjprod : j ≤ j * (j !) := Nat.le_mul_of_pos_right j (Nat.factorial_pos j)
        exact hjA.trans (hjprod.trans hqbound)
      refine ⟨q, hAq, ?_⟩
      have hjprod : j ≤ j * (j !) := Nat.le_mul_of_pos_right j (Nat.factorial_pos j)
      have hqpos : 0 < q := lt_of_lt_of_le hjpos (hjprod.trans hqbound)
      have hcount := count_one_le_factorial m j hm hjm
      have hcountR : (countOccurrences [1]
          ((List.range q).map (digitOf 3 (Int.fract ((m : ℝ) * bgLiouville 3 0 1)))) : ℝ)
          ≤ j ! := by
        exact_mod_cast hcount
      have hratio₁ : f q ≤ (j ! : ℝ) / q := by
        dsimp only [f]
        gcongr
      have hratio₂ : (j ! : ℝ) / q ≤ 1 / (j : ℝ) := by
        rw [div_le_div_iff₀ (by exact_mod_cast hqpos) (by exact_mod_cast hjpos)]
        norm_num
        exact_mod_cast (by simpa [mul_comm] using hqbound)
      have hjy : (1 : ℝ) / j < y := by
        have hJcast : (1 : ℝ) / y < j := hJ.trans_le (by exact_mod_cast hjJ)
        rw [div_lt_iff₀ (by exact_mod_cast hjpos)]
        rw [div_lt_iff₀ hy] at hJcast
        nlinarith
      exact (hratio₁.trans hratio₂).trans_lt hjy
  intro hpos
  exact (not_lt_of_ge hlim) hpos

/-- Universal positive-frequency product blocks do not exist: the ternary
Liouville witness has digit `1` at lower density zero in every multiplier. -/
@[blueprint (title := "Universal positive-frequency product blocks fail")]
theorem not_forall_isDensityProductBlock (S : Finset ℕ) :
    ∃ X : ℝ, Irrational X ∧ ¬ IsDensityProductBlock 3 S X := by
  refine ⟨bgLiouville 3 0 1, irrational_bgLiouville 3 0 1 (by norm_num) le_rfl, ?_⟩
  rintro ⟨m, _hmS, hall⟩
  exact not_pos_liminf_digit_one_bgLiouville m (hall 1 (by norm_num))

end NormalNumbers.Mahler
