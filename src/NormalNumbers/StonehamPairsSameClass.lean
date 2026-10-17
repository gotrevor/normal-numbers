/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamPairsDistinct

/-!
# Aligned arithmetic for Stoneham pairs in one multiplicative class

When `c = g ^ s`, the entered depth is `Nat.log g n / s`.  Thus the denominator of one
cleared Stoneham family is `g ^ (s * (Nat.log g n / s))`.  This file pads that numerator by
the bounded remainder power of `g`, putting every family in the class over the common
denominator `g ^ Nat.log g n`.  This is the exact algebraic interface needed by the periodic
tail argument for literal same-class pairs.
-/

namespace NormalNumbers.StonehamPairsNormal

/-- The numerator of one `g ^ s` Stoneham family after padding it to denominator `g ^ J`. -/
def sameClassClearedFamily (b g s n J : ℕ) : ℤ :=
  stonehamClearedFamily b (g ^ s) n (J / s) *
    (g : ℤ) ^ (J - s * (J / s))

lemma sameClassClearedFamily_nonneg (b g s n J : ℕ) :
    0 ≤ sameClassClearedFamily b g s n J := by
  unfold sameClassClearedFamily stonehamClearedFamily
  positivity

/-- The finite geometric coefficient obtained when every dyadic Stoneham phase is replaced by
its common odd residue. -/
def dyadicGeom (s K : ℕ) : ℤ :=
  ∑ t ∈ Finset.range K, (2 : ℤ) ^ (s * t)

/-- A nonempty dyadic geometric coefficient is `1` modulo its first nonconstant power. -/
lemma dyadicGeom_modEq_one (s K : ℕ) (hs : 1 ≤ s) (hK : 1 ≤ K) :
    dyadicGeom s K ≡ 1 [ZMOD 2 ^ s] := by
  induction K with
  | zero => omega
  | succ K ih =>
      by_cases hK0 : K = 0
      · subst K
        simp [dyadicGeom]
      · have ih' := ih (by omega)
        have hterm : (2 : ℤ) ^ (s * K) ≡ 0 [ZMOD 2 ^ s] :=
          Int.modEq_zero_iff_dvd.mpr (pow_dvd_pow (2 : ℤ) (by
            have hKpos : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK0
            exact Nat.le_mul_of_pos_right s hKpos))
        rw [dyadicGeom, Finset.sum_range_succ]
        simpa only [dyadicGeom, add_zero] using ih'.add hterm

/-- In particular, every nonempty dyadic geometric coefficient is odd. -/
lemma not_two_dvd_dyadicGeom (s K : ℕ) (hs : 1 ≤ s) (hK : 1 ≤ K) :
    ¬ (2 : ℤ) ∣ dyadicGeom s K := by
  have hmod := (dyadicGeom_modEq_one s K hs hK).of_dvd
    (pow_dvd_pow (2 : ℤ) hs)
  intro hdvd
  have hone : (2 : ℤ) ∣ 1 := Int.modEq_zero_iff_dvd.mp
    (hmod.symm.trans (Int.modEq_zero_iff_dvd.mpr hdvd))
  norm_num at hone

/-- Valuation form of oddness. -/
lemma padicValInt_dyadicGeom_eq_zero (s K : ℕ) (hs : 1 ≤ s) (hK : 1 ≤ K) :
    padicValInt 2 (dyadicGeom s K) = 0 :=
  padicValInt.eq_zero_of_not_dvd (not_two_dvd_dyadicGeom s K hs hK)

/-- If both step sizes are at least two, their nonempty dyadic geometric coefficients add to
an integer of exact 2-adic valuation one. -/
lemma padicValInt_dyadicGeom_add_eq_one
    (s₁ s₂ K₁ K₂ : ℕ) (hs₁ : 2 ≤ s₁) (hs₂ : 2 ≤ s₂)
    (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂) :
    padicValInt 2 (dyadicGeom s₁ K₁ + dyadicGeom s₂ K₂) = 1 := by
  have hmod₁ := (dyadicGeom_modEq_one s₁ K₁ (by omega) hK₁).of_dvd
    (pow_dvd_pow (2 : ℤ) hs₁)
  have hmod₂ := (dyadicGeom_modEq_one s₂ K₂ (by omega) hK₂).of_dvd
    (pow_dvd_pow (2 : ℤ) hs₂)
  have hmod : dyadicGeom s₁ K₁ + dyadicGeom s₂ K₂ ≡ 2 [ZMOD 4] := by
    simpa using hmod₁.add hmod₂
  have hnot4 : ¬ (4 : ℤ) ∣ dyadicGeom s₁ K₁ + dyadicGeom s₂ K₂ := by
    intro hdvd
    have htwo : (4 : ℤ) ∣ 2 := Int.modEq_zero_iff_dvd.mp
      (hmod.symm.trans (Int.modEq_zero_iff_dvd.mpr hdvd))
    norm_num at htwo
  have hcore0 : dyadicGeom s₁ K₁ + dyadicGeom s₂ K₂ ≠ 0 :=
    fun hzero => hnot4 (by simp [hzero])
  have hdiv2 : (2 : ℤ) ∣ dyadicGeom s₁ K₁ + dyadicGeom s₂ K₂ := by
    have hmod2 := hmod.of_dvd (by norm_num : (2 : ℤ) ∣ 4)
    exact Int.modEq_zero_iff_dvd.mp
      (hmod2.trans (Int.modEq_zero_iff_dvd.mpr (by norm_num)))
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hlow : 1 ≤ padicValInt 2 (dyadicGeom s₁ K₁ + dyadicGeom s₂ K₂) :=
    ((padicValInt_dvd_iff 1 _).mp (by simpa using hdiv2)).resolve_left hcore0
  have hupp : ¬ 2 ≤ padicValInt 2 (dyadicGeom s₁ K₁ + dyadicGeom s₂ K₂) := by
    intro hle
    apply hnot4
    simpa using (padicValInt_dvd_iff 2 _).mpr (Or.inr hle)
  omega

/-- When one class power is one and the common depth is a multiple of `s`, the two geometric
coefficients add to `2^s` times the sparse one. -/
lemma dyadicGeom_one_mul_add (s K : ℕ) :
    dyadicGeom 1 (s * K) + dyadicGeom s K =
      (2 : ℤ) ^ s * dyadicGeom s K := by
  have h₁ := geom_sum_mul (2 : ℤ) (s * K)
  have h₂ := geom_sum_mul ((2 : ℤ) ^ s) K
  have h₁' : dyadicGeom 1 (s * K) = (2 : ℤ) ^ (s * K) - 1 := by
    simpa [dyadicGeom] using h₁
  have h₂' : dyadicGeom s K * ((2 : ℤ) ^ s - 1) =
      (2 : ℤ) ^ (s * K) - 1 := by
    simpa [dyadicGeom, pow_mul] using h₂
  rw [h₁', ← h₂']
  ring

/-- Replacing every entered dyadic phase by the common odd phase `b^n` is valid to two
digits beyond the entire cleared denominator depth. -/
lemma stonehamClearedFamily_modEq_dyadicGeom
    (b s K n : ℕ) (hb : Odd b) (hs : 1 ≤ s) (hK : 1 ≤ K)
    (hentered : ∀ j ∈ Finset.Icc 1 K, (2 ^ s) ^ j ≤ n) :
    stonehamClearedFamily b (2 ^ s) n K ≡
      (b : ℤ) ^ n * dyadicGeom s K [ZMOD 2 ^ (s * K + 2)] := by
  have hsum :
      ∑ j ∈ Finset.Icc 1 K,
          (b : ℤ) ^ (n - (2 ^ s) ^ j) * ((2 ^ s : ℕ) : ℤ) ^ (K - j) ≡
        ∑ j ∈ Finset.Icc 1 K,
          (b : ℤ) ^ n * ((2 ^ s : ℕ) : ℤ) ^ (K - j)
          [ZMOD 2 ^ (s * K + 2)] := by
    apply Int.ModEq.sum
    intro j hj
    have hphase := twoStonehamPhase_modEq_of_factor
      b (2 ^ s) s 1 j n hb hs (Finset.mem_Icc.mp hj).1 (by simp) (hentered j hj)
    rw [Int.modEq_iff_dvd] at hphase ⊢
    have hjK : j ≤ K := (Finset.mem_Icc.mp hj).2
    have hmul := mul_dvd_mul hphase
      (dvd_refl ((2 : ℤ) ^ (s * (K - j))))
    simpa only [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, sub_mul, ← pow_add,
      show s * j + 2 + s * (K - j) = s * K + 2 by
        rw [show s * K = s * j + s * (K - j) by
          rw [← Nat.mul_add, Nat.add_sub_of_le hjK]]
        omega] using hmul
  rw [stonehamClearedFamily]
  refine hsum.trans ?_
  rw [← Finset.mul_sum]
  have heq :
      (∑ i ∈ Finset.Icc 1 K, ((2 ^ s : ℕ) : ℤ) ^ (K - i)) = dyadicGeom s K := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
    simpa only [dyadicGeom] using
      sum_Icc_one_reflect (fun t => (2 : ℤ) ^ (s * t)) K
  rw [heq]

/-- After padding to the common dyadic depth `J`, the preceding congruence has the uniform
precision `2^(J+2)`. -/
lemma sameClassClearedFamily_modEq_dyadicGeom
    (b s n J : ℕ) (hb : Odd b) (hs : 1 ≤ s) (hK : 1 ≤ J / s)
    (hentered : ∀ j ∈ Finset.Icc 1 (J / s), (2 ^ s) ^ j ≤ n) :
    sameClassClearedFamily b 2 s n J ≡
      (b : ℤ) ^ n *
        ((2 : ℤ) ^ (J - s * (J / s)) * dyadicGeom s (J / s))
        [ZMOD 2 ^ (J + 2)] := by
  have hbase := stonehamClearedFamily_modEq_dyadicGeom
    b s (J / s) n hb hs hK hentered
  rw [Int.modEq_iff_dvd] at hbase ⊢
  have hle : s * (J / s) ≤ J := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self J s
  have hmul := mul_dvd_mul hbase
    (dvd_refl ((2 : ℤ) ^ (J - s * (J / s))))
  have hpow : (2 : ℤ) ^ (s * (J / s) + 2) *
      (2 : ℤ) ^ (J - s * (J / s)) = (2 : ℤ) ^ (J + 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hdiff :
      ((b : ℤ) ^ n * dyadicGeom s (J / s) -
          stonehamClearedFamily b (2 ^ s) n (J / s)) *
          (2 : ℤ) ^ (J - s * (J / s)) =
        (b : ℤ) ^ n *
            ((2 : ℤ) ^ (J - s * (J / s)) * dyadicGeom s (J / s)) -
          stonehamClearedFamily b (2 ^ s) n (J / s) *
            (2 : ℤ) ^ (J - s * (J / s)) := by
    ring
  rw [hpow, hdiff] at hmul
  unfold sameClassClearedFamily
  simp only [Nat.cast_ofNat]
  exact hmul

/-- Both padded dyadic families therefore reduce to a purely geometric integer at the same
precision. -/
lemma sameClassPair_add_modEq_dyadicGeom
    (b s₁ s₂ n J : ℕ) (hb : Odd b) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (hK₁ : 1 ≤ J / s₁) (hK₂ : 1 ≤ J / s₂)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 (J / s₁), (2 ^ s₁) ^ j ≤ n)
    (hentered₂ : ∀ j ∈ Finset.Icc 1 (J / s₂), (2 ^ s₂) ^ j ≤ n) :
    sameClassClearedFamily b 2 s₁ n J + sameClassClearedFamily b 2 s₂ n J ≡
      (b : ℤ) ^ n *
        ((2 : ℤ) ^ (J - s₁ * (J / s₁)) * dyadicGeom s₁ (J / s₁) +
          (2 : ℤ) ^ (J - s₂ * (J / s₂)) * dyadicGeom s₂ (J / s₂))
        [ZMOD 2 ^ (J + 2)] := by
  have h₁ := sameClassClearedFamily_modEq_dyadicGeom
    b s₁ n J hb hs₁ hK₁ hentered₁
  have h₂ := sameClassClearedFamily_modEq_dyadicGeom
    b s₂ n J hb hs₂ hK₂ hentered₂
  convert h₁.add h₂ using 1 <;> ring

/-- Unequal integer `p`-adic valuations prevent additive cancellation. -/
lemma add_ne_zero_of_padicValInt_ne
    (p : ℕ) (A B : ℤ) (hval : padicValInt p A ≠ padicValInt p B) :
    A + B ≠ 0 := by
  intro hzero
  have hAB : A = -B := by omega
  apply hval
  rw [hAB]
  simp only [padicValInt, Int.natAbs_neg]

/-- The elementary ultrametric equality for two integers of unequal `p`-adic valuation. -/
lemma padicValInt_add_eq_min_of_ne
    (p : ℕ) (A B : ℤ) (hp : p.Prime) (hA : A ≠ 0) (hB : B ≠ 0)
    (hval : padicValInt p A ≠ padicValInt p B) :
    padicValInt p (A + B) = min (padicValInt p A) (padicValInt p B) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hsum : A + B ≠ 0 := add_ne_zero_of_padicValInt_ne p A B hval
  have hsumQ : (A : ℚ) + (B : ℚ) ≠ 0 := by exact_mod_cast hsum
  have hAQ : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hBQ : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  have hvalZ : (padicValInt p A : ℤ) ≠ (padicValInt p B : ℤ) := by
    exact_mod_cast hval
  have hrat := padicValRat.add_eq_min hsumQ hAQ hBQ (by
    simpa only [padicValRat.of_int] using hvalZ)
  have hrat' : (padicValInt p (A + B) : ℤ) =
      min (padicValInt p A : ℤ) (padicValInt p B : ℤ) := by
    simpa only [← Int.cast_add, padicValRat.of_int] using hrat
  exact_mod_cast hrat'

lemma padicValInt_two_pow (r : ℕ) : padicValInt 2 ((2 : ℤ) ^ r) = r := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [show (2 : ℤ) ^ r = ((2 ^ r : ℕ) : ℤ) by norm_cast,
    padicValInt.of_nat, padicValNat.prime_pow]

/-- The purely geometric aligned sum is nonzero and has uniformly bounded 2-adic valuation.
The only delicate tied case is when one step size is one; there the exact geometric identity
above gives valuation equal to the other step size. -/
lemma dyadicAlignedGeomPair_add_ne_zero_and_val_le
    (s₁ s₂ J : ℕ) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (hsne : s₁ ≠ s₂)
    (hK₁ : 1 ≤ J / s₁) (hK₂ : 1 ≤ J / s₂) :
    let S : ℤ :=
      (2 : ℤ) ^ (J - s₁ * (J / s₁)) * dyadicGeom s₁ (J / s₁) +
        (2 : ℤ) ^ (J - s₂ * (J / s₂)) * dyadicGeom s₂ (J / s₂)
    S ≠ 0 ∧ padicValInt 2 S ≤ s₁ + s₂ := by
  let K₁ := J / s₁
  let K₂ := J / s₂
  let r₁ := J - s₁ * K₁
  let r₂ := J - s₂ * K₂
  let G₁ := dyadicGeom s₁ K₁
  let G₂ := dyadicGeom s₂ K₂
  let U₁ : ℤ := (2 : ℤ) ^ r₁ * G₁
  let U₂ : ℤ := (2 : ℤ) ^ r₂ * G₂
  have hr₁ : r₁ < s₁ := by
    dsimp only [r₁, K₁]
    rw [← Nat.mod_eq_sub_mul_div]
    exact Nat.mod_lt J (by omega)
  have hr₂ : r₂ < s₂ := by
    dsimp only [r₂, K₂]
    rw [← Nat.mod_eq_sub_mul_div]
    exact Nat.mod_lt J (by omega)
  have hG₁unit : ¬ (2 : ℤ) ∣ G₁ := by
    exact not_two_dvd_dyadicGeom s₁ K₁ hs₁ (by simpa only [K₁] using hK₁)
  have hG₂unit : ¬ (2 : ℤ) ∣ G₂ := by
    exact not_two_dvd_dyadicGeom s₂ K₂ hs₂ (by simpa only [K₂] using hK₂)
  have hG₁0 : G₁ ≠ 0 := fun hzero => hG₁unit (by simp [hzero])
  have hG₂0 : G₂ ≠ 0 := fun hzero => hG₂unit (by simp [hzero])
  have hU₁0 : U₁ ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hG₁0
  have hU₂0 : U₂ ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hG₂0
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hvU₁ : padicValInt 2 U₁ = r₁ := by
    dsimp only [U₁]
    rw [padicValInt.mul (pow_ne_zero _ (by norm_num)) hG₁0,
      padicValInt_two_pow,
      padicValInt.eq_zero_of_not_dvd hG₁unit, add_zero]
  have hvU₂ : padicValInt 2 U₂ = r₂ := by
    dsimp only [U₂]
    rw [padicValInt.mul (pow_ne_zero _ (by norm_num)) hG₂0,
      padicValInt_two_pow,
      padicValInt.eq_zero_of_not_dvd hG₂unit, add_zero]
  change U₁ + U₂ ≠ 0 ∧ padicValInt 2 (U₁ + U₂) ≤ s₁ + s₂
  by_cases hrem : r₁ = r₂
  · by_cases hs₁one : s₁ = 1
    · subst s₁
      have hr₁zero : r₁ = 0 := by simp [r₁, K₁]
      have hr₂zero : r₂ = 0 := by omega
      have hs₂K₂ : s₂ * K₂ = J := by
        have hle : s₂ * K₂ ≤ J := by
          dsimp only [K₂]
          simpa [Nat.mul_comm] using Nat.div_mul_le_self J s₂
        dsimp only [r₂] at hr₂zero
        omega
      have hshape : U₁ + U₂ = (2 : ℤ) ^ s₂ * G₂ := by
        dsimp only [U₁, U₂]
        rw [hr₁zero, hr₂zero, pow_zero, one_mul, one_mul]
        dsimp only [G₁, G₂, K₁]
        rw [← hs₂K₂]
        simpa only [Nat.div_one] using dyadicGeom_one_mul_add s₂ K₂
      rw [hshape]
      have hpow0 : (2 : ℤ) ^ s₂ ≠ 0 := pow_ne_zero _ (by norm_num)
      constructor
      · exact mul_ne_zero hpow0 hG₂0
      · rw [padicValInt.mul hpow0 hG₂0, padicValInt_two_pow,
          padicValInt.eq_zero_of_not_dvd hG₂unit, add_zero]
        omega
    · by_cases hs₂one : s₂ = 1
      · subst s₂
        have hr₂zero : r₂ = 0 := by simp [r₂, K₂]
        have hr₁zero : r₁ = 0 := by omega
        have hs₁K₁ : s₁ * K₁ = J := by
          have hle : s₁ * K₁ ≤ J := by
            dsimp only [K₁]
            simpa [Nat.mul_comm] using Nat.div_mul_le_self J s₁
          dsimp only [r₁] at hr₁zero
          omega
        have hshape : U₁ + U₂ = (2 : ℤ) ^ s₁ * G₁ := by
          dsimp only [U₁, U₂]
          rw [hr₁zero, hr₂zero, pow_zero, one_mul, one_mul, add_comm]
          dsimp only [G₁, G₂, K₂]
          rw [← hs₁K₁]
          simpa only [Nat.div_one] using dyadicGeom_one_mul_add s₁ K₁
        rw [hshape]
        have hpow0 : (2 : ℤ) ^ s₁ ≠ 0 := pow_ne_zero _ (by norm_num)
        constructor
        · exact mul_ne_zero hpow0 hG₁0
        · rw [padicValInt.mul hpow0 hG₁0, padicValInt_two_pow,
            padicValInt.eq_zero_of_not_dvd hG₁unit, add_zero]
          omega
      · have hs₁two : 2 ≤ s₁ := by omega
        have hs₂two : 2 ≤ s₂ := by omega
        have hvcore := padicValInt_dyadicGeom_add_eq_one
          s₁ s₂ K₁ K₂ hs₁two hs₂two (by simpa only [K₁] using hK₁)
            (by simpa only [K₂] using hK₂)
        have hcore0 : G₁ + G₂ ≠ 0 := by
          intro hzero
          rw [show G₁ + G₂ = 0 by exact hzero] at hvcore
          simp [padicValInt] at hvcore
        have hshape : U₁ + U₂ = (2 : ℤ) ^ r₁ * (G₁ + G₂) := by
          dsimp only [U₁, U₂]
          rw [← hrem]
          ring
        rw [hshape]
        have hpow0 : (2 : ℤ) ^ r₁ ≠ 0 := pow_ne_zero _ (by norm_num)
        constructor
        · exact mul_ne_zero hpow0 hcore0
        · rw [padicValInt.mul hpow0 hcore0, padicValInt_two_pow, hvcore]
          omega
  · have hval : padicValInt 2 U₁ ≠ padicValInt 2 U₂ := by
      rw [hvU₁, hvU₂]
      exact hrem
    have hsum0 := add_ne_zero_of_padicValInt_ne 2 U₁ U₂ hval
    have hv := padicValInt_add_eq_min_of_ne 2 U₁ U₂ (by norm_num) hU₁0 hU₂0 hval
    refine ⟨hsum0, ?_⟩
    rw [hv, hvU₁, hvU₂]
    exact (min_le_left r₁ r₂).trans (hr₁.le.trans (Nat.le_add_right s₁ s₂))

/-- At precision exceeding the fixed geometric loss, the actual aligned dyadic numerator is
nonzero and has the same uniform 2-adic upper bound. -/
lemma sameClassPair_add_dyadic_ne_zero_and_val_le
    (b s₁ s₂ n J : ℕ) (hb : Odd b) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (hsne : s₁ ≠ s₂) (hK₁ : 1 ≤ J / s₁) (hK₂ : 1 ≤ J / s₂)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 (J / s₁), (2 ^ s₁) ^ j ≤ n)
    (hentered₂ : ∀ j ∈ Finset.Icc 1 (J / s₂), (2 ^ s₂) ^ j ≤ n)
    (hprec : s₁ + s₂ + 1 ≤ J + 2) :
    let A : ℤ := sameClassClearedFamily b 2 s₁ n J +
      sameClassClearedFamily b 2 s₂ n J
    A ≠ 0 ∧ padicValInt 2 A ≤ s₁ + s₂ := by
  let A : ℤ := sameClassClearedFamily b 2 s₁ n J +
    sameClassClearedFamily b 2 s₂ n J
  let S : ℤ :=
    (2 : ℤ) ^ (J - s₁ * (J / s₁)) * dyadicGeom s₁ (J / s₁) +
      (2 : ℤ) ^ (J - s₂ * (J / s₂)) * dyadicGeom s₂ (J / s₂)
  let R : ℤ := (b : ℤ) ^ n * S
  change A ≠ 0 ∧ padicValInt 2 A ≤ s₁ + s₂
  have hS := dyadicAlignedGeomPair_add_ne_zero_and_val_le
    s₁ s₂ J hs₁ hs₂ hsne hK₁ hK₂
  have hS0 : S ≠ 0 := by simpa only [S] using hS.1
  have hvS : padicValInt 2 S ≤ s₁ + s₂ := by simpa only [S] using hS.2
  have hbunit : ¬ (2 : ℤ) ∣ (b : ℤ) ^ n := by
    intro hdvd
    have hdvdNat : 2 ∣ b ^ n := by exact_mod_cast hdvd
    have hbdivNat : 2 ∣ b := Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvdNat
    exact hb.not_two_dvd_nat hbdivNat
  have hbpow0 : (b : ℤ) ^ n ≠ 0 := by
    intro hzero
    exact hbunit (by simp [hzero])
  have hR0 : R ≠ 0 := by
    dsimp only [R]
    exact mul_ne_zero hbpow0 hS0
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hvR : padicValInt 2 R = padicValInt 2 S := by
    dsimp only [R]
    rw [padicValInt.mul hbpow0 hS0, padicValInt.eq_zero_of_not_dvd hbunit, zero_add]
  have hRnot : ¬ (2 : ℤ) ^ (s₁ + s₂ + 1) ∣ R := by
    intro hdvd
    rcases (padicValInt_dvd_iff (s₁ + s₂ + 1) R).mp hdvd with hzero | hle
    · exact hR0 hzero
    · rw [hvR] at hle
      omega
  have hmod := sameClassPair_add_modEq_dyadicGeom
    b s₁ s₂ n J hb hs₁ hs₂ hK₁ hK₂ hentered₁ hentered₂
  have hmodSmall : A ≡ R [ZMOD (2 : ℤ) ^ (s₁ + s₂ + 1)] := by
    apply hmod.of_dvd
    exact pow_dvd_pow (2 : ℤ) hprec
  have hAnot : ¬ (2 : ℤ) ^ (s₁ + s₂ + 1) ∣ A := by
    intro hdvd
    apply hRnot
    exact Int.modEq_zero_iff_dvd.mp
      (hmodSmall.symm.trans (Int.modEq_zero_iff_dvd.mpr hdvd))
  have hA0 : A ≠ 0 := by
    intro hzero
    apply hAnot
    simp [hzero]
  refine ⟨hA0, ?_⟩
  by_contra hle
  have hlt : s₁ + s₂ < padicValInt 2 A := Nat.lt_of_not_ge hle
  apply hAnot
  apply (padicValInt_dvd_iff (s₁ + s₂ + 1) A).mpr
  exact Or.inr (Nat.succ_le_iff.mpr hlt)

/-- Expanded form of the aligned numerator: the original `g ^ s` kicks occupy precisely the
`g`-depths divisible by `s`. -/
lemma sameClassClearedFamily_eq_sum (b g s n J : ℕ) :
    sameClassClearedFamily b g s n J =
      ∑ j ∈ Finset.Icc 1 (J / s),
        (b : ℤ) ^ (n - g ^ (s * j)) * (g : ℤ) ^ (J - s * j) := by
  unfold sameClassClearedFamily stonehamClearedFamily
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjK : j ≤ J / s := (Finset.mem_Icc.mp hj).2
  have hsK : s * (J / s) ≤ J := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self J s
  rw [pow_mul g s j]
  simp only [Nat.cast_pow]
  rw [mul_assoc]
  congr 1
  rw [← pow_mul, ← pow_add]
  congr 1
  rw [Nat.mul_sub_left_distrib]
  have hsj : s * j ≤ s * (J / s) := Nat.mul_le_mul_left s hjK
  omega

/-- A `g ^ s` Stoneham family, truncated at the depth dictated by `J`, has the common
denominator `g ^ J` after padding its cleared numerator by the division remainder. -/
lemma stonehamPowerFamily_eq_sameClassCleared_div
    (b g s n J : ℕ) (hg0 : g ≠ 0) (hs : 1 ≤ s) :
    ∑ j ∈ Finset.Icc 1 (J / s),
        (b : ℚ) ^ (n - (g ^ s) ^ j) / ((g ^ s : ℕ) : ℚ) ^ j =
      (sameClassClearedFamily b g s n J : ℚ) / (g : ℚ) ^ J := by
  rw [stonehamFamily_eq_cleared_div b (g ^ s) n (J / s) (pow_ne_zero _ hg0)]
  unfold sameClassClearedFamily
  push_cast
  have hle : s * (J / s) ≤ J := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self J s
  have hpow : (g : ℚ) ^ J =
      ((g : ℚ) ^ s) ^ (J / s) * (g : ℚ) ^ (J - s * (J / s)) := by
    calc
      (g : ℚ) ^ J = (g : ℚ) ^ (s * (J / s) + (J - s * (J / s))) := by
        rw [Nat.add_sub_of_le hle]
      _ = ((g : ℚ) ^ s) ^ (J / s) * (g : ℚ) ^ (J - s * (J / s)) := by
        rw [pow_add, pow_mul]
  rw [hpow]
  field_simp

/-- At the actual entered depth, a family whose base is `g ^ s` is represented over the
class-wide denominator `g ^ Nat.log g n`. -/
lemma stonehamPowerFamily_eq_sameClassCleared_log_div
    (b g s n : ℕ) (hg0 : g ≠ 0) (hs : 1 ≤ s) :
    ∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s) n),
        (b : ℚ) ^ (n - (g ^ s) ^ j) / ((g ^ s : ℕ) : ℚ) ^ j =
      (sameClassClearedFamily b g s n (Nat.log g n) : ℚ) /
        (g : ℚ) ^ Nat.log g n := by
  rw [Nat.log_pow_left]
  exact stonehamPowerFamily_eq_sameClassCleared_div b g s n (Nat.log g n) hg0 hs

/-- A signed literal pair in one multiplicative class has a single exact denominator before
reduction.  The coefficient `σ` will later be specialized to `1` and `-1`. -/
lemma stonehamSameClassPair_eq_cleared_div
    (b g s₁ s₂ n : ℕ) (σ : ℤ) (hg0 : g ≠ 0) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) :
    (∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₁) n),
        (b : ℚ) ^ (n - (g ^ s₁) ^ j) / ((g ^ s₁ : ℕ) : ℚ) ^ j) +
      (σ : ℚ) * (∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₂) n),
        (b : ℚ) ^ (n - (g ^ s₂) ^ j) / ((g ^ s₂ : ℕ) : ℚ) ^ j) =
      ((sameClassClearedFamily b g s₁ n (Nat.log g n) +
          σ * sameClassClearedFamily b g s₂ n (Nat.log g n) : ℤ) : ℚ) /
        (g : ℚ) ^ Nat.log g n := by
  rw [stonehamPowerFamily_eq_sameClassCleared_log_div b g s₁ n hg0 hs₁,
    stonehamPowerFamily_eq_sameClassCleared_log_div b g s₂ n hg0 hs₂]
  push_cast
  ring

/-- If an integral numerator has valuation at most `B` inside a denominator of total valuation
`E`, then at least `p^(E-B)` survives in the reduced rational denominator. -/
lemma prime_pow_sub_bound_dvd_rat_den_of_eq_div
    (p E B : ℕ) (A : ℤ) (D : ℕ) (q : ℚ) (hp : p.Prime)
    (hA : A ≠ 0) (hD : D ≠ 0) (hq : q = (A : ℚ) / (D : ℚ))
    (hvA : padicValInt p A ≤ B) (hvD : padicValNat p D = E) (hBE : B ≤ E) :
    p ^ (E - B) ∣ q.den := by
  let v := padicValInt p A
  have hvB : v ≤ B := by simpa only [v] using hvA
  have hvE : v ≤ E := hvB.trans hBE
  have hvD' : padicValNat p D = v + (E - v) := by
    rw [hvD, Nat.add_sub_of_le hvE]
  have hfull := prime_pow_dvd_rat_den_of_eq_div
    p (E - v) v A D q hp hA hD hq rfl hvD'
  have hexp : E - B ≤ E - v := by
    exact Nat.sub_le_sub_left hvB E
  exact (pow_dvd_pow p hexp).trans hfull

/-! ### Prime depth of one aligned family -/

/-- Modulo a prime of the denominator base, only the newest kick of a cleared family remains. -/
lemma stonehamClearedFamily_modEq_newest
    (p b c n K : ℕ) (hpc : p ∣ c) (hK : 1 ≤ K) :
    stonehamClearedFamily b c n K ≡
      (b : ℤ) ^ (n - c ^ K) [ZMOD p] := by
  unfold stonehamClearedFamily
  rw [show K = K - 1 + 1 by omega,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ K - 1 + 1)]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
  have hzero :
      ∑ j ∈ Finset.Icc 1 (K - 1),
          (b : ℤ) ^ (n - c ^ j) * (c : ℤ) ^ (K - j) ≡ 0 [ZMOD p] := by
    simpa only [Finset.sum_const_zero] using
      (Int.ModEq.sum fun j hj => Int.modEq_zero_iff_dvd.mpr (by
        have hjK : j < K := by
          have := (Finset.mem_Icc.mp hj).2
          omega
        have hpow : (p : ℤ) ∣ (c : ℤ) ^ (K - j) := by
          exact_mod_cast dvd_pow hpc (by omega : K - j ≠ 0)
        exact dvd_mul_of_dvd_right hpow ((b : ℤ) ^ (n - c ^ j))))
  simpa only [show K - 1 + 1 = K by omega, zero_add] using
    hzero.add (Int.ModEq.rfl :
      (b : ℤ) ^ (n - c ^ K) ≡ (b : ℤ) ^ (n - c ^ K) [ZMOD p])

/-- Removing the newest kick from a cleared family leaves `c` times the preceding numerator. -/
lemma stonehamClearedFamily_eq_mul_pred_add_newest
    (b c n K : ℕ) (hK : 1 ≤ K) :
    stonehamClearedFamily b c n K =
      (c : ℤ) * stonehamClearedFamily b c n (K - 1) +
        (b : ℤ) ^ (n - c ^ K) := by
  unfold stonehamClearedFamily
  rw [show K = K - 1 + 1 by omega,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ K - 1 + 1)]
  simp only [show K - 1 + 1 = K by omega, Nat.sub_self, pow_zero, mul_one]
  rw [Finset.mul_sum]
  apply congrArg (fun z : ℤ => z + (b : ℤ) ^ (n - c ^ K))
  apply Finset.sum_congr rfl
  intro j hj
  have hjK : j ≤ K - 1 := (Finset.mem_Icc.mp hj).2
  rw [show K - j = (K - 1 - j) + 1 by omega, pow_succ]
  ring

/-- At every prime of the common base, padding a family to the common `g`-depth introduces
exactly the valuation of the remainder power.  The original cleared family is a unit by the
one-family polar argument. -/
lemma sameClassClearedFamily_ne_zero
    (p b g s n J : ℕ) (hp : p.Prime) (hg0 : g ≠ 0) (hpg : p ∣ g)
    (hgb : Nat.Coprime g b) (hK : 1 ≤ J / s)
    (hentered : ∀ j ∈ Finset.Icc 1 (J / s), (g ^ s) ^ j ≤ n) :
    sameClassClearedFamily b g s n J ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro hzero
    subst s
    simp at hK
  have hgs0 : g ^ s ≠ 0 := pow_ne_zero _ hg0
  have hpgs : p ∣ g ^ s := dvd_pow hpg hs0
  have hcop : Nat.Coprime (g ^ s) b := hgb.pow_left s
  have hnot : ¬ (p : ℤ) ∣ stonehamClearedFamily b (g ^ s) n (J / s) :=
    not_dvd_stonehamClearedFamily
      p b (g ^ s) (J / s) n hp hgs0 hpgs hcop hK hentered
  unfold sameClassClearedFamily
  exact mul_ne_zero (fun hzero => hnot (by simp [hzero]))
    (pow_ne_zero _ (Int.natCast_ne_zero.mpr hg0))

lemma padicValInt_sameClassClearedFamily
    (p b g s n J : ℕ) (hp : p.Prime) (hg0 : g ≠ 0) (hpg : p ∣ g)
    (hgb : Nat.Coprime g b) (hK : 1 ≤ J / s)
    (hentered : ∀ j ∈ Finset.Icc 1 (J / s), (g ^ s) ^ j ≤ n) :
    padicValInt p (sameClassClearedFamily b g s n J) =
      g.factorization p * (J - s * (J / s)) := by
  let A := stonehamClearedFamily b (g ^ s) n (J / s)
  have hs0 : s ≠ 0 := by
    intro hzero
    subst s
    simp at hK
  have hgs0 : g ^ s ≠ 0 := pow_ne_zero _ hg0
  have hpgs : p ∣ g ^ s := dvd_pow hpg hs0
  have hcop : Nat.Coprime (g ^ s) b := hgb.pow_left s
  have hnot : ¬ (p : ℤ) ∣ A := by
    exact not_dvd_stonehamClearedFamily
      p b (g ^ s) (J / s) n hp hgs0 hpgs hcop hK hentered
  have hunit : padicValInt p A = 0 := by
    exact padicValInt.eq_zero_of_not_dvd hnot
  have hA0 : A ≠ 0 := by
    intro hzero
    apply hnot
    simp [hzero]
  have hpow0 : (g : ℤ) ^ (J - s * (J / s)) ≠ 0 :=
    pow_ne_zero _ (Int.natCast_ne_zero.mpr hg0)
  letI : Fact p.Prime := ⟨hp⟩
  unfold sameClassClearedFamily
  rw [show stonehamClearedFamily b (g ^ s) n (J / s) = A by rfl,
    padicValInt.mul hA0 hpow0, hunit, zero_add, ← Int.natCast_pow,
    padicValInt.of_nat, padicValNat.pow, ← Nat.factorization_def g hp]
  ac_rfl

/-- If the two division remainders differ, the shallower aligned family is the unique term of
least `p`-adic valuation.  Hence either literal sign has exactly the smaller remainder depth.
Only the tied-remainder phases require the periodic-tail argument. -/
lemma padicValInt_sameClassPair_eq_min_of_remainder_ne
    (p b g s₁ s₂ n J : ℕ) (σ : ℤ) (hp : p.Prime) (hg0 : g ≠ 0) (hpg : p ∣ g)
    (hgb : Nat.Coprime g b) (hK₁ : 1 ≤ J / s₁) (hK₂ : 1 ≤ J / s₂)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 (J / s₁), (g ^ s₁) ^ j ≤ n)
    (hentered₂ : ∀ j ∈ Finset.Icc 1 (J / s₂), (g ^ s₂) ^ j ≤ n)
    (hσ0 : σ ≠ 0) (hσunit : ¬ (p : ℤ) ∣ σ)
    (hrem : J - s₁ * (J / s₁) ≠ J - s₂ * (J / s₂)) :
    padicValInt p
        (sameClassClearedFamily b g s₁ n J +
          σ * sameClassClearedFamily b g s₂ n J) =
      min (g.factorization p * (J - s₁ * (J / s₁)))
        (g.factorization p * (J - s₂ * (J / s₂))) := by
  let A₁ := sameClassClearedFamily b g s₁ n J
  let A₂ := sameClassClearedFamily b g s₂ n J
  have hA₁0 : A₁ ≠ 0 := sameClassClearedFamily_ne_zero
    p b g s₁ n J hp hg0 hpg hgb hK₁ hentered₁
  have hA₂0 : A₂ ≠ 0 := sameClassClearedFamily_ne_zero
    p b g s₂ n J hp hg0 hpg hgb hK₂ hentered₂
  have hv₁ : padicValInt p A₁ =
      g.factorization p * (J - s₁ * (J / s₁)) :=
    padicValInt_sameClassClearedFamily
      p b g s₁ n J hp hg0 hpg hgb hK₁ hentered₁
  have hv₂ : padicValInt p A₂ =
      g.factorization p * (J - s₂ * (J / s₂)) :=
    padicValInt_sameClassClearedFamily
      p b g s₂ n J hp hg0 hpg hgb hK₂ hentered₂
  letI : Fact p.Prime := ⟨hp⟩
  have hσA₂0 : σ * A₂ ≠ 0 := mul_ne_zero hσ0 hA₂0
  have hvσ : padicValInt p (σ * A₂) =
      g.factorization p * (J - s₂ * (J / s₂)) := by
    rw [padicValInt.mul hσ0 hA₂0, padicValInt.eq_zero_of_not_dvd hσunit,
      zero_add, hv₂]
  have ha : 0 < g.factorization p := by
    exact Nat.pos_of_ne_zero (by
      simpa [Nat.factorization_eq_zero_iff, hp, hpg] using hg0)
  have hval : padicValInt p A₁ ≠ padicValInt p (σ * A₂) := by
    rw [hv₁, hvσ]
    exact fun heq => hrem (Nat.eq_of_mul_eq_mul_left ha heq)
  simpa only [A₁, A₂, hv₁, hvσ] using
    padicValInt_add_eq_min_of_ne p A₁ (σ * A₂) hp hA₁0 hσA₂0 hval

/-- For a literal sum at an odd common prime, tied remainder depths still lose nothing: the two
newest kicks are identical modulo `p`, so their coefficient is the unit `2`. -/
lemma padicValInt_sameClassPair_add_eq_of_remainder_eq_of_ne_two
    (p b g s₁ s₂ n J : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hg0 : g ≠ 0) (hpg : p ∣ g) (hgb : Nat.Coprime g b)
    (hK₁ : 1 ≤ J / s₁) (hK₂ : 1 ≤ J / s₂)
    (hrem : J - s₁ * (J / s₁) = J - s₂ * (J / s₂)) :
    padicValInt p
        (sameClassClearedFamily b g s₁ n J +
          sameClassClearedFamily b g s₂ n J) =
      g.factorization p * (J - s₁ * (J / s₁)) := by
  let K₁ := J / s₁
  let K₂ := J / s₂
  let C₁ := stonehamClearedFamily b (g ^ s₁) n K₁
  let C₂ := stonehamClearedFamily b (g ^ s₂) n K₂
  let r := J - s₁ * K₁
  have hsK₁ : s₁ * K₁ ≤ J := by
    dsimp only [K₁]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self J s₁
  have hsK₂ : s₂ * K₂ ≤ J := by
    dsimp only [K₂]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self J s₂
  have hdepth : s₁ * K₁ = s₂ * K₂ := by
    dsimp only [K₁, K₂] at hrem hsK₁ hsK₂ ⊢
    omega
  have hphase : (g ^ s₁) ^ K₁ = (g ^ s₂) ^ K₂ := by
    rw [← pow_mul, ← pow_mul, hdepth]
  have hmod₁ : C₁ ≡ (b : ℤ) ^ (n - (g ^ s₁) ^ K₁) [ZMOD p] := by
    exact stonehamClearedFamily_modEq_newest p b (g ^ s₁) n K₁
      (dvd_pow hpg (by
        intro hs
        subst s₁
        simp [K₁] at hK₁)) (by simpa only [K₁] using hK₁)
  have hmod₂ : C₂ ≡ (b : ℤ) ^ (n - (g ^ s₂) ^ K₂) [ZMOD p] := by
    exact stonehamClearedFamily_modEq_newest p b (g ^ s₂) n K₂
      (dvd_pow hpg (by
        intro hs
        subst s₂
        simp [K₂] at hK₂)) (by simpa only [K₂] using hK₂)
  have hmod : C₁ + C₂ ≡
      2 * (b : ℤ) ^ (n - (g ^ s₁) ^ K₁) [ZMOD p] := by
    have := hmod₁.add hmod₂
    rw [← hphase] at this
    simpa [two_mul] using this
  have hnot : ¬ (p : ℤ) ∣ C₁ + C₂ := by
    intro hdvd
    have hright : (p : ℤ) ∣ 2 * (b : ℤ) ^ (n - (g ^ s₁) ^ K₁) :=
      Int.modEq_zero_iff_dvd.mp
        (hmod.symm.trans (Int.modEq_zero_iff_dvd.mpr hdvd))
    rcases Int.Prime.dvd_mul' hp hright with htwo | hbpow
    · have hpnat : p ∣ 2 := by exact_mod_cast htwo
      have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpnat
      exact hp2 (Nat.le_antisymm hple hp.two_le)
    · have hpb : ¬ p ∣ b := hp.coprime_iff_not_dvd.mp
        (Nat.Coprime.of_dvd_left hpg hgb)
      exact hpb (by
        exact_mod_cast Int.Prime.dvd_pow hp hbpow)
  have hC0 : C₁ + C₂ ≠ 0 := fun hzero => hnot (by simp [hzero])
  have hgpow0 : (g : ℤ) ^ r ≠ 0 :=
    pow_ne_zero _ (Int.natCast_ne_zero.mpr hg0)
  have hshape :
      sameClassClearedFamily b g s₁ n J +
          sameClassClearedFamily b g s₂ n J =
        (C₁ + C₂) * (g : ℤ) ^ r := by
    unfold sameClassClearedFamily
    dsimp only [C₁, C₂, K₁, K₂, r] at hrem ⊢
    rw [← hrem]
    ring
  letI : Fact p.Prime := ⟨hp⟩
  rw [hshape, padicValInt.mul hC0 hgpow0,
    padicValInt.eq_zero_of_not_dvd hnot, zero_add, ← Int.natCast_pow,
    padicValInt.of_nat, padicValNat.pow, ← Nat.factorization_def g hp]
  dsimp only [r, K₁]
  ac_rfl

/-- At an odd prime of the common base, a literal sum has nonzero aligned numerator and loses
at most a fixed number of prime digits, uniformly in the truncation depth. -/
lemma sameClassPair_add_ne_zero_and_val_le_of_ne_two
    (p b g s₁ s₂ n J : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hg0 : g ≠ 0) (hpg : p ∣ g) (hgb : Nat.Coprime g b)
    (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (hK₁ : 1 ≤ J / s₁) (hK₂ : 1 ≤ J / s₂)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 (J / s₁), (g ^ s₁) ^ j ≤ n)
    (hentered₂ : ∀ j ∈ Finset.Icc 1 (J / s₂), (g ^ s₂) ^ j ≤ n) :
    let A : ℤ := sameClassClearedFamily b g s₁ n J +
      sameClassClearedFamily b g s₂ n J
    A ≠ 0 ∧ padicValInt p A ≤ g.factorization p * (s₁ + s₂) := by
  let A₁ := sameClassClearedFamily b g s₁ n J
  let A₂ := sameClassClearedFamily b g s₂ n J
  let A := A₁ + A₂
  let a := g.factorization p
  let r₁ := J - s₁ * (J / s₁)
  let r₂ := J - s₂ * (J / s₂)
  change A ≠ 0 ∧ padicValInt p A ≤ a * (s₁ + s₂)
  have hA₁0 : A₁ ≠ 0 := sameClassClearedFamily_ne_zero
    p b g s₁ n J hp hg0 hpg hgb hK₁ hentered₁
  have hA₂0 : A₂ ≠ 0 := sameClassClearedFamily_ne_zero
    p b g s₂ n J hp hg0 hpg hgb hK₂ hentered₂
  have hA₁nonneg : 0 ≤ A₁ := by
    simpa only [A₁] using sameClassClearedFamily_nonneg b g s₁ n J
  have hA₂nonneg : 0 ≤ A₂ := by
    simpa only [A₂] using sameClassClearedFamily_nonneg b g s₂ n J
  have hA0 : A ≠ 0 := by
    dsimp only [A]
    omega
  refine ⟨hA0, ?_⟩
  have hr₁ : r₁ < s₁ := by
    dsimp only [r₁]
    rw [← Nat.mod_eq_sub_mul_div]
    exact Nat.mod_lt J (by omega)
  have hr₂ : r₂ < s₂ := by
    dsimp only [r₂]
    rw [← Nat.mod_eq_sub_mul_div]
    exact Nat.mod_lt J (by omega)
  by_cases hrem : r₁ = r₂
  · have hv := padicValInt_sameClassPair_add_eq_of_remainder_eq_of_ne_two
      p b g s₁ s₂ n J hp hp2 hg0 hpg hgb hK₁ hK₂ (by
        simpa only [r₁, r₂] using hrem)
    change padicValInt p (A₁ + A₂) ≤ a * (s₁ + s₂)
    rw [hv]
    exact Nat.mul_le_mul_left a (hr₁.le.trans (Nat.le_add_right s₁ s₂))
  · have hv := padicValInt_sameClassPair_eq_min_of_remainder_ne
      p b g s₁ s₂ n J 1 hp hg0 hpg hgb hK₁ hK₂ hentered₁ hentered₂
        (by norm_num) (by
          intro hdvd
          apply hp.not_dvd_one
          exact_mod_cast hdvd) (by simpa only [r₁, r₂] using hrem)
    have hv' : padicValInt p (A₁ + A₂) = min (a * r₁) (a * r₂) := by
      simpa only [A₁, A₂, one_mul, a, r₁, r₂] using hv
    change padicValInt p (A₁ + A₂) ≤ a * (s₁ + s₂)
    rw [hv']
    exact (min_le_left _ _).trans
      ((Nat.mul_le_mul_left a hr₁.le).trans
        (Nat.mul_le_mul_left a (Nat.le_add_right s₁ s₂)))

/-- For a literal difference, tied newest depths cancel exactly.  When the powers `s₁,s₂`
differ, the next kick from the smaller power is the unique least-valuation term, so the loss is
still bounded by one fixed class depth. -/
lemma padicValInt_sameClassPair_sub_eq_of_remainder_eq
    (p b g s₁ s₂ n J : ℕ) (hp : p.Prime) (hg0 : g ≠ 0) (hpg : p ∣ g)
    (hgb : Nat.Coprime g b) (hsne : s₁ ≠ s₂)
    (hK₁ : 2 ≤ J / s₁) (hK₂ : 2 ≤ J / s₂)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 (J / s₁), (g ^ s₁) ^ j ≤ n)
    (hentered₂ : ∀ j ∈ Finset.Icc 1 (J / s₂), (g ^ s₂) ^ j ≤ n)
    (hrem : J - s₁ * (J / s₁) = J - s₂ * (J / s₂)) :
    padicValInt p
        (sameClassClearedFamily b g s₁ n J -
          sameClassClearedFamily b g s₂ n J) =
      g.factorization p * (J - s₁ * (J / s₁)) +
        min (g.factorization p * s₁) (g.factorization p * s₂) := by
  let K₁ := J / s₁
  let K₂ := J / s₂
  let C₁ := stonehamClearedFamily b (g ^ s₁) n K₁
  let C₂ := stonehamClearedFamily b (g ^ s₂) n K₂
  let P₁ := stonehamClearedFamily b (g ^ s₁) n (K₁ - 1)
  let P₂ := stonehamClearedFamily b (g ^ s₂) n (K₂ - 1)
  let T₁ := (g ^ s₁ : ℕ)
  let T₂ := (g ^ s₂ : ℕ)
  let r := J - s₁ * K₁
  have hs₁0 : s₁ ≠ 0 := by
    intro hzero
    subst s₁
    simp [K₁] at hK₁
  have hs₂0 : s₂ ≠ 0 := by
    intro hzero
    subst s₂
    simp [K₂] at hK₂
  have hT₁0 : T₁ ≠ 0 := pow_ne_zero _ hg0
  have hT₂0 : T₂ ≠ 0 := pow_ne_zero _ hg0
  have hpT₁ : p ∣ T₁ := dvd_pow hpg hs₁0
  have hpT₂ : p ∣ T₂ := dvd_pow hpg hs₂0
  have hcop₁ : Nat.Coprime T₁ b := hgb.pow_left s₁
  have hcop₂ : Nat.Coprime T₂ b := hgb.pow_left s₂
  have hprevK₁ : 1 ≤ K₁ - 1 := by dsimp only [K₁]; omega
  have hprevK₂ : 1 ≤ K₂ - 1 := by dsimp only [K₂]; omega
  have hprevEntered₁ : ∀ j ∈ Finset.Icc 1 (K₁ - 1), T₁ ^ j ≤ n := by
    intro j hj
    apply hentered₁ j
    simpa only [K₁, T₁] using Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans (Nat.sub_le _ _)⟩
  have hprevEntered₂ : ∀ j ∈ Finset.Icc 1 (K₂ - 1), T₂ ^ j ≤ n := by
    intro j hj
    apply hentered₂ j
    simpa only [K₂, T₂] using Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans (Nat.sub_le _ _)⟩
  have hP₁unit : ¬ (p : ℤ) ∣ P₁ := by
    exact not_dvd_stonehamClearedFamily p b T₁ (K₁ - 1) n hp hT₁0 hpT₁ hcop₁
      hprevK₁ hprevEntered₁
  have hP₂unit : ¬ (p : ℤ) ∣ P₂ := by
    exact not_dvd_stonehamClearedFamily p b T₂ (K₂ - 1) n hp hT₂0 hpT₂ hcop₂
      hprevK₂ hprevEntered₂
  have hP₁0 : P₁ ≠ 0 := fun hzero => hP₁unit (by simp [hzero])
  have hP₂0 : P₂ ≠ 0 := fun hzero => hP₂unit (by simp [hzero])
  have hterm₁0 : (T₁ : ℤ) * P₁ ≠ 0 :=
    mul_ne_zero (Int.natCast_ne_zero.mpr hT₁0) hP₁0
  have hterm₂0 : -((T₂ : ℤ) * P₂) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (Int.natCast_ne_zero.mpr hT₂0) hP₂0)
  letI : Fact p.Prime := ⟨hp⟩
  have hv₁ : padicValInt p ((T₁ : ℤ) * P₁) = g.factorization p * s₁ := by
    rw [padicValInt.mul (Int.natCast_ne_zero.mpr hT₁0) hP₁0,
      padicValInt.eq_zero_of_not_dvd hP₁unit, add_zero, padicValInt.of_nat,
      ← Nat.factorization_def T₁ hp]
    simp only [T₁, Nat.factorization_pow]
    ac_rfl
  have hv₂ : padicValInt p (-((T₂ : ℤ) * P₂)) = g.factorization p * s₂ := by
    have hv₂raw : padicValInt p ((T₂ : ℤ) * P₂) = g.factorization p * s₂ := by
      rw [padicValInt.mul (Int.natCast_ne_zero.mpr hT₂0) hP₂0,
        padicValInt.eq_zero_of_not_dvd hP₂unit, add_zero, padicValInt.of_nat,
        ← Nat.factorization_def T₂ hp]
      simp only [T₂, Nat.factorization_pow]
      ac_rfl
    simpa only [padicValInt, Int.natAbs_neg] using hv₂raw
  have hval : padicValInt p ((T₁ : ℤ) * P₁) ≠
      padicValInt p (-((T₂ : ℤ) * P₂)) := by
    rw [hv₁, hv₂]
    have ha : 0 < g.factorization p := Nat.pos_of_ne_zero (by
      simpa [Nat.factorization_eq_zero_iff, hp, hpg] using hg0)
    exact fun heq => hsne (Nat.eq_of_mul_eq_mul_left ha heq)
  have hvcore : padicValInt p ((T₁ : ℤ) * P₁ - (T₂ : ℤ) * P₂) =
      min (g.factorization p * s₁) (g.factorization p * s₂) := by
    simpa only [sub_eq_add_neg, hv₁, hv₂] using
      padicValInt_add_eq_min_of_ne p ((T₁ : ℤ) * P₁) (-((T₂ : ℤ) * P₂)) hp
        hterm₁0 hterm₂0 hval
  have hcore0 : (T₁ : ℤ) * P₁ - (T₂ : ℤ) * P₂ ≠ 0 := by
    intro hzero
    have heq : (T₁ : ℤ) * P₁ = -(-((T₂ : ℤ) * P₂)) := by omega
    apply hval
    rw [heq]
    simp only [padicValInt, Int.natAbs_neg, neg_neg]
  have hsK₁ : s₁ * K₁ ≤ J := by
    dsimp only [K₁]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self J s₁
  have hsK₂ : s₂ * K₂ ≤ J := by
    dsimp only [K₂]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self J s₂
  have hdepth : s₁ * K₁ = s₂ * K₂ := by
    dsimp only [K₁, K₂] at hrem hsK₁ hsK₂ ⊢
    omega
  have hphase : T₁ ^ K₁ = T₂ ^ K₂ := by
    dsimp only [T₁, T₂]
    rw [← pow_mul, ← pow_mul, hdepth]
  have hCdiff : C₁ - C₂ = (T₁ : ℤ) * P₁ - (T₂ : ℤ) * P₂ := by
    rw [show C₁ = (T₁ : ℤ) * P₁ + (b : ℤ) ^ (n - T₁ ^ K₁) by
      exact stonehamClearedFamily_eq_mul_pred_add_newest b T₁ n K₁ (by omega),
      show C₂ = (T₂ : ℤ) * P₂ + (b : ℤ) ^ (n - T₂ ^ K₂) by
        exact stonehamClearedFamily_eq_mul_pred_add_newest b T₂ n K₂ (by omega),
      hphase]
    ring
  have hgpow0 : (g : ℤ) ^ r ≠ 0 :=
    pow_ne_zero _ (Int.natCast_ne_zero.mpr hg0)
  have hshape :
      sameClassClearedFamily b g s₁ n J -
          sameClassClearedFamily b g s₂ n J =
        (C₁ - C₂) * (g : ℤ) ^ r := by
    unfold sameClassClearedFamily
    dsimp only [C₁, C₂, K₁, K₂, r] at hrem ⊢
    rw [← hrem]
    ring
  rw [hshape, hCdiff, padicValInt.mul hcore0 hgpow0, hvcore,
    ← Int.natCast_pow, padicValInt.of_nat, padicValNat.pow,
    ← Nat.factorization_def g hp]
  dsimp only [r, K₁]
  ac_rfl

/-- Uniform local cancellation bound for a literal same-class difference.  The bound depends
only on the two class powers, never on `n` or on the common depth `J`. -/
lemma padicValInt_sameClassPair_sub_le
    (p b g s₁ s₂ n J : ℕ) (hp : p.Prime) (hg0 : g ≠ 0) (hpg : p ∣ g)
    (hgb : Nat.Coprime g b) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (hsne : s₁ ≠ s₂)
    (hK₁ : 2 ≤ J / s₁) (hK₂ : 2 ≤ J / s₂)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 (J / s₁), (g ^ s₁) ^ j ≤ n)
    (hentered₂ : ∀ j ∈ Finset.Icc 1 (J / s₂), (g ^ s₂) ^ j ≤ n) :
    padicValInt p
        (sameClassClearedFamily b g s₁ n J -
          sameClassClearedFamily b g s₂ n J) ≤
      g.factorization p * (s₁ + s₂) := by
  let a := g.factorization p
  let r₁ := J - s₁ * (J / s₁)
  let r₂ := J - s₂ * (J / s₂)
  have hr₁ : r₁ < s₁ := by
    dsimp only [r₁]
    rw [← Nat.mod_eq_sub_mul_div]
    exact Nat.mod_lt J (by omega)
  have hr₂ : r₂ < s₂ := by
    dsimp only [r₂]
    rw [← Nat.mod_eq_sub_mul_div]
    exact Nat.mod_lt J (by omega)
  by_cases hrem : r₁ = r₂
  · have hv := padicValInt_sameClassPair_sub_eq_of_remainder_eq
      p b g s₁ s₂ n J hp hg0 hpg hgb hsne hK₁ hK₂ hentered₁ hentered₂ (by
        simpa only [r₁, r₂] using hrem)
    rw [hv]
    have hmin : min (a * s₁) (a * s₂) ≤ a * s₂ := min_le_right _ _
    have hrmul : a * r₁ ≤ a * s₁ := Nat.mul_le_mul_left a hr₁.le
    change a * r₁ + min (a * s₁) (a * s₂) ≤ a * (s₁ + s₂)
    calc
      a * r₁ + min (a * s₁) (a * s₂) ≤ a * s₁ + a * s₂ :=
        Nat.add_le_add hrmul hmin
      _ = a * (s₁ + s₂) := by rw [Nat.mul_add]
  · have hv := padicValInt_sameClassPair_eq_min_of_remainder_ne
      p b g s₁ s₂ n J (-1) hp hg0 hpg hgb (by omega) (by omega)
        hentered₁ hentered₂ (by norm_num) (by
          intro hdvd
          apply hp.not_dvd_one
          have hdvdZ : (p : ℤ) ∣ 1 := by simpa using hdvd
          exact_mod_cast hdvdZ) (by simpa only [r₁, r₂] using hrem)
    have hv' : padicValInt p
        (sameClassClearedFamily b g s₁ n J -
          sameClassClearedFamily b g s₂ n J) = min (a * r₁) (a * r₂) := by
      simpa only [sub_eq_add_neg, neg_mul, one_mul, a, r₁, r₂] using hv
    rw [hv']
    have hmin : min (a * r₁) (a * r₂) ≤ a * r₁ := min_le_left _ _
    have hrmul : a * r₁ ≤ a * s₁ := Nat.mul_le_mul_left a hr₁.le
    calc
      min (a * r₁) (a * r₂) ≤ a * r₁ := hmin
      _ ≤ a * s₁ := hrmul
      _ ≤ a * (s₁ + s₂) := Nat.mul_le_mul_left a (Nat.le_add_right s₁ s₂)

/-- The aligned numerator of a sufficiently deep literal same-class difference is nonzero. -/
lemma sameClassPair_sub_ne_zero
    (p b g s₁ s₂ n J : ℕ) (hp : p.Prime) (hg0 : g ≠ 0) (hpg : p ∣ g)
    (hgb : Nat.Coprime g b) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (hsne : s₁ ≠ s₂)
    (hK₁ : 2 ≤ J / s₁) (hK₂ : 2 ≤ J / s₂)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 (J / s₁), (g ^ s₁) ^ j ≤ n)
    (hentered₂ : ∀ j ∈ Finset.Icc 1 (J / s₂), (g ^ s₂) ^ j ≤ n) :
    sameClassClearedFamily b g s₁ n J -
        sameClassClearedFamily b g s₂ n J ≠ 0 := by
  let A₁ := sameClassClearedFamily b g s₁ n J
  let A₂ := sameClassClearedFamily b g s₂ n J
  let a := g.factorization p
  let r₁ := J - s₁ * (J / s₁)
  let r₂ := J - s₂ * (J / s₂)
  have ha : 0 < a := Nat.pos_of_ne_zero (by
    dsimp only [a]
    simpa [Nat.factorization_eq_zero_iff, hp, hpg] using hg0)
  by_cases hrem : r₁ = r₂
  · have hv := padicValInt_sameClassPair_sub_eq_of_remainder_eq
      p b g s₁ s₂ n J hp hg0 hpg hgb hsne hK₁ hK₂ hentered₁ hentered₂ (by
        simpa only [r₁, r₂] using hrem)
    intro hzero
    rw [show A₁ - A₂ = 0 by simpa only [A₁, A₂] using hzero] at hv
    have hpos : 0 < a * r₁ + min (a * s₁) (a * s₂) := by
      have h₁ : 0 < a * s₁ := Nat.mul_pos ha (by omega)
      have h₂ : 0 < a * s₂ := Nat.mul_pos ha (by omega)
      exact Nat.add_pos_right _ (lt_min h₁ h₂)
    simp only [padicValInt, Int.natAbs_zero, padicValNat.zero] at hv
    dsimp only [a, r₁] at hpos
    omega
  · have hA₁0 : A₁ ≠ 0 := sameClassClearedFamily_ne_zero
      p b g s₁ n J hp hg0 hpg hgb (by omega) hentered₁
    have hA₂0 : A₂ ≠ 0 := sameClassClearedFamily_ne_zero
      p b g s₂ n J hp hg0 hpg hgb (by omega) hentered₂
    have hv₁ : padicValInt p A₁ = a * r₁ := by
      simpa only [A₁, a, r₁] using padicValInt_sameClassClearedFamily
        p b g s₁ n J hp hg0 hpg hgb (by omega) hentered₁
    have hv₂ : padicValInt p (-A₂) = a * r₂ := by
      have hraw := padicValInt_sameClassClearedFamily
        p b g s₂ n J hp hg0 hpg hgb (by omega) hentered₂
      simpa only [padicValInt, Int.natAbs_neg, A₂, a, r₂] using hraw
    have hval : padicValInt p A₁ ≠ padicValInt p (-A₂) := by
      rw [hv₁, hv₂]
      exact fun heq => hrem (Nat.eq_of_mul_eq_mul_left ha heq)
    simpa only [A₁, A₂, sub_eq_add_neg] using
      add_ne_zero_of_padicValInt_ne p A₁ (-A₂) hval

/-- At an odd prime of the common base, the bounded aligned-numerator loss leaves a linearly
growing prime power in the reduced denominator of a literal sum. -/
theorem prime_pow_depth_sub_bound_dvd_sameClassPair_add_den_of_ne_two
    (p b g s₁ s₂ n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hg : 2 ≤ g)
    (hpg : p ∣ g) (hgb : Nat.Coprime g b) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (hsumJ : s₁ + s₂ ≤ Nat.log g n) :
    p ^ (g.factorization p * Nat.log g n - g.factorization p * (s₁ + s₂)) ∣
      ((∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₁) n),
          (b : ℚ) ^ (n - (g ^ s₁) ^ j) / ((g ^ s₁ : ℕ) : ℚ) ^ j) +
        ∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₂) n),
          (b : ℚ) ^ (n - (g ^ s₂) ^ j) / ((g ^ s₂ : ℕ) : ℚ) ^ j).den := by
  let J := Nat.log g n
  let A : ℤ := sameClassClearedFamily b g s₁ n J +
    sameClassClearedFamily b g s₂ n J
  let D : ℕ := g ^ J
  let q : ℚ :=
    (∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₁) n),
        (b : ℚ) ^ (n - (g ^ s₁) ^ j) / ((g ^ s₁ : ℕ) : ℚ) ^ j) +
      ∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₂) n),
        (b : ℚ) ^ (n - (g ^ s₂) ^ j) / ((g ^ s₂ : ℕ) : ℚ) ^ j
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    simp [J] at hsumJ
    omega
  have hK₁ : 1 ≤ J / s₁ := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    dsimp only [J]
    omega
  have hK₂ : 1 ≤ J / s₂ := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    dsimp only [J]
    omega
  have hentered₁ : ∀ j ∈ Finset.Icc 1 (J / s₁), (g ^ s₁) ^ j ≤ n := by
    intro j hj
    have hjlog : j ≤ Nat.log (g ^ s₁) n := by
      simpa only [Nat.log_pow_left, J] using (Finset.mem_Icc.mp hj).2
    exact (Nat.pow_le_pow_right (by positivity) hjlog).trans
      (Nat.pow_log_le_self (g ^ s₁) hn0)
  have hentered₂ : ∀ j ∈ Finset.Icc 1 (J / s₂), (g ^ s₂) ^ j ≤ n := by
    intro j hj
    have hjlog : j ≤ Nat.log (g ^ s₂) n := by
      simpa only [Nat.log_pow_left, J] using (Finset.mem_Icc.mp hj).2
    exact (Nat.pow_le_pow_right (by positivity) hjlog).trans
      (Nat.pow_log_le_self (g ^ s₂) hn0)
  have hlocal := sameClassPair_add_ne_zero_and_val_le_of_ne_two
    p b g s₁ s₂ n J hp hp2 (by omega) hpg hgb hs₁ hs₂ hK₁ hK₂
      hentered₁ hentered₂
  have hA : A ≠ 0 := by simpa only [A] using hlocal.1
  have hvA : padicValInt p A ≤ g.factorization p * (s₁ + s₂) := by
    simpa only [A] using hlocal.2
  have hD : D ≠ 0 := pow_ne_zero _ (by omega)
  have hq : q = (A : ℚ) / (D : ℚ) := by
    dsimp only [q, A, D, J]
    simpa only [Int.cast_add, Int.cast_one, one_mul, Nat.cast_pow] using
      stonehamSameClassPair_eq_cleared_div b g s₁ s₂ n 1 (by omega) hs₁ hs₂
  letI : Fact p.Prime := ⟨hp⟩
  have hvD : padicValNat p D = g.factorization p * J := by
    dsimp only [D]
    rw [padicValNat.pow, ← Nat.factorization_def g hp]
    ac_rfl
  have hBE : g.factorization p * (s₁ + s₂) ≤ g.factorization p * J :=
    Nat.mul_le_mul_left _ (by simpa only [J] using hsumJ)
  have hdiv := prime_pow_sub_bound_dvd_rat_den_of_eq_div
    p (g.factorization p * J) (g.factorization p * (s₁ + s₂)) A D q hp
      hA hD hq hvA hvD hBE
  simpa only [q, J] using hdiv

/-- For two unequal powers of two, the dyadic periodic-tail estimate likewise leaves a
linearly growing power of two in the reduced denominator of the literal sum. -/
theorem two_pow_depth_sub_bound_dvd_sameClassPair_add_den
    (b s₁ s₂ n : ℕ) (hb : Odd b) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (hsne : s₁ ≠ s₂) (hsumJ : s₁ + s₂ ≤ Nat.log 2 n) :
    2 ^ (Nat.log 2 n - (s₁ + s₂)) ∣
      ((∑ j ∈ Finset.Icc 1 (Nat.log (2 ^ s₁) n),
          (b : ℚ) ^ (n - (2 ^ s₁) ^ j) / ((2 ^ s₁ : ℕ) : ℚ) ^ j) +
        ∑ j ∈ Finset.Icc 1 (Nat.log (2 ^ s₂) n),
          (b : ℚ) ^ (n - (2 ^ s₂) ^ j) / ((2 ^ s₂ : ℕ) : ℚ) ^ j).den := by
  let J := Nat.log 2 n
  let A : ℤ := sameClassClearedFamily b 2 s₁ n J +
    sameClassClearedFamily b 2 s₂ n J
  let D : ℕ := 2 ^ J
  let q : ℚ :=
    (∑ j ∈ Finset.Icc 1 (Nat.log (2 ^ s₁) n),
        (b : ℚ) ^ (n - (2 ^ s₁) ^ j) / ((2 ^ s₁ : ℕ) : ℚ) ^ j) +
      ∑ j ∈ Finset.Icc 1 (Nat.log (2 ^ s₂) n),
        (b : ℚ) ^ (n - (2 ^ s₂) ^ j) / ((2 ^ s₂ : ℕ) : ℚ) ^ j
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    simp [J] at hsumJ
    omega
  have hK₁ : 1 ≤ J / s₁ := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    dsimp only [J]
    omega
  have hK₂ : 1 ≤ J / s₂ := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    dsimp only [J]
    omega
  have hentered₁ : ∀ j ∈ Finset.Icc 1 (J / s₁), (2 ^ s₁) ^ j ≤ n := by
    intro j hj
    have hjlog : j ≤ Nat.log (2 ^ s₁) n := by
      simpa only [Nat.log_pow_left, J] using (Finset.mem_Icc.mp hj).2
    exact (Nat.pow_le_pow_right (by positivity) hjlog).trans
      (Nat.pow_log_le_self (2 ^ s₁) hn0)
  have hentered₂ : ∀ j ∈ Finset.Icc 1 (J / s₂), (2 ^ s₂) ^ j ≤ n := by
    intro j hj
    have hjlog : j ≤ Nat.log (2 ^ s₂) n := by
      simpa only [Nat.log_pow_left, J] using (Finset.mem_Icc.mp hj).2
    exact (Nat.pow_le_pow_right (by positivity) hjlog).trans
      (Nat.pow_log_le_self (2 ^ s₂) hn0)
  have hlocal := sameClassPair_add_dyadic_ne_zero_and_val_le
    b s₁ s₂ n J hb hs₁ hs₂ hsne hK₁ hK₂ hentered₁ hentered₂ (by
      dsimp only [J]
      omega)
  have hA : A ≠ 0 := by simpa only [A] using hlocal.1
  have hvA : padicValInt 2 A ≤ s₁ + s₂ := by simpa only [A] using hlocal.2
  have hD : D ≠ 0 := pow_ne_zero _ (by norm_num)
  have hq : q = (A : ℚ) / (D : ℚ) := by
    dsimp only [q, A, D, J]
    simpa only [Int.cast_add, Int.cast_one, one_mul, Nat.cast_pow] using
      stonehamSameClassPair_eq_cleared_div b 2 s₁ s₂ n 1 (by norm_num) hs₁ hs₂
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hvD : padicValNat 2 D = J := by
    dsimp only [D]
    exact padicValNat.prime_pow (p := 2) J
  have hdiv := prime_pow_sub_bound_dvd_rat_den_of_eq_div
    2 J (s₁ + s₂) A D q (by norm_num) hA hD hq hvA hvD
      (by simpa only [J] using hsumJ)
  simpa only [q, J] using hdiv

/-- A reusable transfer from an eventual prime-power divisor of a literal pair denominator to
the exact two-family Stoneham state, including the fixed Fourier multiplier. -/
theorem eventually_pair_add_state_den_power_lower_of_eventual_dvd
    (p b g c₁ c₂ a B : ℕ) (h : ℤ) (hp : p.Prime) (hg : 2 ≤ g)
    (ha : 1 ≤ a) (hh : h ≠ 0)
    (hdiv : ∀ᶠ n : ℕ in Filter.atTop,
      p ^ (a * Nat.log g n - B) ∣
        ((∑ j ∈ Finset.Icc 1 (Nat.log c₁ n),
            (b : ℚ) ^ (n - c₁ ^ j) / (c₁ : ℚ) ^ j) +
          ∑ j ∈ Finset.Icc 1 (Nat.log c₂ n),
            (b : ℚ) ^ (n - c₂ ^ j) / (c₂ : ℚ) ^ j).den) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ (Real.log p / Real.log g) ≤
        (p ^ (B + padicValInt p h + 1) : ℕ) *
          (NormalNumbers.StonehamSumsNormal.stonehamState b 1
            ![c₁, c₂] ![1, 1] ![h, h] n).den := by
  let H := B + padicValInt p h
  filter_upwards [hdiv] with n hpair
  have hpair' : p ^ (a * Nat.log g n - B) ∣
      ((∑ j ∈ Finset.Icc 1 (Nat.log c₁ n),
          (b : ℚ) ^ (n - c₁ ^ j) / (c₁ : ℚ) ^ j) +
        (1 : ℚ) * (∑ j ∈ Finset.Icc 1 (Nat.log c₂ n),
          (b : ℚ) ^ (n - c₂ ^ j) / (c₂ : ℚ) ^ j)).den := by
    simpa only [one_mul] using hpair
  have hstateDiv : p ^ (a * Nat.log g n - H) ∣
      (NormalNumbers.StonehamSumsNormal.stonehamState b 1
        ![c₁, c₂] ![1, 1] ![h, h] n).den := by
    have hstate := prime_pow_sub_padicValInt_dvd_stonehamState_pair_one_den
      p (a * Nat.log g n - B) b c₁ c₂ n h 1 hp hh hpair'
    simpa only [one_mul, H, Nat.sub_sub] using hstate
  have hpowden : p ^ (a * Nat.log g n - H) ≤
      (NormalNumbers.StonehamSumsNormal.stonehamState b 1
        ![c₁, c₂] ![1, 1] ![h, h] n).den :=
    Nat.le_of_dvd (by positivity) hstateDiv
  calc
    (n : ℝ) ^ (Real.log p / Real.log g) ≤
        (p ^ (H + 1) : ℕ) * (p ^ (a * Nat.log g n - H) : ℕ) :=
      nat_rpow_log_ratio_le_prime_pow_mul_prime_pow_depth_sub p g n a H hp hg ha
    _ ≤ (p ^ (H + 1) : ℕ) *
        (NormalNumbers.StonehamSumsNormal.stonehamState b 1
          ![c₁, c₂] ![1, 1] ![h, h] n).den := by
      exact_mod_cast Nat.mul_le_mul_left (p ^ (H + 1)) hpowden
    _ = (p ^ (B + padicValInt p h + 1) : ℕ) *
        (NormalNumbers.StonehamSumsNormal.stonehamState b 1
          ![c₁, c₂] ![1, 1] ![h, h] n).den := by
      rfl

/-- Global positive-power state-denominator bound obtained from the preceding eventual
prime-power divisor transfer. -/
theorem exists_pair_add_state_den_power_lower_of_eventual_dvd
    (p b g c₁ c₂ a B : ℕ) (h : ℤ) (hp : p.Prime) (hg : 2 ≤ g)
    (ha : 1 ≤ a) (hh : h ≠ 0)
    (hdiv : ∀ᶠ n : ℕ in Filter.atTop,
      p ^ (a * Nat.log g n - B) ∣
        ((∑ j ∈ Finset.Icc 1 (Nat.log c₁ n),
            (b : ℚ) ^ (n - c₁ ^ j) / (c₁ : ℚ) ^ j) +
          ∑ j ∈ Finset.Icc 1 (Nat.log c₂ n),
            (b : ℚ) ^ (n - c₂ ^ j) / (c₂ : ℚ) ^ j).den) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ n : ℕ,
      (n : ℝ) ^ rho ≤ C *
        (NormalNumbers.StonehamSumsNormal.stonehamState b 1
          ![c₁, c₂] ![1, 1] ![h, h] n).den := by
  have hevent := eventually_pair_add_state_den_power_lower_of_eventual_dvd
    p b g c₁ c₂ a B h hp hg ha hh hdiv
  obtain ⟨C, hC, hbound⟩ := exists_global_power_lower_of_eventually
    (fun n => (NormalNumbers.StonehamSumsNormal.stonehamState b 1
      ![c₁, c₂] ![1, 1] ![h, h] n).den)
    (Real.log p / Real.log g)
    (p ^ (B + padicValInt p h + 1) : ℕ)
    (div_pos (Real.log_pos (by exact_mod_cast hp.one_lt))
      (Real.log_pos (by exact_mod_cast (show 1 < g by omega)))).le
    (by exact_mod_cast pow_pos hp.pos (B + padicValInt p h + 1))
    (fun n => (NormalNumbers.StonehamSumsNormal.stonehamState b 1
      ![c₁, c₂] ![1, 1] ![h, h] n).pos)
    hevent
  exact ⟨Real.log p / Real.log g, C,
    div_pos (Real.log_pos (by exact_mod_cast hp.one_lt))
      (Real.log_pos (by exact_mod_cast (show 1 < g by omega))), hC, hbound⟩

/-- Complete arithmetic output for a same-class literal sum at an odd prime divisor of the
common base. -/
theorem exists_sameClassPair_add_state_den_power_lower_at_odd_prime
    (p b g s₁ s₂ : ℕ) (h : ℤ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hg : 2 ≤ g) (hpg : p ∣ g) (hgb : Nat.Coprime g b)
    (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (hh : h ≠ 0) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ n : ℕ,
      (n : ℝ) ^ rho ≤ C *
        (NormalNumbers.StonehamSumsNormal.stonehamState b 1
          ![g ^ s₁, g ^ s₂] ![1, 1] ![h, h] n).den := by
  let a := g.factorization p
  let B := a * (s₁ + s₂)
  have ha : 1 ≤ a := by
    dsimp only [a]
    apply Nat.one_le_iff_ne_zero.mpr
    simpa [Nat.factorization_eq_zero_iff, hp, hpg] using (show g ≠ 0 by omega)
  have hdiv : ∀ᶠ n : ℕ in Filter.atTop,
      p ^ (a * Nat.log g n - B) ∣
        ((∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₁) n),
            (b : ℚ) ^ (n - (g ^ s₁) ^ j) / ((g ^ s₁ : ℕ) : ℚ) ^ j) +
          ∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₂) n),
            (b : ℚ) ^ (n - (g ^ s₂) ^ j) / ((g ^ s₂ : ℕ) : ℚ) ^ j).den := by
    filter_upwards [Filter.eventually_ge_atTop (g ^ (s₁ + s₂))] with n hn
    have hn0 : n ≠ 0 := ne_of_gt ((pow_pos (by omega) (s₁ + s₂)).trans_le hn)
    have hsumJ : s₁ + s₂ ≤ Nat.log g n :=
      (Nat.le_log_iff_pow_le (by omega) hn0).2 hn
    simpa only [a, B] using
      prime_pow_depth_sub_bound_dvd_sameClassPair_add_den_of_ne_two
        p b g s₁ s₂ n hp hp2 hg hpg hgb hs₁ hs₂ hsumJ
  exact exists_pair_add_state_den_power_lower_of_eventual_dvd
    p b g (g ^ s₁) (g ^ s₂) a B h hp hg ha hh hdiv

/-- Complete arithmetic output for a literal sum of two unequal powers of two. -/
theorem exists_dyadicPair_add_state_den_power_lower
    (b s₁ s₂ : ℕ) (h : ℤ) (hb : Odd b) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (hsne : s₁ ≠ s₂) (hh : h ≠ 0) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ n : ℕ,
      (n : ℝ) ^ rho ≤ C *
        (NormalNumbers.StonehamSumsNormal.stonehamState b 1
          ![2 ^ s₁, 2 ^ s₂] ![1, 1] ![h, h] n).den := by
  have hdiv : ∀ᶠ n : ℕ in Filter.atTop,
      2 ^ (Nat.log 2 n - (s₁ + s₂)) ∣
        ((∑ j ∈ Finset.Icc 1 (Nat.log (2 ^ s₁) n),
            (b : ℚ) ^ (n - (2 ^ s₁) ^ j) / ((2 ^ s₁ : ℕ) : ℚ) ^ j) +
          ∑ j ∈ Finset.Icc 1 (Nat.log (2 ^ s₂) n),
            (b : ℚ) ^ (n - (2 ^ s₂) ^ j) / ((2 ^ s₂ : ℕ) : ℚ) ^ j).den := by
    filter_upwards [Filter.eventually_ge_atTop (2 ^ (s₁ + s₂))] with n hn
    have hn0 : n ≠ 0 := ne_of_gt ((pow_pos (by norm_num) (s₁ + s₂)).trans_le hn)
    have hsumJ : s₁ + s₂ ≤ Nat.log 2 n :=
      (Nat.le_log_iff_pow_le (by norm_num) hn0).2 hn
    exact two_pow_depth_sub_bound_dvd_sameClassPair_add_den
      b s₁ s₂ n hb hs₁ hs₂ hsne hsumJ
  have hdiv' : ∀ᶠ n : ℕ in Filter.atTop,
      2 ^ (1 * Nat.log 2 n - (s₁ + s₂)) ∣
        ((∑ j ∈ Finset.Icc 1 (Nat.log (2 ^ s₁) n),
            (b : ℚ) ^ (n - (2 ^ s₁) ^ j) / ((2 ^ s₁ : ℕ) : ℚ) ^ j) +
          ∑ j ∈ Finset.Icc 1 (Nat.log (2 ^ s₂) n),
            (b : ℚ) ^ (n - (2 ^ s₂) ^ j) / ((2 ^ s₂ : ℕ) : ℚ) ^ j).den := by
    simpa only [one_mul] using hdiv
  simpa only [one_mul] using
    exists_pair_add_state_den_power_lower_of_eventual_dvd
      2 b 2 (2 ^ s₁) (2 ^ s₂) 1 (s₁ + s₂) h (by norm_num) (by norm_num)
        (by norm_num) hh hdiv'

/-- The bounded aligned-numerator loss leaves a linearly growing prime power in the reduced
denominator of every sufficiently deep literal same-class difference. -/
theorem prime_pow_depth_sub_bound_dvd_sameClassPair_sub_den
    (p b g s₁ s₂ n : ℕ) (hp : p.Prime) (hg : 2 ≤ g) (hpg : p ∣ g)
    (hgb : Nat.Coprime g b) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (hsne : s₁ ≠ s₂)
    (hK₁ : 2 ≤ Nat.log g n / s₁) (hK₂ : 2 ≤ Nat.log g n / s₂) :
    p ^ (g.factorization p * Nat.log g n - g.factorization p * (s₁ + s₂)) ∣
      ((∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₁) n),
          (b : ℚ) ^ (n - (g ^ s₁) ^ j) / ((g ^ s₁ : ℕ) : ℚ) ^ j) -
        ∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₂) n),
          (b : ℚ) ^ (n - (g ^ s₂) ^ j) / ((g ^ s₂ : ℕ) : ℚ) ^ j).den := by
  let J := Nat.log g n
  let A : ℤ := sameClassClearedFamily b g s₁ n J -
    sameClassClearedFamily b g s₂ n J
  let D : ℕ := g ^ J
  let q : ℚ :=
    (∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₁) n),
        (b : ℚ) ^ (n - (g ^ s₁) ^ j) / ((g ^ s₁ : ℕ) : ℚ) ^ j) -
      ∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₂) n),
        (b : ℚ) ^ (n - (g ^ s₂) ^ j) / ((g ^ s₂ : ℕ) : ℚ) ^ j
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    simp [J] at hK₁
  have hentered₁ : ∀ j ∈ Finset.Icc 1 (J / s₁), (g ^ s₁) ^ j ≤ n := by
    intro j hj
    have hjlog : j ≤ Nat.log (g ^ s₁) n := by
      simpa only [Nat.log_pow_left, J] using (Finset.mem_Icc.mp hj).2
    exact (Nat.pow_le_pow_right (by positivity) hjlog).trans
      (Nat.pow_log_le_self (g ^ s₁) hn0)
  have hentered₂ : ∀ j ∈ Finset.Icc 1 (J / s₂), (g ^ s₂) ^ j ≤ n := by
    intro j hj
    have hjlog : j ≤ Nat.log (g ^ s₂) n := by
      simpa only [Nat.log_pow_left, J] using (Finset.mem_Icc.mp hj).2
    exact (Nat.pow_le_pow_right (by positivity) hjlog).trans
      (Nat.pow_log_le_self (g ^ s₂) hn0)
  have hA : A ≠ 0 := by
    dsimp only [A]
    exact sameClassPair_sub_ne_zero p b g s₁ s₂ n J hp (by omega) hpg hgb
      hs₁ hs₂ hsne (by simpa only [J] using hK₁) (by simpa only [J] using hK₂)
      hentered₁ hentered₂
  have hD : D ≠ 0 := pow_ne_zero _ (by omega)
  have hq : q = (A : ℚ) / (D : ℚ) := by
    dsimp only [q, A, D, J]
    simpa [sub_eq_add_neg] using
      stonehamSameClassPair_eq_cleared_div b g s₁ s₂ n (-1) (by omega) hs₁ hs₂
  have hvA : padicValInt p A ≤ g.factorization p * (s₁ + s₂) := by
    dsimp only [A]
    exact padicValInt_sameClassPair_sub_le p b g s₁ s₂ n J hp (by omega) hpg hgb
      hs₁ hs₂ hsne (by simpa only [J] using hK₁) (by simpa only [J] using hK₂)
      hentered₁ hentered₂
  letI : Fact p.Prime := ⟨hp⟩
  have hvD : padicValNat p D = g.factorization p * J := by
    dsimp only [D]
    rw [padicValNat.pow, ← Nat.factorization_def g hp]
    ac_rfl
  have htwice₁ : 2 * s₁ ≤ J := by
    exact (Nat.le_div_iff_mul_le (by omega)).mp (by simpa only [J] using hK₁)
  have htwice₂ : 2 * s₂ ≤ J := by
    exact (Nat.le_div_iff_mul_le (by omega)).mp (by simpa only [J] using hK₂)
  have hsJ : s₁ + s₂ ≤ J := by omega
  have hBE : g.factorization p * (s₁ + s₂) ≤ g.factorization p * J :=
    Nat.mul_le_mul_left _ hsJ
  have hdiv := prime_pow_sub_bound_dvd_rat_den_of_eq_div
    p (g.factorization p * J) (g.factorization p * (s₁ + s₂)) A D q hp
      hA hD hq hvA hvD hBE
  simpa only [q, J] using hdiv

/-- The same-class difference denominator has a positive power lower bound eventually, after
the fixed aligned-tail loss and the fixed Fourier-multiplier loss. -/
theorem eventually_sameClassPair_sub_state_den_power_lower
    (p b g s₁ s₂ : ℕ) (h : ℤ) (hp : p.Prime) (hg : 2 ≤ g) (hpg : p ∣ g)
    (hgb : Nat.Coprime g b) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (hsne : s₁ ≠ s₂)
    (hh : h ≠ 0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ (Real.log p / Real.log g) ≤
        (p ^ (g.factorization p * (s₁ + s₂) + padicValInt p h + 1) : ℕ) *
          (NormalNumbers.StonehamSumsNormal.stonehamState b 1
            ![g ^ s₁, g ^ s₂] ![1, 1] ![h, -h] n).den := by
  let a := g.factorization p
  let B := a * (s₁ + s₂)
  let H := B + padicValInt p h
  let T := 2 * (s₁ + s₂) + H
  have ha : 1 ≤ a := by
    dsimp only [a]
    apply Nat.one_le_iff_ne_zero.mpr
    simpa [Nat.factorization_eq_zero_iff, hp, hpg] using (show g ≠ 0 by omega)
  filter_upwards [Filter.eventually_ge_atTop (g ^ T)] with n hn
  have hn0 : n ≠ 0 := ne_of_gt ((pow_pos (by omega) T).trans_le hn)
  have hTlog : T ≤ Nat.log g n :=
    (Nat.le_log_iff_pow_le (by omega) hn0).2 hn
  have hs₁log : 2 * s₁ ≤ Nat.log g n := by
    dsimp only [T] at hTlog
    omega
  have hs₂log : 2 * s₂ ≤ Nat.log g n := by
    dsimp only [T] at hTlog
    omega
  have hK₁ : 2 ≤ Nat.log g n / s₁ :=
    (Nat.le_div_iff_mul_le (by omega)).2 hs₁log
  have hK₂ : 2 ≤ Nat.log g n / s₂ :=
    (Nat.le_div_iff_mul_le (by omega)).2 hs₂log
  have hpair := prime_pow_depth_sub_bound_dvd_sameClassPair_sub_den
    p b g s₁ s₂ n hp hg hpg hgb hs₁ hs₂ hsne hK₁ hK₂
  let q : ℚ :=
    (∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₁) n),
        (b : ℚ) ^ (n - (g ^ s₁) ^ j) / ((g ^ s₁ : ℕ) : ℚ) ^ j) -
      ∑ j ∈ Finset.Icc 1 (Nat.log (g ^ s₂) n),
        (b : ℚ) ^ (n - (g ^ s₂) ^ j) / ((g ^ s₂ : ℕ) : ℚ) ^ j
  have hpair' : p ^ (a * Nat.log g n - B) ∣ q.den := by
    simpa only [a, B, q] using hpair
  have hstateDiv : p ^ (a * Nat.log g n - H) ∣
      (NormalNumbers.StonehamSumsNormal.stonehamState b 1
        ![g ^ s₁, g ^ s₂] ![1, 1] ![h, -h] n).den := by
    have hmul := prime_pow_sub_padicValInt_dvd_mul_den
      p (a * Nat.log g n - B) h q hp hh hpair'
    have hstate :
        NormalNumbers.StonehamSumsNormal.stonehamState b 1
            ![g ^ s₁, g ^ s₂] ![1, 1] ![h, -h] n = (h : ℚ) * q := by
      simpa [q, sub_eq_add_neg] using
        stonehamState_pair_one_eq b (g ^ s₁) (g ^ s₂) n h (-1)
    rw [hstate]
    simpa only [H, B, Nat.sub_sub] using hmul
  have hpowden : p ^ (a * Nat.log g n - H) ≤
      (NormalNumbers.StonehamSumsNormal.stonehamState b 1
        ![g ^ s₁, g ^ s₂] ![1, 1] ![h, -h] n).den :=
    Nat.le_of_dvd (by positivity) hstateDiv
  calc
    (n : ℝ) ^ (Real.log p / Real.log g) ≤
        (p ^ (H + 1) : ℕ) * (p ^ (a * Nat.log g n - H) : ℕ) :=
      nat_rpow_log_ratio_le_prime_pow_mul_prime_pow_depth_sub
        p g n a H hp hg ha
    _ ≤ (p ^ (H + 1) : ℕ) *
        (NormalNumbers.StonehamSumsNormal.stonehamState b 1
          ![g ^ s₁, g ^ s₂] ![1, 1] ![h, -h] n).den := by
      exact_mod_cast Nat.mul_le_mul_left (p ^ (H + 1)) hpowden
    _ = (p ^ (g.factorization p * (s₁ + s₂) + padicValInt p h + 1) : ℕ) *
        (NormalNumbers.StonehamSumsNormal.stonehamState b 1
          ![g ^ s₁, g ^ s₂] ![1, 1] ![h, -h] n).den := by
      rfl

/-- Global form of the preceding eventual estimate. -/
theorem exists_sameClassPair_sub_state_den_power_lower_at_prime
    (p b g s₁ s₂ : ℕ) (h : ℤ) (hp : p.Prime) (hg : 2 ≤ g) (hpg : p ∣ g)
    (hgb : Nat.Coprime g b) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (hsne : s₁ ≠ s₂)
    (hh : h ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (n : ℝ) ^ (Real.log p / Real.log g) ≤ C *
        (NormalNumbers.StonehamSumsNormal.stonehamState b 1
          ![g ^ s₁, g ^ s₂] ![1, 1] ![h, -h] n).den := by
  apply exists_global_power_lower_of_eventually
    (fun n => (NormalNumbers.StonehamSumsNormal.stonehamState b 1
      ![g ^ s₁, g ^ s₂] ![1, 1] ![h, -h] n).den)
    (Real.log p / Real.log g)
    (p ^ (g.factorization p * (s₁ + s₂) + padicValInt p h + 1) : ℕ)
  · exact (div_pos (Real.log_pos (by exact_mod_cast hp.one_lt))
      (Real.log_pos (by exact_mod_cast (show 1 < g by omega)))).le
  · exact_mod_cast pow_pos hp.pos
      (g.factorization p * (s₁ + s₂) + padicValInt p h + 1)
  · intro n
    exact (NormalNumbers.StonehamSumsNormal.stonehamState b 1
      ![g ^ s₁, g ^ s₂] ![1, 1] ![h, -h] n).pos
  · exact eventually_sameClassPair_sub_state_den_power_lower
      p b g s₁ s₂ h hp hg hpg hgb hs₁ hs₂ hsne hh

/-- Complete arithmetic output for a literal difference of two unequal powers in one
multiplicative class. -/
theorem exists_sameClassPair_sub_state_den_power_lower
    (b g s₁ s₂ : ℕ) (h : ℤ) (hg : 2 ≤ g) (hgb : Nat.Coprime g b)
    (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (hsne : s₁ ≠ s₂) (hh : h ≠ 0) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ n : ℕ,
      (n : ℝ) ^ rho ≤ C *
        (NormalNumbers.StonehamSumsNormal.stonehamState b 1
          ![g ^ s₁, g ^ s₂] ![1, 1] ![h, -h] n).den := by
  let p := g.minFac
  have hp : p.Prime := by
    dsimp only [p]
    exact Nat.minFac_prime (by omega)
  have hpg : p ∣ g := by
    dsimp only [p]
    exact Nat.minFac_dvd g
  obtain ⟨C, hC, hbound⟩ := exists_sameClassPair_sub_state_den_power_lower_at_prime
    p b g s₁ s₂ h hp hg hpg hgb hs₁ hs₂ hsne hh
  exact ⟨Real.log p / Real.log g, C,
    div_pos (Real.log_pos (by exact_mod_cast hp.one_lt))
      (Real.log_pos (by exact_mod_cast (show 1 < g by omega))), hC, hbound⟩

/-- A literal sum of two powers of one common base is normal as soon as that base has an odd
prime divisor. -/
theorem isNormal_stonehamAlpha_add_of_common_power_of_odd_prime
    (hV : Literature.VandeheyDiff.VandeheyThm51) (p b g s₁ s₂ : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpg : p ∣ g) (hb : 2 ≤ b) (hg : 2 ≤ g)
    (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (hcb₁ : Nat.Coprime (g ^ s₁) b) (hcb₂ : Nat.Coprime (g ^ s₂) b) :
    IsNormal b (stonehamAlpha b (g ^ s₁) + stonehamAlpha b (g ^ s₂)) := by
  have hgb : Nat.Coprime g b := Nat.Coprime.of_dvd_left
    (dvd_pow_self g (by omega)) hcb₁
  simpa using
    NormalNumbers.StonehamSumsNormal.isNormal_stonehamAlpha_pair_of_powerLower
      hV b (g ^ s₁) (g ^ s₂) 1 hb
        (Nat.one_lt_pow (by omega) (by omega))
        (Nat.one_lt_pow (by omega) (by omega)) hcb₁ hcb₂ (by norm_num) (fun h hh => by
          obtain ⟨rho, C, hrho, hC, hbound⟩ :=
            exists_sameClassPair_add_state_den_power_lower_at_odd_prime
              p b g s₁ s₂ h hp hp2 hg hpg hgb hs₁ hs₂ hh
          exact ⟨rho, C, hrho, hC, by
            simpa [NormalNumbers.StonehamSumsNormal.StonehamStateDenPowerLower] using hbound⟩)

/-- The genuinely dyadic literal sum of two unequal powers of two is normal. -/
theorem isNormal_stonehamAlpha_add_of_dyadic_powers
    (hV : Literature.VandeheyDiff.VandeheyThm51) (b s₁ s₂ : ℕ)
    (hb : 2 ≤ b) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (hcb₁ : Nat.Coprime (2 ^ s₁) b) (hcb₂ : Nat.Coprime (2 ^ s₂) b)
    (hsne : s₁ ≠ s₂) :
    IsNormal b (stonehamAlpha b (2 ^ s₁) + stonehamAlpha b (2 ^ s₂)) := by
  have h2b : Nat.Coprime 2 b := Nat.Coprime.of_dvd_left
    (dvd_pow_self 2 (by omega)) hcb₁
  have hbodd : Odd b := h2b.odd_of_left
  simpa using
    NormalNumbers.StonehamSumsNormal.isNormal_stonehamAlpha_pair_of_powerLower
      hV b (2 ^ s₁) (2 ^ s₂) 1 hb
        (Nat.one_lt_pow (Nat.ne_of_gt hs₁) (by norm_num))
        (Nat.one_lt_pow (Nat.ne_of_gt hs₂) (by norm_num)) hcb₁ hcb₂ (by norm_num) (fun h hh => by
          obtain ⟨rho, C, hrho, hC, hbound⟩ :=
            exists_dyadicPair_add_state_den_power_lower
              b s₁ s₂ h hbodd hs₁ hs₂ hsne hh
          exact ⟨rho, C, hrho, hC, by
            simpa [NormalNumbers.StonehamSumsNormal.StonehamStateDenPowerLower] using hbound⟩)

/-- A literal sum of unequal powers of one common base is normal.  Removing the entire
2-primary part of the common base exposes an odd prime unless the class is purely dyadic; in
that last case the powers are rewritten over base two and the dyadic tail theorem applies. -/
theorem isNormal_stonehamAlpha_add_of_common_power
    (hV : Literature.VandeheyDiff.VandeheyThm51) (b g s₁ s₂ : ℕ)
    (hb : 2 ≤ b) (hg : 2 ≤ g) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (hcb₁ : Nat.Coprime (g ^ s₁) b) (hcb₂ : Nat.Coprime (g ^ s₂) b)
    (hsne : s₁ ≠ s₂) :
    IsNormal b (stonehamAlpha b (g ^ s₁) + stonehamAlpha b (g ^ s₂)) := by
  let u := ordCompl[2] g
  by_cases hu : u = 1
  · let a := g.factorization 2
    have hdecomp := Nat.ordProj_mul_ordCompl_eq_self g 2
    have hgpow : g = 2 ^ a := by
      rw [show ordCompl[2] g = 1 by simpa only [u] using hu, mul_one] at hdecomp
      exact hdecomp.symm
    have ha : 1 ≤ a := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro ha0
      have : g = 1 := by simpa only [hgpow, ha0, pow_zero]
      omega
    have hc₁ : g ^ s₁ = 2 ^ (a * s₁) := by rw [hgpow, pow_mul]
    have hc₂ : g ^ s₂ = 2 ^ (a * s₂) := by rw [hgpow, pow_mul]
    have has₁ : 1 ≤ a * s₁ := Nat.mul_pos ha hs₁
    have has₂ : 1 ≤ a * s₂ := Nat.mul_pos ha hs₂
    have hasne : a * s₁ ≠ a * s₂ := by
      intro heq
      exact hsne (Nat.eq_of_mul_eq_mul_left (by omega) heq)
    have hcb₁' : Nat.Coprime (2 ^ (a * s₁)) b := by rwa [← hc₁]
    have hcb₂' : Nat.Coprime (2 ^ (a * s₂)) b := by rwa [← hc₂]
    rw [hc₁, hc₂]
    exact isNormal_stonehamAlpha_add_of_dyadic_powers
      hV b (a * s₁) (a * s₂) hb has₁ has₂ hcb₁' hcb₂' hasne
  · let p := u.minFac
    have hu0 : u ≠ 0 := ne_of_gt (by
      dsimp only [u]
      exact Nat.ordCompl_pos 2 (by omega))
    have hp : p.Prime := by
      dsimp only [p]
      exact Nat.minFac_prime (by omega)
    have hpu : p ∣ u := by
      dsimp only [p]
      exact Nat.minFac_dvd u
    have hpg : p ∣ g := hpu.trans (by
      dsimp only [u]
      exact Nat.ordCompl_dvd g 2)
    have hp2 : p ≠ 2 := by
      intro heq
      have h2u : 2 ∣ u := heq ▸ hpu
      exact (Nat.not_dvd_ordCompl (n := g) (p := 2) (by norm_num) (by omega)) (by
        simpa only [u] using h2u)
    exact isNormal_stonehamAlpha_add_of_common_power_of_odd_prime
      hV p b g s₁ s₂ hp hp2 hpg hb hg hs₁ hs₂ hcb₁ hcb₂

/-- A literal difference of unequal powers of one common base is normal. -/
theorem isNormal_stonehamAlpha_sub_of_common_power
    (hV : Literature.VandeheyDiff.VandeheyThm51) (b g s₁ s₂ : ℕ)
    (hb : 2 ≤ b) (hg : 2 ≤ g) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (hcb₁ : Nat.Coprime (g ^ s₁) b) (hcb₂ : Nat.Coprime (g ^ s₂) b)
    (hsne : s₁ ≠ s₂) :
    IsNormal b (stonehamAlpha b (g ^ s₁) - stonehamAlpha b (g ^ s₂)) := by
  have hgb : Nat.Coprime g b := Nat.Coprime.of_dvd_left
    (dvd_pow_self g (by omega)) hcb₁
  simpa [sub_eq_add_neg] using
    NormalNumbers.StonehamSumsNormal.isNormal_stonehamAlpha_pair_of_powerLower
      hV b (g ^ s₁) (g ^ s₂) (-1) hb
        (Nat.one_lt_pow (by omega) (by omega))
        (Nat.one_lt_pow (by omega) (by omega)) hcb₁ hcb₂ (by norm_num) (fun h hh => by
          obtain ⟨rho, C, hrho, hC, hbound⟩ :=
            exists_sameClassPair_sub_state_den_power_lower
              b g s₁ s₂ h hg hgb hs₁ hs₂ hsne hh
          exact ⟨rho, C, hrho, hC, by
            simpa [NormalNumbers.StonehamSumsNormal.StonehamStateDenPowerLower] using hbound⟩)

end NormalNumbers.StonehamPairsNormal
