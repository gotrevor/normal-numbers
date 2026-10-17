/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamSumsBoundary
import NormalNumbers.StonehamPairsUnconditional
import NormalNumbers.StonehamPrimeClassFinite
import NormalNumbers.StonehamPrimeClassMahler
import NormalNumbers.StonehamPrimeClassState
import NormalNumbers.StonehamPrimeClassSchedule
import NormalNumbers.StonehamPrimeClassNonNormal
import NormalNumbers.VandeheyProof

/-!
# Joint normality of one prime class of Stoneham constants (Theorem T-B′)

Fix a prime `p ∤ b` and let `d = ord_p b`.  The family `α_{b^{mᵢ}, p^{sᵢ}}` is rationally jointly
`b`-normal (every nonzero `ℚ`-combination is `b`-normal) exactly when the powers `ζ^{mᵢ}` of a
primitive `d`-th root of unity are `ℚ`-linearly independent.  The exponents `sᵢ` play no role.
Since `ℚ(ζ)` has degree `φ(d)`, a jointly normal family has at most `φ(d)` members; for
`p ∈ {2, 3}` that is one.

`ζ` stands in for the Teichmüller lift `ω_p(b) ∈ ℤ_p`: both generate a copy of the `d`-th
cyclotomic field, and `ℚ`-linear independence of the `ζ^{mᵢ}` does not depend on the embedding.
For `p = 2`, `d = 1` and `ζ = 1`, matching the convention `ω₂ := 1`.

Source: `papers/2026-10-16-bailey-borwein-full-answer.md`, Theorem T-B′ and referee repair 1.
-/

namespace NormalNumbers.StonehamPrimeClass

/-- The prime-class Stoneham family `i ↦ α_{b^{mᵢ}, p^{sᵢ}}`. -/
noncomputable def primeClassFamily (b p : ℕ) {r : ℕ} (m s : Fin r → ℕ) : Fin r → ℝ :=
  fun i => stonehamAlpha (b ^ m i) (p ^ s i)

/-- **T-B′, non-normal half.**  If the `ζ^{mᵢ}` are `ℚ`-linearly dependent, some nonzero rational
combination of the family is not `b`-normal. -/
theorem not_isRationallyJointNormal_of_not_linearIndependent
    (b p : ℕ) (hp : p.Prime) (hb : 2 ≤ b) (hpb : Nat.Coprime p b)
    {r : ℕ} (m s : Fin r → ℕ) (hm : ∀ i, 1 ≤ m i) (hs : ∀ i, 1 ≤ s i)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hdep : ¬ LinearIndependent ℚ (fun i => ζ ^ m i)) :
    ¬ IsRationallyJointNormal b (primeClassFamily b p m s) := by
  classical
  intro hjoint
  let u : Fin r → ℕ := fun i ↦ primeClassReducedExponent p (s i) (m i)
  obtain ⟨a, ha, -, -, -, hrel₀, -⟩ :=
    exists_inverseMahlerWitness_of_not_linearIndependent
      b p hp hb hpb s m hs ζ hζ hdep
  have hrel : ∀ E, (p : ℤ) ^ E ∣ ∑ i,
      a i * ((b : ℤ) ^ (p ^ E)) ^ primeClassComplementExponent u i := by
    simpa only [u] using hrel₀
  have hu : ∀ i, 1 ≤ u i := by
    intro i
    apply Nat.one_le_iff_ne_zero.mpr
    intro hui
    have hfac : u i * (p ^ s i) ^ primeClassShiftCount p (s i) (m i) = m i := by
      simpa only [u] using primeClassReducedExponent_mul_pow p (s i) (m i)
    rw [hui, zero_mul] at hfac
    have hmi := hm i
    omega
  have ha_exists : ∃ i, a i ≠ 0 := by
    by_contra hnone
    apply ha
    funext i
    by_contra hai
    exact hnone ⟨i, hai⟩
  obtain ⟨i₀, hai₀⟩ := ha_exists
  have hseed : 1 ≤ primeClassScheduleSeed p s u := by
    have hterm : 1 ≤ u i₀ * p ^ s i₀ := by
      exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (Nat.one_le_iff_ne_zero.mp (hu i₀)) (pow_ne_zero _ hp.ne_zero))
    exact hterm.trans
      (Finset.single_le_sum (fun i _ ↦ Nat.zero_le (u i * p ^ s i))
        (Finset.mem_univ i₀))
  have hperiod : 1 ≤ primeClassScalePeriod s :=
    Nat.one_le_iff_ne_zero.mpr (primeClassScalePeriod_pos s hs).ne'
  let δ : Fin r → ℕ := primeClassScheduleGap p s u
  let D : ℕ := primeClassScheduleTop p s u
  let a' : Fin r → ℤ := fun i ↦
    primeClassStateCoefficient p (s i) (δ i) D (a i)
  have ha' : a' ≠ 0 := by
    intro hzero
    apply ha
    funext i
    by_contra hai
    have hne : a' i ≠ 0 := by
      dsimp only [a', δ, D]
      exact primeClassStateCoefficient_ne_zero p (s i)
        (primeClassScheduleGap p s u i) (primeClassScheduleTop p s u) (a i)
          hp (hs i) hai
    exact hne (by simpa only [Pi.zero_apply] using congrFun hzero i)
  let q : Fin r → ℚ := primeClassInverseMahlerCoefficient p s m a'
  have hq : q ≠ 0 := by
    simpa only [q] using primeClassInverseMahlerCoefficient_ne_zero p s m a' hp ha'
  have hnormalOriginal : IsNormal b
      (∑ i, (q i : ℝ) * stonehamAlpha (b ^ m i) (p ^ s i)) := by
    simpa only [primeClassFamily] using hjoint q hq
  have hnormalReduced : IsNormal b
      (∑ i, (a' i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i)) := by
    apply (isNormal_inverseMahlerCombination_iff b p s m a' hb hp hs).mp
    simpa only [q, u] using hnormalOriginal
  let x : ℝ := ∑ i, (a' i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i)
  let C : ℝ := ∑ i, |(a' i : ℝ)| * ((u i * p ^ s i : ℕ) : ℝ)
  have hnot : ¬ IsNormal b x := by
    apply not_isNormal_of_geometric_integer_approx b p (primeClassScalePeriod s)
      (primeClassScheduleSeed p s u) hb hp.two_le hperiod hseed x C
    intro t n hnlower hnupper hn
    obtain ⟨z, hz⟩ := primeClassSchedule_state_eq_int p b s u a hp hpb hs hu hrel
      t n hnlower hnupper
    refine ⟨z, ?_⟩
    have happ := StonehamSumsNormal.stonehamCombination_approx
      b 1 (fun i ↦ p ^ s i) u a' n hb (by norm_num)
        (fun i ↦ two_le_prime_pow p (s i) hp (hs i)) hu hn
    rw [hz] at happ
    simpa [x, C] using happ
  exact hnot (by simpa only [x] using hnormalReduced)

/-- **T-B′, normal half.**  If the `ζ^{mᵢ}` are `ℚ`-linearly independent, every nonzero rational
combination of the family is `b`-normal. -/
theorem isRationallyJointNormal_of_linearIndependent
    (b p : ℕ) (hp : p.Prime) (hb : 2 ≤ b) (hpb : Nat.Coprime p b)
    {r : ℕ} (m s : Fin r → ℕ) (hm : ∀ i, 1 ≤ m i) (hs : ∀ i, 1 ≤ s i)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hind : LinearIndependent ℚ (fun i => ζ ^ m i)) :
    IsRationallyJointNormal b (primeClassFamily b p m s) := by
  sorry

/-- **Theorem T-B′.**  A prime-class Stoneham family is rationally jointly normal exactly when the
`ζ^{mᵢ}` are `ℚ`-linearly independent. -/
theorem isRationallyJointNormal_iff_linearIndependent
    (b p : ℕ) (hp : p.Prime) (hb : 2 ≤ b) (hpb : Nat.Coprime p b)
    {r : ℕ} (m s : Fin r → ℕ) (hm : ∀ i, 1 ≤ m i) (hs : ∀ i, 1 ≤ s i)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p))) :
    IsRationallyJointNormal b (primeClassFamily b p m s) ↔
      LinearIndependent ℚ (fun i => ζ ^ m i) :=
  ⟨fun h => by
    by_contra hdep
    exact not_isRationallyJointNormal_of_not_linearIndependent b p hp hb hpb m s hm hs ζ hζ
      hdep h,
   isRationallyJointNormal_of_linearIndependent b p hp hb hpb m s hm hs ζ hζ⟩

/-- **Pairs.**  `α_{b^{m₁}, p^{s₁}}` and `α_{b^{m₂}, p^{s₂}}` are rationally jointly `b`-normal
exactly when `ord_p b ∤ 2(m₂ − m₁)`. -/
theorem isRationallyJointNormal_pair_iff
    (b p m₁ m₂ s₁ s₂ : ℕ) (hp : p.Prime) (hb : 2 ≤ b) (hpb : Nat.Coprime p b)
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) :
    IsRationallyJointNormal b
        ![stonehamAlpha (b ^ m₁) (p ^ s₁), stonehamAlpha (b ^ m₂) (p ^ s₂)] ↔
      ¬ ((orderOf (b : ZMod p) : ℤ) ∣ 2 * ((m₂ : ℤ) - m₁)) := by
  have hd : orderOf (b : ZMod p) ≠ 0 :=
    orderOf_ne_zero_iff.mpr ((ZMod.isUnit_iff_coprime b p).mpr hpb.symm).isOfFinOrder
  obtain ⟨ζ, hζ, hli⟩ := exists_primitiveRoot_linearIndependent_two_powers_iff
    (orderOf (b : ZMod p)) m₁ m₂ hd
  have hm : ∀ i : Fin 2, 1 ≤ ![m₁, m₂] i := by
    intro i
    fin_cases i <;> simp [hm₁, hm₂]
  have hs : ∀ i : Fin 2, 1 ≤ ![s₁, s₂] i := by
    intro i
    fin_cases i <;> simp [hs₁, hs₂]
  change IsRationallyJointNormal b (primeClassFamily b p ![m₁, m₂] ![s₁, s₂]) ↔ _
  refine (isRationallyJointNormal_iff_linearIndependent b p hp hb hpb
    ![m₁, m₂] ![s₁, s₂] hm hs ζ hζ).trans ?_
  have heq : (fun i : Fin 2 ↦ ζ ^ ![m₁, m₂] i) = ![ζ ^ m₁, ζ ^ m₂] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact hli

/-- **The L2 premise holds**: each pair in `α_{3,7}, α_{9,7}, α_{27,7}` is rationally jointly
`3`-normal (`ord_7 3 = 6` divides none of `2, 4`). -/
theorem stonehamThreeSevenPairwiseNormal_holds : StonehamThreeSevenPairwiseNormal := by
  have pair_apply {x y : ℝ} (h : IsRationallyJointNormal 3 ![x, y])
      (a c : ℚ) (hac : a ≠ 0 ∨ c ≠ 0) :
      IsNormal 3 ((a : ℝ) * x + (c : ℝ) * y) := by
    have hq : ![a, c] ≠ (0 : Fin 2 → ℚ) := by
      intro heq
      have ha := congrFun heq (0 : Fin 2)
      have hc := congrFun heq (1 : Fin 2)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at ha hc
      rcases hac with ha0 | hc0
      · exact ha0 ha
      · exact hc0 hc
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h ![a, c] hq
  have horder : orderOf (3 : ZMod 7) = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide +kernel
    · intro k hk hk0
      interval_cases k <;> decide +kernel
  have h₁₂ : IsRationallyJointNormal 3
      ![stonehamAlpha 3 7, stonehamAlpha 9 7] := by
    apply (isRationallyJointNormal_pair_iff 3 7 1 2 1 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
    change ¬ ((orderOf (3 : ZMod 7) : ℤ) ∣ _)
    rw [horder]
    norm_num
  have h₁₃ : IsRationallyJointNormal 3
      ![stonehamAlpha 3 7, stonehamAlpha 27 7] := by
    apply (isRationallyJointNormal_pair_iff 3 7 1 3 1 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
    change ¬ ((orderOf (3 : ZMod 7) : ℤ) ∣ _)
    rw [horder]
    norm_num
  have h₂₃ : IsRationallyJointNormal 3
      ![stonehamAlpha 9 7, stonehamAlpha 27 7] := by
    apply (isRationallyJointNormal_pair_iff 3 7 2 3 1 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
    change ¬ ((orderOf (3 : ZMod 7) : ℤ) ∣ _)
    rw [horder]
    norm_num
  intro i j hij a c hac
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · simpa [stonehamThreeSevenFamily] using pair_apply h₁₂ a c hac
  · simpa [stonehamThreeSevenFamily] using pair_apply h₁₃ a c hac
  · simpa [stonehamThreeSevenFamily, add_comm] using pair_apply h₁₂ c a hac.symm
  · exact (hij rfl).elim
  · simpa [stonehamThreeSevenFamily] using pair_apply h₂₃ a c hac
  · simpa [stonehamThreeSevenFamily, add_comm] using pair_apply h₁₃ c a hac.symm
  · simpa [stonehamThreeSevenFamily, add_comm] using pair_apply h₂₃ c a hac.symm
  · exact (hij rfl).elim

/-- **Joint normality is not pairwise**, unconditionally: the ternary triple is pairwise but not
jointly rationally `3`-normal. -/
theorem stonehamThreeSeven_pairwise_not_joint_unconditional :
    IsPairwiseRationallyJointNormal 3 stonehamThreeSevenFamily ∧
      ¬ IsRationallyJointNormal 3 stonehamThreeSevenFamily :=
  stonehamThreeSeven_pairwise_not_joint stonehamThreeSevenPairwiseNormal_holds

end NormalNumbers.StonehamPrimeClass
