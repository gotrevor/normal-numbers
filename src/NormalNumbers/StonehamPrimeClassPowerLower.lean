/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamPrimeClassSchedule
import NormalNumbers.StonehamPairsResultant

/-!
# Power-denominator preparation for one prime Stoneham class

For a mixed family with parameters `p ^ s i`, the weighted entered depths
`s i * K_i(n)` all lie in a fixed-width window.  This is the scheduling input needed to reduce
the denominator argument to finitely many gap patterns.  The bound here is deliberately coarse
but completely uniform in the orbit time: the gap below the maximum is less than `u i + s i`.
-/

namespace NormalNumbers.StonehamPrimeClass

open Finset Polynomial

/-- The `p`-adic depth of the `i`-th entered Stoneham history at orbit time `n`. -/
def primeClassWeightedDepth {r : ℕ} (p : ℕ) (s u : Fin r → ℕ) (n : ℕ)
    (i : Fin r) : ℕ :=
  s i * StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i n

/-- The largest weighted depth among a finite prime-class family. -/
def primeClassMaxDepth {r : ℕ} (p : ℕ) (s u : Fin r → ℕ) (n : ℕ) : ℕ :=
  (univ : Finset (Fin r)).sup (primeClassWeightedDepth p s u n)

/-- The gap of one family below the largest weighted depth. -/
def primeClassMaxDepthGap {r : ℕ} (p : ℕ) (s u : Fin r → ℕ) (n : ℕ)
    (i : Fin r) : ℕ :=
  primeClassMaxDepth p s u n - primeClassWeightedDepth p s u n i

/-- Every component depth lies below the family maximum. -/
lemma primeClassWeightedDepth_le_maxDepth
    {r : ℕ} (p : ℕ) (s u : Fin r → ℕ) (n : ℕ) (i : Fin r) :
    primeClassWeightedDepth p s u n i ≤ primeClassMaxDepth p s u n := by
  exact Finset.le_sup (f := primeClassWeightedDepth p s u n) (Finset.mem_univ i)

/-- A natural coefficient is bounded by the corresponding power of any prime base. -/
lemma coefficient_le_prime_pow_self (p a : ℕ) (hp : p.Prime) : a ≤ p ^ a := by
  exact (Nat.le_mul_of_pos_left a hp.pos).trans (Nat.mul_le_pow hp.ne_one a)

/-- The weighted depths of any two components differ by a time-independent amount.  The
asymmetric bound is tailored to the component whose denominator contribution will be retained.
-/
lemma primeClassWeightedDepth_lt_add
    {r : ℕ} (p : ℕ) (s u : Fin r → ℕ) (n : ℕ)
    (hp : p.Prime) (hs : ∀ i, 1 ≤ s i) (hu : ∀ i, 1 ≤ u i)
    (hn : n ≠ 0) (i j : Fin r) :
    primeClassWeightedDepth p s u n j <
      u i + primeClassWeightedDepth p s u n i + s i := by
  let c : Fin r → ℕ := fun k ↦ p ^ s k
  let K : Fin r → ℕ := fun k ↦ StonehamSumsNormal.stonehamK c u k n
  have hjpow : p ^ (s j * K j) ≤ n := by
    have h := StonehamSumsNormal.stonehamK_pow_le
      c u j n hn
    simpa only [c, K, pow_mul] using h
  have hiupper : n < u i * p ^ (s i * (K i + 1)) := by
    have h := StonehamSumsNormal.lt_mul_stonehamK_succ
      c u i n (two_le_prime_pow p (s i) hp (hs i)) (hu i)
    simpa only [c, K, pow_mul] using h
  have huPow : u i ≤ p ^ u i := coefficient_le_prime_pow_self p (u i) hp
  have hpow : p ^ (s j * K j) < p ^ (u i + s i * K i + s i) := by
    calc
      p ^ (s j * K j) ≤ n := hjpow
      _ < u i * p ^ (s i * (K i + 1)) := hiupper
      _ ≤ p ^ u i * p ^ (s i * (K i + 1)) := Nat.mul_le_mul_right _ huPow
      _ = p ^ (u i + s i * K i + s i) := by
        rw [← pow_add]
        congr 1
        simp only [Nat.mul_add, Nat.mul_one]
        exact (Nat.add_assoc _ _ _).symm
  have hexp : s j * K j < u i + s i * K i + s i :=
    (Nat.pow_lt_pow_iff_right hp.one_lt).mp hpow
  simpa only [primeClassWeightedDepth, c, K] using hexp

/-- Uniform bounded-gap scheduling lemma.  Consequently all possible max-depth gap vectors lie
in the fixed finite box `∏ i, Fin (u i + s i)` independently of `n`. -/
theorem primeClassMaxDepthGap_lt
    {r : ℕ} (p : ℕ) (s u : Fin r → ℕ) (n : ℕ)
    (hp : p.Prime) (hs : ∀ i, 1 ≤ s i) (hu : ∀ i, 1 ≤ u i)
    (hn : n ≠ 0) (i : Fin r) :
    primeClassMaxDepthGap p s u n i < u i + s i := by
  have htop : primeClassMaxDepth p s u n ≤
      u i + primeClassWeightedDepth p s u n i + s i - 1 := by
    unfold primeClassMaxDepth
    apply Finset.sup_le
    intro j hj
    have h := primeClassWeightedDepth_lt_add p s u n hp hs hu hn i j
    omega
  have hdepth := primeClassWeightedDepth_le_maxDepth p s u n i
  have hui := hu i
  have hsi := hs i
  unfold primeClassMaxDepthGap
  omega

/-- The bounded gap vector as an element of one fixed finite dependent product. -/
def primeClassGapPattern
    {r : ℕ} (p : ℕ) (s u : Fin r → ℕ) (n : ℕ)
    (hp : p.Prime) (hs : ∀ i, 1 ≤ s i) (hu : ∀ i, 1 ≤ u i)
    (hn : n ≠ 0) : ∀ i, Fin (u i + s i) :=
  fun i ↦ ⟨primeClassMaxDepthGap p s u n i,
    primeClassMaxDepthGap_lt p s u n hp hs hu hn i⟩

@[simp] lemma primeClassGapPattern_val
    {r : ℕ} (p : ℕ) (s u : Fin r → ℕ) (n : ℕ)
    (hp : p.Prime) (hs : ∀ i, 1 ≤ s i) (hu : ∀ i, 1 ≤ u i)
    (hn : n ≠ 0) (i : Fin r) :
    (primeClassGapPattern p s u n hp hs hu hn i : ℕ) =
      primeClassMaxDepthGap p s u n i := rfl

/-- The maximum weighted depth also has the correct logarithmic size: any chosen component
shows that the orbit time is smaller than a fixed power times `p ^ maxDepth`. -/
theorem orbitTime_lt_prime_pow_add_maxDepth
    {r : ℕ} (p : ℕ) (s u : Fin r → ℕ) (n : ℕ)
    (hp : p.Prime) (hs : ∀ i, 1 ≤ s i) (hu : ∀ i, 1 ≤ u i)
    (i : Fin r) :
    n < p ^ (u i + primeClassMaxDepth p s u n + s i) := by
  let c : Fin r → ℕ := fun k ↦ p ^ s k
  let K : Fin r → ℕ := fun k ↦ StonehamSumsNormal.stonehamK c u k n
  have hiupper : n < u i * p ^ (s i * (K i + 1)) := by
    have h := StonehamSumsNormal.lt_mul_stonehamK_succ
      c u i n (two_le_prime_pow p (s i) hp (hs i)) (hu i)
    simpa only [c, K, pow_mul] using h
  have huPow : u i ≤ p ^ u i := coefficient_le_prime_pow_self p (u i) hp
  have hdepth : s i * K i ≤ primeClassMaxDepth p s u n := by
    simpa only [primeClassWeightedDepth, c, K] using
      primeClassWeightedDepth_le_maxDepth p s u n i
  calc
    n < u i * p ^ (s i * (K i + 1)) := hiupper
    _ ≤ p ^ u i * p ^ (s i * (K i + 1)) := Nat.mul_le_mul_right _ huPow
    _ = p ^ (u i + s i * K i + s i) := by
      rw [← pow_add]
      congr 1
      simp only [Nat.mul_add, Nat.mul_one]
      exact (Nat.add_assoc _ _ _).symm
    _ ≤ p ^ (u i + primeClassMaxDepth p s u n + s i) := by
      apply Nat.pow_le_pow_right hp.pos
      omega

/-! ### Fixed-pattern resultant input -/

/-- Complementing every exponent in one common cap preserves linear independence.  This is the
inverse-phase orientation occurring after the finite Stoneham histories are cleared to a common
prime-power denominator. -/
lemma linearIndependent_powers_complement
    {d r : ℕ} (hd : d ≠ 0) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d)
    (u : Fin r → ℕ) (hind : LinearIndependent ℚ (fun i ↦ ζ ^ u i)) :
    LinearIndependent ℚ (fun i ↦ ζ ^ primeClassComplementExponent u i) := by
  have hinv : LinearIndependent ℚ (fun i ↦ (ζ⁻¹) ^ u i) :=
    (linearIndependent_powers_primitiveRoot_congr hd hζ hζ.inv u).mp hind
  rw [Fintype.linearIndependent_iff] at hinv ⊢
  intro q hq
  apply hinv q
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hd
  have hfactor :
      ∑ i, q i • ζ ^ primeClassComplementExponent u i =
        ζ ^ primeClassExponentCap u * ∑ i, q i • (ζ⁻¹) ^ u i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [primeClassComplementExponent,
      pow_sub₀ ζ hζ0 (primeClassExponent_le_cap u i), inv_pow]
    simp only [Algebra.smul_def]
    ring
  rw [hfactor] at hq
  exact (mul_eq_zero.mp hq).resolve_left (pow_ne_zero _ hζ0)

/-- The integral coefficient left at a fixed max-depth gap pattern after multiplying all
geometric denominators `(p ^ s i - 1)` into the cleared state.  The deleted product matches the
deleted finite-phase product, hence the complementary exponent. -/
def primeClassPatternCoefficient
    (p : ℕ) {r : ℕ} (s : Fin r → ℕ) (q : Fin r → ℤ) (δ : Fin r → ℕ)
    (i : Fin r) : ℤ :=
  q i * (p : ℤ) ^ δ i *
    ∏ j ∈ (univ : Finset (Fin r)).erase i, ((p : ℤ) ^ s j - 1)

/-- A nonzero Fourier coefficient vector remains nonzero after the fixed-pattern scaling. -/
lemma primeClassPatternCoefficient_ne_zero
    (p : ℕ) {r : ℕ} (s : Fin r → ℕ) (q : Fin r → ℤ) (δ : Fin r → ℕ)
    (hp : p.Prime) (hs : ∀ i, 1 ≤ s i) (hq : q ≠ 0) :
    primeClassPatternCoefficient p s q δ ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
    by_contra hnone
    apply hq
    funext i
    by_contra hi
    exact hnone ⟨i, hi⟩
  intro hzero
  have hscale : ∀ j, (p : ℤ) ^ s j - 1 ≠ 0 := by
    intro j h
    have hpow : 1 < p ^ s j :=
      Nat.one_lt_pow (Nat.ne_zero_of_lt (hs j)) hp.one_lt
    have : (p : ℤ) ^ s j ≠ 1 := by exact_mod_cast hpow.ne'
    exact this (sub_eq_zero.mp h)
  have hne : primeClassPatternCoefficient p s q δ i ≠ 0 := by
    unfold primeClassPatternCoefficient
    exact mul_ne_zero
      (mul_ne_zero hi (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)))
      (prod_ne_zero_iff.mpr (fun j hj ↦ hscale j))
  exact hne (by simpa only [Pi.zero_apply] using congrFun hzero i)

/-- Linear independence makes the cyclotomic resultant of every nonzero cleared coefficient
polynomial nonzero.  Applied to each member of the finite gap-pattern box, this gives the fixed
integer whose `p`-adic valuation bounds the loss at that pattern. -/
lemma cyclotomic_resultant_integerRelation_ne_zero
    {d r : ℕ} (hd : d ≠ 0) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d)
    (u : Fin r → ℕ) (a : Fin r → ℤ) (ha : a ≠ 0)
    (hind : LinearIndependent ℚ (fun i ↦ ζ ^ u i)) :
    (cyclotomic d ℤ).resultant (integerRelationPolynomial u a) ≠ 0 := by
  let _ : NeZero d := ⟨hd⟩
  apply StonehamPairsNormal.resultant_ne_zero_of_complex_root_nonvanishing
  · exact (cyclotomic.monic d ℤ).ne_zero
  · intro ξ hξ
    have hξprim : IsPrimitiveRoot ξ d := by
      apply isRoot_cyclotomic_iff.mp
      simpa only [map_cyclotomic] using hξ
    have hindξ : LinearIndependent ℚ (fun i ↦ ξ ^ u i) :=
      (linearIndependent_powers_primitiveRoot_congr hd hζ hξprim u).mp hind
    intro hzero
    have hsum : ∑ i, (Int.castRingHom ℂ) (a i) * ξ ^ u i = 0 := by
      rw [Polynomial.eval_map] at hzero
      rw [integerRelationPolynomial, eval₂_finsetSum] at hzero
      simpa only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X] using hzero
    have hcoeff : (fun i ↦ (a i : ℚ)) = 0 := by
      funext i
      apply (Fintype.linearIndependent_iff.mp hindξ) (fun i ↦ (a i : ℚ))
      convert hsum using 1
      all_goals simp [Algebra.smul_def]
    apply ha
    funext i
    have hi := congrFun hcoeff i
    simp only [Pi.zero_apply] at hi
    exact_mod_cast hi

/-- Every fixed gap pattern has a nonzero cyclotomic resultant in the complementary orientation.
These finitely many integers are the exact source of the uniform `p`-adic loss constant. -/
lemma cyclotomic_resultant_primeClassPattern_ne_zero
    {d r : ℕ} (hd : d ≠ 0) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d)
    (p : ℕ) (s u : Fin r → ℕ) (q : Fin r → ℤ) (δ : Fin r → ℕ)
    (hp : p.Prime) (hs : ∀ i, 1 ≤ s i) (hq : q ≠ 0)
    (hind : LinearIndependent ℚ (fun i ↦ ζ ^ u i)) :
    (cyclotomic d ℤ).resultant
        (integerRelationPolynomial (primeClassComplementExponent u)
          (primeClassPatternCoefficient p s q δ)) ≠ 0 := by
  apply cyclotomic_resultant_integerRelation_ne_zero hd ζ hζ
    (primeClassComplementExponent u) (primeClassPatternCoefficient p s q δ)
  · exact primeClassPatternCoefficient_ne_zero p s q δ hp hs hq
  · exact linearIndependent_powers_complement hd ζ hζ u hind

/-- The uniform cancellation loss obtained by maximizing the resultant valuation over the fixed
finite box of all max-depth gap patterns. -/
noncomputable def primeClassPatternResultantLoss
    (d p : ℕ) {r : ℕ} (s u : Fin r → ℕ) (q : Fin r → ℤ) : ℕ :=
  (univ : Finset (∀ i, Fin (u i + s i))).sup fun δ ↦
    padicValInt p <| (cyclotomic d ℤ).resultant
      (integerRelationPolynomial (primeClassComplementExponent u)
        (primeClassPatternCoefficient p s q (fun i ↦ δ i)))

/-- Every admissible pattern resultant has valuation at most the single finite-family loss. -/
lemma padicValInt_patternResultant_le_loss
    (d p : ℕ) {r : ℕ} (s u : Fin r → ℕ) (q : Fin r → ℤ)
    (δ : ∀ i, Fin (u i + s i)) :
    padicValInt p ((cyclotomic d ℤ).resultant
        (integerRelationPolynomial (primeClassComplementExponent u)
          (primeClassPatternCoefficient p s q (fun i ↦ δ i)))) ≤
      primeClassPatternResultantLoss d p s u q := by
  unfold primeClassPatternResultantLoss
  exact Finset.le_sup (f := fun δ : ∀ i, Fin (u i + s i) ↦
    padicValInt p <| (cyclotomic d ℤ).resultant
      (integerRelationPolynomial (primeClassComplementExponent u)
        (primeClassPatternCoefficient p s q (fun i ↦ δ i)))) (mem_univ δ)

/-- Concrete anchor: a singleton family has zero gap at every nonzero orbit time. -/
theorem primeClassMaxDepthGap_singleton_three (n : ℕ) :
    primeClassMaxDepthGap 3 ![1] ![1] n 0 = 0 := by
  simp [primeClassMaxDepthGap, primeClassMaxDepth, primeClassWeightedDepth]

end NormalNumbers.StonehamPrimeClass
