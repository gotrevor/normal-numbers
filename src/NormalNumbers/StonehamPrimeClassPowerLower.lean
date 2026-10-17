/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamPrimeClassSchedule
import NormalNumbers.StonehamPairsDistinct
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
open Literature.VandeheyDiff NormalNumbers.G4

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

/-! ### Literal cleared-state bridge -/

/-- After all geometric denominators are multiplied in, the complete-history weights reduce
modulo the common depth to the fixed-pattern coefficients.  The discarded top term in family
`i` contains exactly `p ^ (δ i + s i * K i) = p ^ T`. -/
lemma primeClassPattern_history_modEq
    (p T : ℕ) {r : ℕ} (s K δ : Fin r → ℕ) (q R : Fin r → ℤ)
    (hp : p.Prime) (hT : ∀ i, δ i + s i * K i = T) :
    (∏ j, ((p : ℤ) ^ s j - 1)) *
        ∑ i, q i * (primeClassHistoryWeight p (s i) (K i) (δ i) : ℤ) * R i ≡
      -∑ i, primeClassPatternCoefficient p s q δ i * R i [ZMOD p ^ T] := by
  rw [mul_sum]
  rw [← sum_neg_distrib]
  apply Int.ModEq.sum
  intro i hi
  let G : ℤ := ∏ j ∈ (univ : Finset (Fin r)).erase i, ((p : ℤ) ^ s j - 1)
  have hprod : (∏ j, ((p : ℤ) ^ s j - 1)) = ((p : ℤ) ^ s i - 1) * G := by
    exact (mul_prod_erase (univ : Finset (Fin r))
      (fun j ↦ (p : ℤ) ^ s j - 1) (mem_univ i)).symm
  have hgeomNat := primeClassHistoryWeight_mul_sub_one p (s i) (K i) (δ i) hp
  have hps : 1 ≤ p ^ s i :=
    Nat.one_le_pow _ _ (Nat.one_le_iff_ne_zero.mpr hp.ne_zero)
  have hpK : 1 ≤ p ^ (s i * K i) :=
    Nat.one_le_pow _ _ (Nat.one_le_iff_ne_zero.mpr hp.ne_zero)
  have hgeom :
      ((p : ℤ) ^ s i - 1) *
          (primeClassHistoryWeight p (s i) (K i) (δ i) : ℤ) =
        (p : ℤ) ^ δ i * ((p : ℤ) ^ (s i * K i) - 1) := by
    exact_mod_cast hgeomNat
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-(q i * G * R i), ?_⟩
  rw [hprod]
  rw [show
    ((p : ℤ) ^ s i - 1) * G *
        (q i * (primeClassHistoryWeight p (s i) (K i) (δ i) : ℤ) * R i) =
      q i * G * R i * (((p : ℤ) ^ s i - 1) *
        (primeClassHistoryWeight p (s i) (K i) (δ i) : ℤ)) by ring]
  rw [hgeom]
  simp only [primeClassPatternCoefficient, G]
  have hpow : (p : ℤ) ^ δ i * (p : ℤ) ^ (s i * K i) = (p : ℤ) ^ T := by
    rw [← pow_add, hT i]
  rw [← hpow]
  ring

/-- Congruence beyond the valuation of a nonzero integer preserves its `p`-adic valuation. -/
lemma padicValInt_eq_of_modEq_pow
    (p E : ℕ) (A B : ℤ) (hp : p.Prime) (hB : B ≠ 0)
    (hmod : A ≡ B [ZMOD p ^ E]) (hval : padicValInt p B < E) :
    A ≠ 0 ∧ padicValInt p A = padicValInt p B := by
  letI : Fact p.Prime := ⟨hp⟩
  let v := padicValInt p B
  have hvE : v ≤ E := (Nat.le_of_lt hval)
  have hdiffE : (p : ℤ) ^ E ∣ B - A := hmod.dvd
  have hA : A ≠ 0 := by
    intro hzero
    subst A
    have hdiv : (p : ℤ) ^ E ∣ B := by simpa using hdiffE
    have hEle : E ≤ padicValInt p B :=
      ((padicValInt_dvd_iff E B).mp hdiv).resolve_left hB
    omega
  have hdiffv : (p : ℤ) ^ v ∣ B - A :=
    (pow_dvd_pow (p : ℤ) hvE).trans hdiffE
  have hBdiv : (p : ℤ) ^ v ∣ B := padicValInt_dvd B
  have hAdiv : (p : ℤ) ^ v ∣ A := by
    have := dvd_sub hBdiv hdiffv
    simpa only [sub_sub_cancel] using this
  have hvA : v ≤ padicValInt p A :=
    ((padicValInt_dvd_iff v A).mp hAdiv).resolve_left hA
  have hAv : padicValInt p A ≤ v := by
    by_contra hnot
    have hvoneA : v + 1 ≤ padicValInt p A := by omega
    have hvoneE : v + 1 ≤ E := by omega
    have hAdiv' : (p : ℤ) ^ (v + 1) ∣ A :=
      (padicValInt_dvd_iff (v + 1) A).mpr (Or.inr hvoneA)
    have hdiff' : (p : ℤ) ^ (v + 1) ∣ B - A :=
      (pow_dvd_pow (p : ℤ) hvoneE).trans hdiffE
    have hBdiv' : (p : ℤ) ^ (v + 1) ∣ B := by
      have := dvd_add hdiff' hAdiv'
      simpa only [sub_add_cancel] using this
    have := ((padicValInt_dvd_iff (v + 1) B).mp hBdiv').resolve_left hB
    omega
  exact ⟨hA, le_antisymm hAv hvA⟩

/-- The deleted finite-phase sum for an admissible gap pattern loses at most the uniform
resultant valuation.  The hypothesis `loss < E` places the comparison below every selected
top depth, so the literal deleted products and the single level-`E` evaluation have the same
valuation. -/
lemma padicValInt_deletedPhasePattern_le_loss
    (p b E : ℕ) {r : ℕ} (s u K : Fin r → ℕ) (q : Fin r → ℤ)
    (δ : ∀ i, Fin (u i + s i)) (ζ : ℂ)
    (hp : p.Prime) (hpb : Nat.Coprime p b) (hs : ∀ i, 1 ≤ s i)
    (hq : q ≠ 0)
    (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hind : LinearIndependent ℚ (fun i ↦ ζ ^ u i))
    (hdepth : ∀ i, E ≤ s i * K i)
    (hloss : primeClassPatternResultantLoss (orderOf (b : ZMod p)) p s u q < E) :
    (∑ i, primeClassPatternCoefficient p s q (fun j ↦ δ j) i *
        ∏ j ∈ (univ : Finset (Fin r)).erase i,
          ((b : ℤ) ^ (p ^ (s j * K j))) ^ u j) ≠ 0 ∧
      padicValInt p (∑ i, primeClassPatternCoefficient p s q (fun j ↦ δ j) i *
        ∏ j ∈ (univ : Finset (Fin r)).erase i,
          ((b : ℤ) ^ (p ^ (s j * K j))) ^ u j) ≤
        primeClassPatternResultantLoss (orderOf (b : ZMod p)) p s u q := by
  letI : Fact p.Prime := ⟨hp⟩
  let d := orderOf (b : ZMod p)
  let a : Fin r → ℤ := primeClassPatternCoefficient p s q (fun i ↦ δ i)
  let f : ℤ[X] := integerRelationPolynomial (primeClassComplementExponent u) a
  let g : ℤ[X] := cyclotomic d ℤ
  let z : ℤ := (b : ℤ) ^ (p ^ E)
  let R : ℤ := g.resultant f
  have hd : d ≠ 0 :=
    orderOf_ne_zero_iff.mpr ((ZMod.isUnit_iff_coprime b p).mpr hpb.symm).isOfFinOrder
  have hres : R ≠ 0 := by
    dsimp only [R, g, f, a, d]
    exact cyclotomic_resultant_primeClassPattern_ne_zero hd ζ hζ p s u q
      (fun i ↦ δ i) hp hs hq hind
  have hres_le : padicValInt p R ≤
      primeClassPatternResultantLoss d p s u q := by
    dsimp only [R, g, f, a]
    exact padicValInt_patternResultant_le_loss d p s u q δ
  have hres_lt : padicValInt p R < E := hres_le.trans_lt hloss
  have hgdeg : g.natDegree ≠ 0 := by
    dsimp only [g]
    rw [natDegree_cyclotomic]
    intro hzero
    exact hd (Nat.totient_eq_zero.mp hzero)
  have hroot : (p : ℤ) ^ E ∣ g.eval z := by
    dsimp only [g, z, d]
    exact prime_pow_dvd_cyclotomic_eval_teichmuller p b E hp hpb.symm
  have heval_le : padicValInt p (f.eval z) ≤ padicValInt p R := by
    exact StonehamPairsNormal.padicValInt_eval_le_resultant
      p E z f g hgdeg hres hroot hres_lt
  have heval_ne : f.eval z ≠ 0 := by
    intro heval0
    have hfdvd : (p : ℤ) ^ E ∣ f.eval z := by simp only [heval0, dvd_zero]
    have hrdvd := StonehamPairsNormal.dvd_resultant_of_dvd_eval
      ((p : ℤ) ^ E) z f g hgdeg hfdvd hroot
    have hEle : E ≤ padicValInt p R :=
      ((padicValInt_dvd_iff E R).mp hrdvd).resolve_left hres
    omega
  have hsum :
      (∑ i, a i * ∏ j ∈ (univ : Finset (Fin r)).erase i,
          ((b : ℤ) ^ (p ^ (s j * K j))) ^ u j) ≡
        f.eval z [ZMOD p ^ (E + 1)] := by
    rw [eval_integerRelationPolynomial]
    apply Int.ModEq.sum
    intro i hi
    exact (primeClassDeletedPhaseProduct_modEq p b E s u K i hp hdepth).mul_left (a i)
  have hsumE :
      (∑ i, a i * ∏ j ∈ (univ : Finset (Fin r)).erase i,
          ((b : ℤ) ^ (p ^ (s j * K j))) ^ u j) ≡
        f.eval z [ZMOD p ^ E] :=
    hsum.of_dvd (pow_dvd_pow (p : ℤ) (by omega))
  have hvaleq := padicValInt_eq_of_modEq_pow p E
    (∑ i, a i * ∏ j ∈ (univ : Finset (Fin r)).erase i,
      ((b : ℤ) ^ (p ^ (s j * K j))) ^ u j) (f.eval z) hp heval_ne hsumE
      (heval_le.trans_lt hres_lt)
  dsimp only [a] at hvaleq ⊢
  exact ⟨hvaleq.1, hvaleq.2.le.trans (heval_le.trans hres_le)⟩

/-- At sufficiently large common depth, the literal cleared-state numerator has valuation at
most the finite-pattern resultant loss.  The common phase product, the geometric-denominator
product, and `b ^ n` are all `p`-adic units, so the valuation bound for the deleted phase sum
passes unchanged to the actual numerator. -/
lemma padicValInt_primeClassClearedStateNumerator_le_loss
    (p b T n E : ℕ) {r : ℕ} (s u K : Fin r → ℕ) (q : Fin r → ℤ)
    (δ : ∀ i, Fin (u i + s i)) (ζ : ℂ)
    (hp : p.Prime) (hpb : Nat.Coprime p b) (hs : ∀ i, 1 ≤ s i)
    (hq : q ≠ 0)
    (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hind : LinearIndependent ℚ (fun i ↦ ζ ^ u i))
    (hK : ∀ i, StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i n = K i)
    (hT : ∀ i, (δ i : ℕ) + s i * K i = T)
    (hentered : ∀ i, ∀ k ∈ Icc 1 (K i), u i * p ^ (s i * k) ≤ n)
    (hdepth : ∀ i, E ≤ s i * K i)
    (hloss : primeClassPatternResultantLoss (orderOf (b : ZMod p)) p s u q < E) :
    primeClassClearedStateNumerator b p T n s u q ≠ 0 ∧
      padicValInt p (primeClassClearedStateNumerator b p T n s u q) ≤
        primeClassPatternResultantLoss (orderOf (b : ZMod p)) p s u q := by
  letI : Fact p.Prime := ⟨hp⟩
  let N : ℤ := primeClassClearedStateNumerator b p T n s u q
  let G : ℤ := ∏ i, ((p : ℤ) ^ s i - 1)
  let P : ℤ := ∏ i, ((b : ℤ) ^ (p ^ (s i * K i))) ^ u i
  let R : Fin r → ℤ := fun i ↦
    ∏ j ∈ (univ : Finset (Fin r)).erase i,
      ((b : ℤ) ^ (p ^ (s j * K j))) ^ u j
  let S : ℤ := ∑ i, primeClassPatternCoefficient p s q (fun j ↦ (δ j : ℕ)) i * R i
  obtain ⟨i₀, hi₀⟩ : ∃ i, q i ≠ 0 := by
    by_contra hnone
    apply hq
    funext i
    by_contra hi
    exact hnone ⟨i, hi⟩
  have hET : E ≤ T := by
    calc
      E ≤ s i₀ * K i₀ := hdepth i₀
      _ ≤ (δ i₀ : ℕ) + s i₀ * K i₀ := Nat.le_add_left _ _
      _ = T := hT i₀
  have hphase := primeClassClearedHistories_mul_phaseProduct_modEq
    p b T n s u K (fun i ↦ (δ i : ℕ)) q hp hT hentered
  rw [← primeClassClearedStateNumerator_eq_alignedHistories
    b p T n s u K (fun i ↦ (δ i : ℕ)) q hK hT] at hphase
  have hphaseT : N * P ≡
      (b : ℤ) ^ n * ∑ i,
        q i * (primeClassHistoryWeight p (s i) (K i) (δ i) : ℤ) * R i
        [ZMOD p ^ T] := by
    apply hphase.of_dvd (pow_dvd_pow (p : ℤ) (by omega))
  have hpattern :
      G * ∑ i, q i * (primeClassHistoryWeight p (s i) (K i) (δ i) : ℤ) * R i ≡
        -S [ZMOD p ^ T] := by
    simpa only [G, R, S] using primeClassPattern_history_modEq
      p T s K (fun i ↦ (δ i : ℕ)) q R hp hT
  have hmain : G * N * P ≡ -(b : ℤ) ^ n * S [ZMOD p ^ T] := by
    calc
      G * N * P = G * (N * P) := by ring
      _ ≡ G * ((b : ℤ) ^ n * ∑ i,
          q i * (primeClassHistoryWeight p (s i) (K i) (δ i) : ℤ) * R i)
          [ZMOD p ^ T] := hphaseT.mul_left G
      _ = (b : ℤ) ^ n * (G * ∑ i,
          q i * (primeClassHistoryWeight p (s i) (K i) (δ i) : ℤ) * R i) := by ring
      _ ≡ (b : ℤ) ^ n * (-S) [ZMOD p ^ T] := hpattern.mul_left ((b : ℤ) ^ n)
      _ = -(b : ℤ) ^ n * S := by ring
  obtain ⟨hS0, hSval⟩ := padicValInt_deletedPhasePattern_le_loss
    p b E s u K q δ ζ hp hpb hs hq hζ hind hdepth hloss
  have hbInt : ¬(p : ℤ) ∣ (b : ℤ) := by
    exact_mod_cast (hp.coprime_iff_not_dvd.mp hpb)
  have hGunit : ¬(p : ℤ) ∣ G := by
    dsimp only [G]
    apply (Nat.prime_iff_prime_int.mp hp).not_dvd_finsetProd
    intro i hi hdiv
    have hsp : s i ≠ 0 := Nat.one_le_iff_ne_zero.mp (hs i)
    have hpPow : (p : ℤ) ∣ (p : ℤ) ^ s i := dvd_pow_self _ hsp
    have hpOne : (p : ℤ) ∣ 1 := by
      simpa only [sub_sub_cancel] using dvd_sub hpPow hdiv
    exact (Nat.prime_iff_prime_int.mp hp).not_dvd_one hpOne
  have hPunit : ¬(p : ℤ) ∣ P := by
    dsimp only [P]
    apply (Nat.prime_iff_prime_int.mp hp).not_dvd_finsetProd
    intro i hi hdiv
    exact hbInt ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow
      ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hdiv))
  have hb0 : b ≠ 0 := by
    intro hb0
    subst b
    simp only [Nat.coprime_zero_right] at hpb
    exact hp.ne_one hpb
  have hbpow0 : (b : ℤ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hb0)
  have hrhs0 : -(b : ℤ) ^ n * S ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hbpow0) hS0
  have hrhsVal : padicValInt p (-(b : ℤ) ^ n * S) = padicValInt p S := by
    rw [padicValInt.mul (neg_ne_zero.mpr hbpow0) hS0]
    have hbpowUnit : ¬(p : ℤ) ∣ -(b : ℤ) ^ n := by
      intro hdiv
      exact hbInt ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow
        (dvd_neg.mp hdiv))
    rw [padicValInt.eq_zero_of_not_dvd hbpowUnit, zero_add]
  have hrhsLt : padicValInt p (-(b : ℤ) ^ n * S) < T := by
    rw [hrhsVal]
    exact (hSval.trans_lt hloss).trans_le hET
  obtain ⟨hlhs0, hvaleq⟩ :=
    padicValInt_eq_of_modEq_pow p T (G * N * P) (-(b : ℤ) ^ n * S)
      hp hrhs0 hmain hrhsLt
  have hN0 : N ≠ 0 := by
    intro hzero
    apply hlhs0
    simp only [hzero, mul_zero, zero_mul]
  have hG0 : G ≠ 0 := fun hzero ↦ hGunit (by simp [hzero])
  have hP0 : P ≠ 0 := fun hzero ↦ hPunit (by simp [hzero])
  have hlhsVal : padicValInt p (G * N * P) = padicValInt p N := by
    rw [padicValInt.mul (mul_ne_zero hG0 hN0) hP0,
      padicValInt.mul hG0 hN0,
      padicValInt.eq_zero_of_not_dvd hGunit,
      padicValInt.eq_zero_of_not_dvd hPunit]
    omega
  refine ⟨by simpa only [N] using hN0, ?_⟩
  dsimp only [N] at hlhsVal
  rw [← hlhsVal, hvaleq, hrhsVal]
  exact hSval

/-- The fixed loss in prime depth: the bounded scheduling gap plus the worst resultant
valuation among all gap patterns. -/
noncomputable def primeClassDenominatorLoss
    (d p : ℕ) {r : ℕ} (s u : Fin r → ℕ) (q : Fin r → ℤ) : ℕ :=
  (∑ i, (u i + s i)) + primeClassPatternResultantLoss d p s u q

/-- A fixed-loss prime power survives in the reduced denominator of every literal prime-class
Stoneham state.  This is the arithmetic interface needed by the Vandehey/Weyl engine. -/
theorem prime_pow_maxDepth_sub_loss_dvd_stonehamState_den
    (b p : ℕ) {r : ℕ} (s u : Fin r → ℕ) (q : Fin r → ℤ) (ζ : ℂ)
    (hp : p.Prime) (hpb : Nat.Coprime p b) (hs : ∀ i, 1 ≤ s i)
    (hu : ∀ i, 1 ≤ u i) (hq : q ≠ 0)
    (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hind : LinearIndependent ℚ (fun i ↦ ζ ^ u i)) (n : ℕ) :
    p ^ (primeClassMaxDepth p s u n -
        primeClassDenominatorLoss (orderOf (b : ZMod p)) p s u q) ∣
      (StonehamSumsNormal.stonehamState b 1 (fun i ↦ p ^ s i) u q n).den := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let d := orderOf (b : ZMod p)
  let B := primeClassPatternResultantLoss d p s u q
  let A := ∑ i, (u i + s i)
  let C := primeClassDenominatorLoss d p s u q
  let T := primeClassMaxDepth p s u n
  by_cases hsmall : T ≤ C
  · rw [Nat.sub_eq_zero_of_le hsmall, pow_zero]
    exact one_dvd _
  have hn : n ≠ 0 := by
    intro hn0
    subst n
    have hT0 : T = 0 := by
      simp [T, primeClassMaxDepth, primeClassWeightedDepth,
        StonehamSumsNormal.stonehamK]
    omega
  let K : Fin r → ℕ := fun i ↦
    StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i n
  let δ : ∀ i, Fin (u i + s i) := primeClassGapPattern p s u n hp hs hu hn
  let E := T - A
  have hK : ∀ i,
      StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i n = K i := fun _ ↦ rfl
  have hT : ∀ i, (δ i : ℕ) + s i * K i = T := by
    intro i
    have hle := primeClassWeightedDepth_le_maxDepth p s u n i
    simpa only [δ, primeClassGapPattern_val, primeClassMaxDepthGap,
      primeClassWeightedDepth, K, T] using Nat.sub_add_cancel hle
  have hentered : ∀ i, ∀ k ∈ Icc 1 (K i), u i * p ^ (s i * k) ≤ n := by
    intro i k hk
    have hle := (StonehamSumsNormal.le_stonehamK_iff
      (fun j ↦ p ^ s j) u i n k (two_le_prime_pow p (s i) hp (hs i))
        (hu i) (mem_Icc.mp hk).1).mp (by simpa only [K] using (mem_Icc.mp hk).2)
    simpa only [pow_mul] using hle
  have hδA : ∀ i, (δ i : ℕ) ≤ A := by
    intro i
    have hlt := primeClassMaxDepthGap_lt p s u n hp hs hu hn i
    have hterm : u i + s i ≤ A := by
      dsimp only [A]
      exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (u j + s j)) (mem_univ i)
    exact (Nat.le_of_lt (by simpa only [δ, primeClassGapPattern_val] using hlt)).trans hterm
  have hdepth : ∀ i, E ≤ s i * K i := by
    intro i
    have hi := hT i
    have hAi := hδA i
    dsimp only [E]
    omega
  have hCA : C = A + B := by rfl
  have hloss : B < E := by
    dsimp only [E]
    rw [hCA] at hsmall
    omega
  obtain ⟨hnum0, hnumVal⟩ := padicValInt_primeClassClearedStateNumerator_le_loss
    p b T n E s u K q δ ζ hp hpb hs hq hζ hind hK hT hentered hdepth
      (by simpa only [B, d] using hloss)
  have hTle : ∀ i, s i *
      StonehamSumsNormal.stonehamK (fun j ↦ p ^ s j) u i n ≤ T := by
    intro i
    simpa only [primeClassWeightedDepth, T] using
      primeClassWeightedDepth_le_maxDepth p s u n i
  have hstate := stonehamState_eq_primeClassClearedStateNumerator_div
    b p T n s u q hp hTle
  let v := padicValInt p (primeClassClearedStateNumerator b p T n s u q)
  have hBT : B ≤ T := by
    have hAB : B ≤ A + B := Nat.le_add_left B A
    rw [← hCA] at hAB
    exact hAB.trans (Nat.le_of_not_ge hsmall)
  have hvB : v ≤ B := by simpa only [v, B] using hnumVal
  have hvT : v ≤ T := hvB.trans hBT
  have hdenVal : padicValNat p (p ^ T) = v + (T - v) := by
    rw [padicValNat.prime_pow, Nat.add_sub_of_le hvT]
  have hstate' :
      StonehamSumsNormal.stonehamState b 1 (fun i ↦ p ^ s i) u q n =
        (primeClassClearedStateNumerator b p T n s u q : ℚ) / (p ^ T : ℕ) := by
    simpa only [Nat.cast_pow] using hstate
  have hfull : p ^ (T - v) ∣
      (StonehamSumsNormal.stonehamState b 1 (fun i ↦ p ^ s i) u q n).den := by
    apply StonehamPairsNormal.prime_pow_dvd_rat_den_of_eq_div
      p (T - v) v (primeClassClearedStateNumerator b p T n s u q) (p ^ T)
        (StonehamSumsNormal.stonehamState b 1 (fun i ↦ p ^ s i) u q n)
        hp hnum0 (pow_ne_zero _ hp.ne_zero) hstate'
        (by rfl) hdenVal
  have hexp : T - C ≤ T - v := by
    apply Nat.sub_le_sub_left
    exact hvB.trans (by rw [hCA]; exact Nat.le_add_left B A)
  exact (pow_dvd_pow p hexp).trans hfull

/-- The fixed-loss divisor has linear size in the orbit time.  Thus every nonzero integral
prime-class combination satisfying the cyclotomic independence criterion supplies the positive
power denominator hypothesis consumed by the analytic normality engine. -/
theorem exists_primeClass_stonehamStateDenPowerLower
    (b p : ℕ) {r : ℕ} (s u : Fin r → ℕ) (q : Fin r → ℤ) (ζ : ℂ)
    (hp : p.Prime) (hpb : Nat.Coprime p b) (hs : ∀ i, 1 ≤ s i)
    (hu : ∀ i, 1 ≤ u i) (hq : q ≠ 0)
    (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hind : LinearIndependent ℚ (fun i ↦ ζ ^ u i)) :
    ∃ C : ℝ, 0 < C ∧
      StonehamSumsNormal.StonehamStateDenPowerLower
        b 1 (fun i ↦ p ^ s i) u q 1 C := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, q i ≠ 0 := by
    by_contra hnone
    apply hq
    funext i
    by_contra hi
    exact hnone ⟨i, hi⟩
  let C₀ := primeClassDenominatorLoss (orderOf (b : ZMod p)) p s u q
  let C : ℝ := (p ^ (u i₀ + s i₀ + C₀) : ℕ)
  have hC : 0 < C := by
    dsimp only [C]
    exact_mod_cast pow_pos hp.pos (u i₀ + s i₀ + C₀)
  refine ⟨C, hC, ?_⟩
  intro n
  rw [Real.rpow_one]
  let T := primeClassMaxDepth p s u n
  have hdiv := prime_pow_maxDepth_sub_loss_dvd_stonehamState_den
    b p s u q ζ hp hpb hs hu hq hζ hind n
  have hpowden : p ^ (T - C₀) ≤
      (StonehamSumsNormal.stonehamState b 1 (fun i ↦ p ^ s i) u q n).den :=
    Nat.le_of_dvd (Rat.den_pos _) (by simpa only [T, C₀] using hdiv)
  have hnlt := orbitTime_lt_prime_pow_add_maxDepth p s u n hp hs hu i₀
  have hscale : p ^ (u i₀ + T + s i₀) ≤
      p ^ (u i₀ + s i₀ + C₀) * p ^ (T - C₀) := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right hp.pos
    omega
  have hnat : n ≤ p ^ (u i₀ + s i₀ + C₀) *
      (StonehamSumsNormal.stonehamState b 1 (fun i ↦ p ^ s i) u q n).den :=
    (Nat.le_of_lt hnlt).trans (hscale.trans (Nat.mul_le_mul_left _ hpowden))
  dsimp only [C]
  exact_mod_cast hnat

/-- Analytic completion for an integral prime-class combination whose coefficients are all
nonzero.  Fourier multiplication preserves both nonvanishing and the same cyclotomic
independence criterion; the preceding arithmetic theorem supplies a linear denominator bound
for each Fourier mode. -/
theorem isNormal_primeClassCombination_int_nonzero
    (hV : VandeheyThm51) (b p : ℕ) {r : ℕ} (s u : Fin r → ℕ)
    (q : Fin r → ℤ) (ζ : ℂ)
    (hp : p.Prime) (hb : 2 ≤ b) (hpb : Nat.Coprime p b)
    (hs : ∀ i, 1 ≤ s i) (hu : ∀ i, 1 ≤ u i) (hr : 1 ≤ r)
    (hq : ∀ i, q i ≠ 0)
    (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hind : LinearIndependent ℚ (fun i ↦ ζ ^ u i)) :
    IsNormal b (∑ i, (q i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i)) := by
  let x : ℝ := ∑ i, (q i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i)
  rw [isNormal_iff_equidistributed_orbit b hb]
  refine equidistributed_of_weyl _ (orbit_mem_Ico b _) ?_
  intro h hh
  let q' : Fin r → ℤ := fun i ↦ h * q i
  have hq' : ∀ i, q' i ≠ 0 := fun i => mul_ne_zero hh (hq i)
  have hq'fun : q' ≠ 0 := by
    intro hzero
    have hi := congrFun hzero (⟨0, hr⟩ : Fin r)
    exact hq' ⟨0, hr⟩ (by simpa only [Pi.zero_apply] using hi)
  obtain ⟨C, hC, hlower⟩ := exists_primeClass_stonehamStateDenPowerLower
    b p s u q' ζ hp hpb hs hu hq'fun hζ hind
  have hc : ∀ i, 2 ≤ p ^ s i := fun i => two_le_prime_pow p (s i) hp (hs i)
  have hcb : ∀ i, Nat.Coprime (p ^ s i) b := fun i => hpb.pow_left (s i)
  have hmean := StonehamSumsNormal.stonehamCombination_mean_tendsto_of_powerLower
    (StonehamSumsNormal.vandeheyCor12_of_thm51 hV)
    b 1 (fun i ↦ p ^ s i) u q' 1 C hb (by omega) (by simp) hr hc hu hcb hq'
      (by norm_num) hC hlower
  have heq : fourierMean (orbit b x) h = fun N : ℕ =>
      (∑ n ∈ range N, ePhase ((h : ℝ) * orbit b x n)) / (N : ℂ) := by
    funext N
    rw [fourierMean]
    congr 1
    apply sum_congr rfl
    intro n hn
    rw [ePhase]
    congr 1
    push_cast
    ring
  rw [heq]
  convert hmean using 1
  funext N
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [StonehamSumsNormal.ePhase_orbit]
  congr 1
  dsimp only [x, q']
  push_cast
  norm_num
  calc
    (h : ℝ) * ((b : ℝ) ^ n *
        ∑ i, (q i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i)) =
      (b : ℝ) ^ n * ((h : ℝ) *
        ∑ i, (q i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i)) := by ring
    _ = (b : ℝ) ^ n *
        ∑ i, (h : ℝ) * (q i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i) := by
      rw [Finset.mul_sum]
      simp only [mul_assoc]

/-- Zero coefficients can be discarded without changing the combination.  Linear independence
passes to the resulting subfamily, so every nonzero integral coefficient vector is normal. -/
theorem isNormal_primeClassCombination_int
    (hV : VandeheyThm51) (b p : ℕ) {r : ℕ} (s u : Fin r → ℕ)
    (q : Fin r → ℤ) (ζ : ℂ)
    (hp : p.Prime) (hb : 2 ≤ b) (hpb : Nat.Coprime p b)
    (hs : ∀ i, 1 ≤ s i) (hu : ∀ i, 1 ≤ u i) (hq : q ≠ 0)
    (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hind : LinearIndependent ℚ (fun i ↦ ζ ^ u i)) :
    IsNormal b (∑ i, (q i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i)) := by
  classical
  let S : Finset (Fin r) := univ.filter fun i ↦ q i ≠ 0
  let R : ℕ := Fintype.card S
  let e : Fin R ≃ S := (Fintype.equivFin S).symm
  let s' : Fin R → ℕ := fun j ↦ s (e j).1
  let u' : Fin R → ℕ := fun j ↦ u (e j).1
  let q' : Fin R → ℤ := fun j ↦ q (e j).1
  have hSnonempty : Nonempty S := by
    by_contra hempty
    apply hq
    funext i
    by_contra hi
    have his : i ∈ S := by
      dsimp only [S]
      exact mem_filter.mpr ⟨mem_univ i, hi⟩
    exact hempty ⟨i, his⟩
  have hR : 1 ≤ R := by
    dsimp only [R]
    exact Fintype.card_pos_iff.mpr hSnonempty
  have hs' : ∀ j, 1 ≤ s' j := fun j ↦ hs (e j).1
  have hu' : ∀ j, 1 ≤ u' j := fun j ↦ hu (e j).1
  have hq' : ∀ j, q' j ≠ 0 := by
    intro j
    have hj := (e j).property
    simpa only [S, mem_filter, mem_univ, true_and, q'] using hj
  have hind' : LinearIndependent ℚ (fun j ↦ ζ ^ u' j) := by
    have hcomp := hind.comp (fun j : Fin R ↦ (e j).1)
      (Subtype.val_injective.comp e.injective)
    change LinearIndependent ℚ
      ((fun i : Fin r ↦ ζ ^ u i) ∘ fun j : Fin R ↦ (e j).1)
    exact hcomp
  have hsum : (∑ i, (q i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i)) =
      ∑ j, (q' j : ℝ) * stonehamAlpha (b ^ u' j) (p ^ s' j) := by
    let f : Fin r → ℝ := fun i ↦
      (q i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i)
    calc
      ∑ i, (q i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i) = ∑ i ∈ S, f i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i hi hiS
        have hqi : q i = 0 := by
          simpa only [S, mem_filter, mem_univ, true_and, not_ne_iff] using hiS
        simp only [f, hqi, Int.cast_zero, zero_mul]
      _ = ∑ x : S, f x.1 := by
        exact (Finset.sum_coe_sort S f).symm
      _ = ∑ j : Fin R, f (e j).1 :=
        (Equiv.sum_comp e (fun x : S ↦ f x.1)).symm
      _ = ∑ j, (q' j : ℝ) * stonehamAlpha (b ^ u' j) (p ^ s' j) := by rfl
  rw [hsum]
  exact isNormal_primeClassCombination_int_nonzero
    hV b p s' u' q' ζ hp hb hpb hs' hu' hR hq' hζ hind'

/-- Clearing rational coefficients to one positive common denominator and scaling back by its
reciprocal extends the integral result to every nonzero rational coefficient vector. -/
theorem isNormal_primeClassCombination_rat
    (hV : VandeheyThm51) (b p : ℕ) {r : ℕ} (s u : Fin r → ℕ)
    (q : Fin r → ℚ) (ζ : ℂ)
    (hp : p.Prime) (hb : 2 ≤ b) (hpb : Nat.Coprime p b)
    (hs : ∀ i, 1 ≤ s i) (hu : ∀ i, 1 ≤ u i) (hq : q ≠ 0)
    (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hind : LinearIndependent ℚ (fun i ↦ ζ ^ u i)) :
    IsNormal b (∑ i, (q i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i)) := by
  classical
  let D : ℕ := ∏ i, (q i).den
  let a : Fin r → ℤ := fun i ↦ (D / (q i).den : ℕ) * (q i).num
  have hDpos : 0 < D := by
    dsimp only [D]
    exact Finset.prod_pos fun i _ ↦ (q i).pos
  have hden : ∀ i, (q i).den ∣ D := fun i ↦ by
    dsimp only [D]
    exact Finset.dvd_prod_of_mem (fun j ↦ (q j).den) (mem_univ i)
  have haq : ∀ i, (a i : ℝ) = (D : ℝ) * (q i : ℝ) := by
    intro i
    have hmul := Nat.div_mul_cancel (hden i)
    have hmulR : ((D / (q i).den : ℕ) : ℝ) * (q i).den = D := by
      exact_mod_cast hmul
    dsimp only [a]
    rw [Rat.cast_def]
    simp only [Int.cast_mul, Int.cast_natCast]
    have hdenR : ((q i).den : ℝ) ≠ 0 := by positivity
    field_simp [hdenR]
    linear_combination ((q i).num : ℝ) * hmulR
  have ha : a ≠ 0 := by
    intro ha0
    apply hq
    funext i
    have hai : a i = 0 := congrFun ha0 i
    have hqiR : (q i : ℝ) = 0 := by
      have hi := haq i
      rw [hai, Int.cast_zero] at hi
      exact (mul_eq_zero.mp hi.symm).resolve_left (by positivity)
    exact_mod_cast hqiR
  let x : ℝ := ∑ i, (q i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i)
  have hscaled : (∑ i, (a i : ℝ) * stonehamAlpha (b ^ u i) (p ^ s i)) =
      (D : ℝ) * x := by
    dsimp only [x]
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [haq i]
    ring
  have hn : IsNormal b ((D : ℝ) * x) := by
    rw [← hscaled]
    exact isNormal_primeClassCombination_int
      hV b p s u a ζ hp hb hpb hs hu ha hζ hind
  let c : ℚ := 1 / (D : ℚ)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact one_div_ne_zero (by exact_mod_cast hDpos.ne')
  have hout := isNormal_rat_mul_add b hb ((D : ℝ) * x) c 0 hc hn
  have hDR : (D : ℝ) ≠ 0 := by positivity
  convert hout using 1
  dsimp only [c, x]
  push_cast
  field_simp
  ring

/-- Concrete anchor: a singleton family has zero gap at every nonzero orbit time. -/
theorem primeClassMaxDepthGap_singleton_three (n : ℕ) :
    primeClassMaxDepthGap 3 ![1] ![1] n 0 = 0 := by
  simp [primeClassMaxDepthGap, primeClassMaxDepth, primeClassWeightedDepth]

end NormalNumbers.StonehamPrimeClass
