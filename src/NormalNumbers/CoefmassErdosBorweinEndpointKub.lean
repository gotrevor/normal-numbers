/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import Architect
import NormalNumbers.RealDefs
import NormalNumbers.CoefmassErdosBorweinEndpointEK
import NormalNumbers.CoefmassErdosBorweinEndpointKubAux
import PrimeNumberTheoremAnd.IEANTN.RosserSchoenfeld.RosserSchoenfeldPrime

/-!
# The Erdős–Borwein endpoint `a = ln 2` without FDEK (Kubilius-model route)

Statements copied verbatim from the KB packet `NNErdosBorweinRandom.lean`.  The literature input is
`KubiliusTV` (a named hypothesis, not an axiom).  Mertens' second theorem is available proved:
`RS_prime.mertens_second_theorem'` (PrimeNumberTheoremAnd).  Step 1 (the growing-moment criterion)
is `ebRandom_ae_normal_of_divisorVariance_diverges`.  Plan: `EB-ENDPOINT-KUB-NEXT.md`.
-/

namespace NormalNumbers.ErdosBorweinEndpointKub

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinPositive NormalNumbers.ErdosBorweinEndpoint
  NormalNumbers.ErdosBorweinEndpointEK

/-! ### An FDEK-free endpoint via the Kubilius model (personal-c5, 2026-10-25)

Replaces `ErdosKacFiniteDim`, whose theorem number is unverified, by the Kubilius-model
total-variation bound, whose citation is verified.  Ford, arXiv 2408.03803v4, Theorem A, quotes
Tenenbaum, Number Theory in Progress Vol. 2 (1999), pp. 1099–1129, Théorème 1.1 and (1.7):
`d_TV ≪_ε u^{-u} + x^{-1+ε}` for the prime-exponent vector, `p ≤ y ≤ x`, `u = log x / log y`.
`KubiliusTV` is its image under `v ↦ {p : v_p ≥ 1}` at `ε = 1/2`; TV only shrinks under a map.
On the model, the walk `ω(n; ≤ e^{e^u}) − u` is a sum of independent bounded variables, so the
Step 2 crossing needs no Gaussian limit (paper section "A route that replaces FDEK"). -/

/-- The primes `≤ y`. -/
def primesUpTo (y : ℕ) : Finset ℕ := (Finset.range (y + 1)).filter Nat.Prime

theorem primesUpTo_eq_filter_Iic (y : ℕ) :
    primesUpTo y = Finset.filter Nat.Prime (Finset.Iic y) := by
  ext p
  simp [primesUpTo]

/-- Mertens' second theorem in the exact natural-cutoff form used by the Kubilius model. -/
theorem mertens_primeReciprocalSum_bound :
    ∃ C : ℝ, ∀ y : ℕ, 2 ≤ y →
      |∑ p ∈ primesUpTo y, (1 / p : ℝ) - Real.log (Real.log y)| ≤ C := by
  obtain ⟨C, hC⟩ := RS_prime.mertens_second_theorem'
  refine ⟨C, fun y hy ↦ ?_⟩
  have h := hC (y : ℝ) (by exact_mod_cast hy)
  simpa [primesUpTo_eq_filter_Iic] using h

/-- The reciprocal-prime mass in `(a,b]` is the difference of the two prefix masses. -/
theorem primeReciprocalSum_block_eq_sub (a b : ℕ) (hab : a ≤ b) :
    ∑ p ∈ (primesUpTo b).filter (a < ·), (1 / p : ℝ) =
      (∑ p ∈ primesUpTo b, (1 / p : ℝ)) -
        ∑ p ∈ primesUpTo a, (1 / p : ℝ) := by
  have hsub : primesUpTo a ⊆ primesUpTo b := by
    intro p hp
    simp only [primesUpTo_eq_filter_Iic, Finset.mem_filter, Finset.mem_Iic] at hp ⊢
    exact ⟨hp.1.trans hab, hp.2⟩
  have hblock : (primesUpTo b).filter (a < ·) = primesUpTo b \ primesUpTo a := by
    ext p
    simp only [primesUpTo_eq_filter_Iic, Finset.mem_filter, Finset.mem_Iic,
      Finset.mem_sdiff]
    by_cases hpprime : p.Prime <;> simp [hpprime]
  rw [hblock]
  have hsum := Finset.sum_sdiff (s₁ := primesUpTo a) (s₂ := primesUpTo b)
    hsub (f := fun p ↦ (1 / p : ℝ))
  linarith

/-- Mertens gives a uniform lower bound for the reciprocal-prime mass of every natural block. -/
theorem mertens_primeReciprocalSum_block_lower :
    ∃ C : ℝ, ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      Real.log (Real.log b) - Real.log (Real.log a) - 2 * C ≤
        ∑ p ∈ (primesUpTo b).filter (a < ·), (1 / p : ℝ) := by
  obtain ⟨C, hC⟩ := mertens_primeReciprocalSum_bound
  refine ⟨C, fun a b ha hab ↦ ?_⟩
  have hb : 2 ≤ b := ha.trans hab
  have hCa := abs_le.mp (hC a ha)
  have hCb := abs_le.mp (hC b hb)
  rw [primeReciprocalSum_block_eq_sub a b hab]
  linarith

/-- On prime blocks, Bernoulli variance is at least half the reciprocal-prime mass.  Combined
with Mertens, this is the lower bound needed for every independent crossing block. -/
theorem mertens_primeVariance_block_lower :
    ∃ C : ℝ, ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      (1 / 2 : ℝ) *
          (Real.log (Real.log b) - Real.log (Real.log a) - 2 * C) ≤
        ∑ p ∈ (primesUpTo b).filter (a < ·),
          (1 / p : ℝ) * (1 - 1 / p) := by
  obtain ⟨C, hC⟩ := mertens_primeReciprocalSum_block_lower
  refine ⟨C, fun a b ha hab ↦ ?_⟩
  calc
    (1 / 2 : ℝ) *
        (Real.log (Real.log b) - Real.log (Real.log a) - 2 * C) ≤
        (1 / 2 : ℝ) *
          ∑ p ∈ (primesUpTo b).filter (a < ·), (1 / p : ℝ) := by
      gcongr
      exact hC a b ha hab
    _ = ∑ p ∈ (primesUpTo b).filter (a < ·),
          (1 / 2 : ℝ) * (1 / p : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ (primesUpTo b).filter (a < ·),
          (1 / p : ℝ) * (1 - 1 / p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpprime : p.Prime := by
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hpprime.two_le
      have hpinv : (1 / p : ℝ) ≤ 1 / 2 := by
        exact one_div_le_one_div_of_le (by norm_num) hpR
      have hhalf : (1 / 2 : ℝ) ≤ 1 - 1 / p := by linarith
      nlinarith [show (0 : ℝ) ≤ 1 / p by positivity]

/-- The variance of a prime prefix is at most its Mertens main term plus a fixed constant. -/
theorem mertens_primeVariance_prefix_upper :
    ∃ C : ℝ, ∀ y : ℕ, 2 ≤ y →
      ∑ p ∈ primesUpTo y, (1 / p : ℝ) * (1 - 1 / p) ≤
        Real.log (Real.log y) + C := by
  obtain ⟨C, hC⟩ := mertens_primeReciprocalSum_bound
  refine ⟨C, fun y hy ↦ ?_⟩
  calc
    ∑ p ∈ primesUpTo y, (1 / p : ℝ) * (1 - 1 / p) ≤
        ∑ p ∈ primesUpTo y, (1 / p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hq : (0 : ℝ) ≤ 1 / p := by positivity
      nlinarith
    _ ≤ Real.log (Real.log y) + C := by
      linarith [(abs_le.mp (hC y hy)).2]

open Classical in
/-- Intersecting the prime factors cut off at `y` with the primes up to `a ≤ y` recovers the
prime factors cut off at `a`. -/
theorem primeFactors_filter_inter_primesUpTo {n a y : ℕ} (hay : a ≤ y) :
    n.primeFactors.filter (· ≤ y) ∩ primesUpTo a = primeFactorsUpTo a n := by
  ext p
  simp only [Finset.mem_inter, Finset.mem_filter, primesUpTo_eq_filter_Iic,
    Finset.mem_Iic, primeFactorsUpTo]
  constructor
  · rintro ⟨⟨hpn, _⟩, hpa, _⟩
    exact ⟨hpn, hpa⟩
  · rintro ⟨hpn, hpa⟩
    exact ⟨⟨hpn, hpa.trans hay⟩, hpa, (Nat.mem_primeFactors.mp hpn).1⟩

open Classical in
/-- In the Kubilius coordinate set of an integer, a centered prime-prefix sum is its restricted
prime-factor count minus the reciprocal-prime mean. -/
theorem bernoulliCenteredSum_primesUpTo_primeFactors {n a y : ℕ} (hay : a ≤ y) :
    bernoulliCenteredSum (primesUpTo a) (fun p ↦ (1 / p : ℝ))
        (n.primeFactors.filter (· ≤ y)) =
      (omegaUpTo (a : ℝ) n : ℝ) - ∑ p ∈ primesUpTo a, (1 / p : ℝ) := by
  rw [bernoulliCenteredSum_eq_card_inter_sub_sum,
    primeFactors_filter_inter_primesUpTo hay, card_primeFactorsUpTo_eq_omegaUpTo]

open Classical in
/-- A centered prime-prefix sum splits into the prefix at `a` and the block `(a,b]`. -/
theorem bernoulliCenteredSum_primesUpTo_eq_add_block (S : Finset ℕ) {a b : ℕ}
    (hab : a ≤ b) :
    bernoulliCenteredSum (primesUpTo b) (fun p ↦ (1 / p : ℝ)) S =
      bernoulliCenteredSum (primesUpTo a) (fun p ↦ (1 / p : ℝ)) S +
        bernoulliCenteredSum ((primesUpTo b).filter (a < ·))
          (fun p ↦ (1 / p : ℝ)) S := by
  have hsub : primesUpTo a ⊆ primesUpTo b := by
    intro p hp
    simp only [primesUpTo_eq_filter_Iic, Finset.mem_filter, Finset.mem_Iic] at hp ⊢
    exact ⟨hp.1.trans hab, hp.2⟩
  have hblock : (primesUpTo b).filter (a < ·) = primesUpTo b \ primesUpTo a := by
    ext p
    simp only [primesUpTo_eq_filter_Iic, Finset.mem_filter, Finset.mem_Iic,
      Finset.mem_sdiff]
    by_cases hpprime : p.Prime <;> simp [hpprime]
  rw [hblock, ← bernoulliCenteredSum_union]
  · rw [Finset.union_sdiff_of_subset hsub]
  · exact Finset.disjoint_sdiff

open Classical in
/-- Mass of `A` under the Kubilius model: each prime `p ≤ y` is included independently with
probability `1/p`. -/
noncomputable def kubiliusMass (y : ℕ) (A : Set (Finset ℕ)) : ℝ :=
  ∑ S ∈ (primesUpTo y).powerset,
    if S ∈ A then ∏ p ∈ primesUpTo y, (if p ∈ S then (1 / p : ℝ) else 1 - 1 / p) else 0

open Classical in
theorem kubiliusMass_eq_bernoulliSubsetMass (y : ℕ) (A : Set (Finset ℕ)) :
    kubiliusMass y A =
      bernoulliSubsetMass (primesUpTo y) (fun p ↦ (1 / p : ℝ)) A := rfl

theorem kubiliusParameter_nonneg (y p : ℕ) (_hp : p ∈ primesUpTo y) :
    (0 : ℝ) ≤ 1 / p := by positivity

theorem kubiliusParameter_le_one (y p : ℕ) (hp : p ∈ primesUpTo y) :
    (1 / p : ℝ) ≤ 1 := by
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_le
  exact (div_le_one (by positivity)).mpr hpR

open Classical in
theorem kubiliusMass_univ (y : ℕ) : kubiliusMass y Set.univ = 1 := by
  rw [kubiliusMass_eq_bernoulliSubsetMass]
  exact bernoulliSubsetMass_univ _ _

open Classical in
theorem kubiliusMass_nonneg (y : ℕ) (A : Set (Finset ℕ)) : 0 ≤ kubiliusMass y A := by
  rw [kubiliusMass_eq_bernoulliSubsetMass]
  exact bernoulliSubsetMass_nonneg _ _ _
    (kubiliusParameter_nonneg y) (kubiliusParameter_le_one y)

open Classical in
theorem kubiliusMass_mono (y : ℕ) {A B : Set (Finset ℕ)} (hAB : A ⊆ B) :
    kubiliusMass y A ≤ kubiliusMass y B := by
  simp only [kubiliusMass_eq_bernoulliSubsetMass]
  exact bernoulliSubsetMass_mono _ _ hAB
    (kubiliusParameter_nonneg y) (kubiliusParameter_le_one y)

open Classical in
theorem kubiliusMass_le_one (y : ℕ) (A : Set (Finset ℕ)) : kubiliusMass y A ≤ 1 := by
  rw [kubiliusMass_eq_bernoulliSubsetMass]
  exact bernoulliSubsetMass_le_one _ _ _
    (kubiliusParameter_nonneg y) (kubiliusParameter_le_one y)

open Classical in
/-- Finite Kubilius mass is subadditive. -/
theorem kubiliusMass_union_le (y : ℕ) (A B : Set (Finset ℕ)) :
    kubiliusMass y (A ∪ B) ≤ kubiliusMass y A + kubiliusMass y B := by
  unfold kubiliusMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S hS
  have hweight : 0 ≤
      ∏ p ∈ primesUpTo y, if p ∈ S then (1 / p : ℝ) else 1 - 1 / p := by
    exact bernoulliSubsetWeight_nonneg (primesUpTo y) S (fun p ↦ (1 / p : ℝ))
      (kubiliusParameter_nonneg y) (kubiliusParameter_le_one y)
  by_cases hA : S ∈ A
  · by_cases hB : S ∈ B
    · simp only [Set.mem_union, hA, hB, true_or, if_true]
      simpa only [one_div] using le_add_of_nonneg_right hweight
    · simp [hA, hB]
  · by_cases hB : S ∈ B <;> simp [hA, hB]

open Classical in
/-- Union bound for a finite family of events in the Kubilius model. -/
theorem kubiliusMass_exists_mem_le_sum {ι : Type*} [DecidableEq ι]
    (y : ℕ) (I : Finset ι) (A : ι → Set (Finset ℕ)) :
    kubiliusMass y {S | ∃ i ∈ I, S ∈ A i} ≤ ∑ i ∈ I, kubiliusMass y (A i) := by
  induction I using Finset.induction_on with
  | empty => simp [kubiliusMass]
  | @insert i I hi ih =>
      have hevent : {S | ∃ j ∈ insert i I, S ∈ A j} =
          A i ∪ {S | ∃ j ∈ I, S ∈ A j} := by
        ext S
        simp
      rw [hevent, Finset.sum_insert hi]
      exact (kubiliusMass_union_le y _ _).trans (add_le_add le_rfl ih)

open Classical in
/-- Chebyshev's inequality for a centered sum on any prime-coordinate block inside the full
Kubilius model. -/
theorem kubiliusMass_blockCenteredSum_abs_ge_le (y : ℕ) (B : Finset ℕ)
    (hB : B ⊆ primesUpTo y) {r : ℝ} (hr : 0 < r) :
    kubiliusMass y {S | r ≤ |bernoulliCenteredSum B (fun p ↦ (1 / p : ℝ)) S|} ≤
      (∑ p ∈ B, (1 / p : ℝ) * (1 - 1 / p)) / r ^ 2 := by
  rw [kubiliusMass_eq_bernoulliSubsetMass]
  let A : Set (Finset ℕ) :=
    {S | r ≤ |bernoulliCenteredSum B (fun p ↦ (1 / p : ℝ)) S|}
  calc
    bernoulliSubsetMass (primesUpTo y) (fun p ↦ (1 / p : ℝ)) A =
        bernoulliSubsetMass (primesUpTo y) (fun p ↦ (1 / p : ℝ))
          {S | S ∩ B ∈ A} := by
      congr 1
      ext S
      simp only [A, Set.mem_ofPred_eq]
      rw [bernoulliCenteredSum_inter]
    _ = bernoulliSubsetMass B (fun p ↦ (1 / p : ℝ)) A :=
      bernoulliSubsetMass_inter (primesUpTo y) B hB _ A
    _ ≤ (∑ p ∈ B, (1 / p : ℝ) * (1 - 1 / p)) / r ^ 2 := by
      exact bernoulliSubsetMass_centeredSum_abs_ge_le B (fun p ↦ (1 / p : ℝ))
        (fun p hp ↦ by positivity)
        (fun p hp ↦ kubiliusParameter_le_one y p (hB hp)) hr

open Classical in
/-- Chebyshev's inequality for the selected-prime cardinality, centered at its reciprocal-prime
mean.  The intersection makes the statement valid for arbitrary ambient finite sets `S`. -/
theorem kubiliusMass_card_deviation_ge_le (y : ℕ) {r : ℝ} (hr : 0 < r) :
    kubiliusMass y
        {S | r ≤ |(((S ∩ primesUpTo y).card : ℝ) -
          ∑ p ∈ primesUpTo y, (1 / p : ℝ))|} ≤
      (∑ p ∈ primesUpTo y, (1 / p : ℝ) * (1 - 1 / p)) / r ^ 2 := by
  simpa only [bernoulliCenteredSum_eq_card_inter_sub_sum] using
    kubiliusMass_blockCenteredSum_abs_ge_le y (primesUpTo y) (fun _ hp ↦ hp) hr

open Classical in
/-- The number of selected primes has mean `∑_{p ≤ y} 1/p` in the Kubilius model. -/
theorem kubilius_card_expectation (y : ℕ) :
    ∑ S ∈ (primesUpTo y).powerset,
        bernoulliSubsetWeight (primesUpTo y) S (fun p ↦ (1 / p : ℝ)) * (S.card : ℝ) =
      ∑ p ∈ primesUpTo y, (1 / p : ℝ) :=
  bernoulliSubset_card_expectation _ _

open Classical in
/-- Every prime block of variance at least one has a fixed positive one-sided crossing mass in
the full Kubilius model. -/
theorem kubiliusMass_blockCenteredSum_ge_sqrt_eighth (y : ℕ) (B : Finset ℕ)
    (hB : B ⊆ primesUpTo y)
    (hV : 1 ≤ ∑ p ∈ B, (1 / p : ℝ) * (1 - 1 / p)) :
    (1 : ℝ) / 64 ≤ kubiliusMass y
      {S | Real.sqrt (∑ p ∈ B, (1 / p : ℝ) * (1 - 1 / p)) / 8 ≤
        bernoulliCenteredSum B (fun p ↦ (1 / p : ℝ)) S} := by
  rw [kubiliusMass_eq_bernoulliSubsetMass]
  exact bernoulliSubsetMass_blockCenteredSum_ge_sqrt_eighth
    (primesUpTo y) B hB (fun p ↦ (1 / p : ℝ))
    (fun p hp ↦ kubiliusParameter_nonneg y p (hB hp))
    (fun p hp ↦ kubiliusParameter_le_one y p (hB hp)) hV

open Classical in
/-- Pairwise-disjoint prime blocks amplify the one-block crossing estimate: the mass on which
every block misses its `sqrt(V)/8` crossing is at most `(63/64)^#blocks`. -/
theorem kubiliusMass_all_blockCenteredSum_lt_sqrt_eighth_le {ι : Type*} [DecidableEq ι]
    (y : ℕ) (I : Finset ι) (B : ι → Finset ℕ)
    (hBU : ∀ i ∈ I, B i ⊆ primesUpTo y)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j))
    (hV : ∀ i ∈ I, 1 ≤ ∑ p ∈ B i, (1 / p : ℝ) * (1 - 1 / p)) :
    kubiliusMass y
        {S | ∀ i ∈ I, bernoulliCenteredSum (B i) (fun p ↦ (1 / p : ℝ)) S <
          Real.sqrt (∑ p ∈ B i, (1 / p : ℝ) * (1 - 1 / p)) / 8} ≤
      ((63 : ℝ) / 64) ^ I.card := by
  rw [kubiliusMass_eq_bernoulliSubsetMass]
  exact bernoulliSubsetMass_all_blockCenteredSum_lt_sqrt_eighth_le
    (primesUpTo y) I B hBU hdisj (fun p ↦ (1 / p : ℝ))
    (kubiliusParameter_nonneg y) (kubiliusParameter_le_one y) hV

open Classical in
/-- The three exceptional events in the fixed-block Kubilius crossing argument: too many selected
primes, every block missing its positive increment, or an abnormally negative block start. -/
noncomputable def kubiliusBlockBadEvent {ι : Type*} [DecidableEq ι]
    (y : ℕ) (I : Finset ι) (a b : ι → ℕ) (R : ι → ℝ) (L : ℝ) :
    Set (Finset ℕ) :=
  {S | 2 * L < ((S ∩ primesUpTo y).card : ℝ) ∨
    (∀ i ∈ I,
      bernoulliCenteredSum ((primesUpTo (b i)).filter (a i < ·))
          (fun p ↦ (1 / p : ℝ)) S <
        Real.sqrt (∑ p ∈ (primesUpTo (b i)).filter (a i < ·),
          (1 / p : ℝ) * (1 - 1 / p)) / 8) ∨
    ∃ i ∈ I,
      bernoulliCenteredSum (primesUpTo (a i)) (fun p ↦ (1 / p : ℝ)) S ≤ -R i}

open Classical in
/-- Fixed-block probability bound for `kubiliusBlockBadEvent`.  The three terms are respectively
the missed-increment probability, the terminal-cardinality Chebyshev bound, and the sum of the
block-start Chebyshev bounds. -/
theorem kubiliusMass_blockBadEvent_le {ι : Type*} [DecidableEq ι]
    (y : ℕ) (I : Finset ι) (a b : ι → ℕ) (R : ι → ℝ) (L D : ℝ)
    (hab : ∀ i ∈ I, a i ≤ b i) (hby : ∀ i ∈ I, b i ≤ y)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint ((primesUpTo (b i)).filter (a i < ·))
        ((primesUpTo (b j)).filter (a j < ·)))
    (hV : ∀ i ∈ I, 1 ≤ ∑ p ∈ (primesUpTo (b i)).filter (a i < ·),
      (1 / p : ℝ) * (1 - 1 / p))
    (hD : 0 < D) (hR : ∀ i ∈ I, 0 < R i)
    (hmean : (∑ p ∈ primesUpTo y, (1 / p : ℝ)) + D ≤ 2 * L) :
    kubiliusMass y (kubiliusBlockBadEvent y I a b R L) ≤
      ((63 : ℝ) / 64) ^ I.card +
        (∑ p ∈ primesUpTo y, (1 / p : ℝ) * (1 - 1 / p)) / D ^ 2 +
        ∑ i ∈ I, (∑ p ∈ primesUpTo (a i),
          (1 / p : ℝ) * (1 - 1 / p)) / (R i) ^ 2 := by
  let B : ι → Finset ℕ := fun i ↦ (primesUpTo (b i)).filter (a i < ·)
  let Ecard : Set (Finset ℕ) :=
    {S | 2 * L < ((S ∩ primesUpTo y).card : ℝ)}
  let Eblocks : Set (Finset ℕ) :=
    {S | ∀ i ∈ I, bernoulliCenteredSum (B i) (fun p ↦ (1 / p : ℝ)) S <
      Real.sqrt (∑ p ∈ B i, (1 / p : ℝ) * (1 - 1 / p)) / 8}
  let Estarts : Set (Finset ℕ) :=
    {S | ∃ i ∈ I,
      bernoulliCenteredSum (primesUpTo (a i)) (fun p ↦ (1 / p : ℝ)) S ≤ -R i}
  have hBU : ∀ i ∈ I, B i ⊆ primesUpTo y := by
    intro i hi p hp
    have hpbi : p ∈ primesUpTo (b i) := (Finset.mem_filter.mp hp).1
    simp only [primesUpTo_eq_filter_Iic, Finset.mem_filter, Finset.mem_Iic] at hpbi ⊢
    exact ⟨hpbi.1.trans (hby i hi), hpbi.2⟩
  have hblocks : kubiliusMass y Eblocks ≤ ((63 : ℝ) / 64) ^ I.card := by
    exact kubiliusMass_all_blockCenteredSum_lt_sqrt_eighth_le
      y I B hBU (fun i hi j hj hij ↦ hdisj i hi j hj hij) (fun i hi ↦ hV i hi)
  have hcardEvent : Ecard ⊆
      {S | D ≤ |(((S ∩ primesUpTo y).card : ℝ) -
        ∑ p ∈ primesUpTo y, (1 / p : ℝ))|} := by
    intro S hS
    change 2 * L < ((S ∩ primesUpTo y).card : ℝ) at hS
    have hdiff : D ≤ ((S ∩ primesUpTo y).card : ℝ) -
        ∑ p ∈ primesUpTo y, (1 / p : ℝ) := by
      linarith
    exact hdiff.trans (le_abs_self _)
  have hcardMass : kubiliusMass y Ecard ≤
      (∑ p ∈ primesUpTo y, (1 / p : ℝ) * (1 - 1 / p)) / D ^ 2 := by
    exact (kubiliusMass_mono y hcardEvent).trans
      (kubiliusMass_card_deviation_ge_le y hD)
  have hstartOne : ∀ i ∈ I,
      kubiliusMass y
          {S | bernoulliCenteredSum (primesUpTo (a i))
            (fun p ↦ (1 / p : ℝ)) S ≤ -R i} ≤
        (∑ p ∈ primesUpTo (a i), (1 / p : ℝ) * (1 - 1 / p)) / (R i) ^ 2 := by
    intro i hi
    have haiy : a i ≤ y := (hab i hi).trans (hby i hi)
    have hprefix : primesUpTo (a i) ⊆ primesUpTo y := by
      intro p hp
      simp only [primesUpTo_eq_filter_Iic, Finset.mem_filter, Finset.mem_Iic] at hp ⊢
      exact ⟨hp.1.trans haiy, hp.2⟩
    have hsub :
        {S | bernoulliCenteredSum (primesUpTo (a i))
            (fun p ↦ (1 / p : ℝ)) S ≤ -R i} ⊆
          {S | R i ≤ |bernoulliCenteredSum (primesUpTo (a i))
            (fun p ↦ (1 / p : ℝ)) S|} := by
      intro S hS
      change bernoulliCenteredSum (primesUpTo (a i))
        (fun p ↦ (1 / p : ℝ)) S ≤ -R i at hS
      change R i ≤ |bernoulliCenteredSum (primesUpTo (a i))
        (fun p ↦ (1 / p : ℝ)) S|
      have hxnonpos : bernoulliCenteredSum (primesUpTo (a i))
          (fun p ↦ (1 / p : ℝ)) S ≤ 0 := by
        linarith [hR i hi]
      rw [abs_of_nonpos hxnonpos]
      linarith
    exact (kubiliusMass_mono y hsub).trans
      (kubiliusMass_blockCenteredSum_abs_ge_le y (primesUpTo (a i))
        hprefix (hR i hi))
  have hstarts : kubiliusMass y Estarts ≤
      ∑ i ∈ I, (∑ p ∈ primesUpTo (a i),
        (1 / p : ℝ) * (1 - 1 / p)) / (R i) ^ 2 := by
    exact (kubiliusMass_exists_mem_le_sum y I (fun i ↦
      {S | bernoulliCenteredSum (primesUpTo (a i))
        (fun p ↦ (1 / p : ℝ)) S ≤ -R i})).trans
      (Finset.sum_le_sum fun i hi ↦ hstartOne i hi)
  have hevent : kubiliusBlockBadEvent y I a b R L = Eblocks ∪ (Ecard ∪ Estarts) := by
    ext S
    simp only [kubiliusBlockBadEvent, Set.mem_ofPred_eq, Set.mem_union]
    change (2 * L < ((S ∩ primesUpTo y).card : ℝ) ∨
      (∀ i ∈ I, bernoulliCenteredSum (B i) (fun p ↦ (1 / p : ℝ)) S <
        Real.sqrt (∑ p ∈ B i, (1 / p : ℝ) * (1 - 1 / p)) / 8) ∨
      (∃ i ∈ I, bernoulliCenteredSum (primesUpTo (a i))
        (fun p ↦ (1 / p : ℝ)) S ≤ -R i)) ↔ _
    simp only [Eblocks, Ecard, Estarts, Set.mem_ofPred_eq]
    tauto
  rw [hevent]
  calc
    kubiliusMass y (Eblocks ∪ (Ecard ∪ Estarts)) ≤
        kubiliusMass y Eblocks + kubiliusMass y (Ecard ∪ Estarts) :=
      kubiliusMass_union_le y _ _
    _ ≤ kubiliusMass y Eblocks + (kubiliusMass y Ecard + kubiliusMass y Estarts) := by
      gcongr
      exact kubiliusMass_union_le y _ _
    _ ≤ ((63 : ℝ) / 64) ^ I.card +
        (∑ p ∈ primesUpTo y, (1 / p : ℝ) * (1 - 1 / p)) / D ^ 2 +
        ∑ i ∈ I, (∑ p ∈ primesUpTo (a i),
          (1 / p : ℝ) * (1 - 1 / p)) / (R i) ^ 2 := by
      linarith

open Classical in
/-- A single good Kubilius block forces the divisor-variance mass above `T`.  The starting
prime-prefix fluctuation is centered at its reciprocal-prime mean; consequently Mertens is spent
only once, at the block endpoint. -/
theorem divisorVarianceMass_gt_of_kubilius_block_crossing
    (v : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hv0 : ∀ m, 0 ≤ v m)
    (hv : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-Real.log 2) ≤ v m)
    {P n y a b : ℕ} {T L C R : ℝ} (hn : n ≠ 0) (hPa : P ≤ a)
    (hab : a ≤ b) (hby : b ≤ y) (hL : 0 < L)
    (hcard : ((n.primeFactors.filter (· ≤ y)).card : ℝ) ≤ 2 * L)
    (hstart : -R <
      bernoulliCenteredSum (primesUpTo a) (fun p ↦ (1 / p : ℝ))
        (n.primeFactors.filter (· ≤ y)))
    (hcross :
      Real.sqrt (∑ p ∈ (primesUpTo b).filter (a < ·),
          (1 / p : ℝ) * (1 - 1 / p)) / 8 ≤
        bernoulliCenteredSum ((primesUpTo b).filter (a < ·))
          (fun p ↦ (1 / p : ℝ)) (n.primeFactors.filter (· ≤ y)))
    (hvariance : 1 ≤ ∑ p ∈ (primesUpTo b).filter (a < ·),
      (1 / p : ℝ) * (1 - 1 / p))
    (hMertens :
      |∑ p ∈ primesUpTo b, (1 / p : ℝ) - Real.log (Real.log b)| ≤ C)
    (hdom :
      1 + Real.log (2 * L) + Real.log (T / c) / Real.log 2 ≤
        Real.sqrt (∑ p ∈ (primesUpTo b).filter (a < ·),
          (1 / p : ℝ) * (1 - 1 / p)) / 8 - R - C) :
    T < divisorVarianceMass v P n := by
  let S : Finset ℕ := n.primeFactors.filter (· ≤ y)
  let B : Finset ℕ := (primesUpTo b).filter (a < ·)
  let V : ℝ := ∑ p ∈ B, (1 / p : ℝ) * (1 - 1 / p)
  change (S.card : ℝ) ≤ 2 * L at hcard
  change -R < bernoulliCenteredSum (primesUpTo a) (fun p ↦ (1 / p : ℝ)) S at hstart
  change Real.sqrt V / 8 ≤
    bernoulliCenteredSum B (fun p ↦ (1 / p : ℝ)) S at hcross
  change 1 ≤ V at hvariance
  change 1 + Real.log (2 * L) + Real.log (T / c) / Real.log 2 ≤
    Real.sqrt V / 8 - R - C at hdom
  have hsqrt_pos : 0 < Real.sqrt V / 8 := by
    exact div_pos (Real.sqrt_pos.2 (zero_lt_one.trans_le hvariance)) (by norm_num)
  have hay : a ≤ y := hab.trans hby
  have hprefa := bernoulliCenteredSum_primesUpTo_primeFactors (n := n) hay
  have hprefb := bernoulliCenteredSum_primesUpTo_primeFactors (n := n) hby
  change bernoulliCenteredSum (primesUpTo a) (fun p ↦ (1 / p : ℝ)) S =
    (omegaUpTo (a : ℝ) n : ℝ) - ∑ p ∈ primesUpTo a, (1 / p : ℝ) at hprefa
  change bernoulliCenteredSum (primesUpTo b) (fun p ↦ (1 / p : ℝ)) S =
    (omegaUpTo (b : ℝ) n : ℝ) - ∑ p ∈ primesUpTo b, (1 / p : ℝ) at hprefb
  have hsplit := bernoulliCenteredSum_primesUpTo_eq_add_block S hab
  change bernoulliCenteredSum (primesUpTo b) (fun p ↦ (1 / p : ℝ)) S =
    bernoulliCenteredSum (primesUpTo a) (fun p ↦ (1 / p : ℝ)) S +
      bernoulliCenteredSum B (fun p ↦ (1 / p : ℝ)) S at hsplit
  have homega_card : omegaUpTo (b : ℝ) n ≤ S.card := by
    rw [← card_primeFactorsUpTo_eq_omegaUpTo]
    have hinter := primeFactors_filter_inter_primesUpTo (n := n) hby
    change S ∩ primesUpTo b = primeFactorsUpTo b n at hinter
    rw [← hinter]
    exact Finset.card_le_card Finset.inter_subset_left
  have homega : (omegaUpTo (b : ℝ) n : ℝ) ≤ 2 * L := by
    exact (by exact_mod_cast homega_card :
      (omegaUpTo (b : ℝ) n : ℝ) ≤ (S.card : ℝ)).trans hcard
  by_contra hnot
  have hmass : divisorVarianceMass v P n ≤ T := le_of_not_gt hnot
  have hbridge := omegaUpTo_cutoff_eq_early_or_sub_log_log_le
    (P := P) (n := n) (x := (a : ℝ)) (y := (b : ℝ)) (T := T) (L := L)
    v c hc hv0 hv hn (by exact_mod_cast hPa) (by exact_mod_cast hab) hmass hL homega
  rcases hbridge with hearly | hcap
  · have hmeanblock := primeReciprocalSum_block_eq_sub a b hab
    change (∑ p ∈ B, (1 / p : ℝ)) =
      (∑ p ∈ primesUpTo b, (1 / p : ℝ)) -
        ∑ p ∈ primesUpTo a, (1 / p : ℝ) at hmeanblock
    have hmeanblock_nonneg : 0 ≤ ∑ p ∈ B, (1 / p : ℝ) := by
      apply Finset.sum_nonneg
      intro p hp
      positivity
    have hearlyR : (omegaUpTo (b : ℝ) n : ℝ) = omegaUpTo (a : ℝ) n := by
      exact_mod_cast hearly
    have hblock_nonpos :
        bernoulliCenteredSum B (fun p ↦ (1 / p : ℝ)) S ≤ 0 := by
      linarith
    linarith
  · have hMertensLower := (abs_le.mp hMertens).1
    have hwalk :
        1 + Real.log (2 * L) + Real.log (T / c) / Real.log 2 <
          (omegaUpTo (b : ℝ) n : ℝ) - Real.log (Real.log b) := by
      linarith
    exact (not_lt_of_ge hcap) hwalk

open Classical in
/-- If the divisor-variance mass is at most `T`, then the prime-factor coordinate set must lie in
the fixed-block exceptional event.  Thus `kubiliusMass_blockBadEvent_le` can be transferred to
integer density by `KubiliusTV` once a concrete block schedule has been chosen. -/
theorem primeFactorSet_mem_kubiliusBlockBadEvent_of_divisorVarianceMass_le
    {ι : Type*} [DecidableEq ι]
    (v : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hv0 : ∀ m, 0 ≤ v m)
    (hv : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-Real.log 2) ≤ v m)
    {P n y : ℕ} {T L C : ℝ} (I : Finset ι) (a b : ι → ℕ) (R : ι → ℝ)
    (hn : n ≠ 0) (hPa : ∀ i ∈ I, P ≤ a i)
    (hab : ∀ i ∈ I, a i ≤ b i) (hby : ∀ i ∈ I, b i ≤ y) (hL : 0 < L)
    (hV : ∀ i ∈ I, 1 ≤ ∑ p ∈ (primesUpTo (b i)).filter (a i < ·),
      (1 / p : ℝ) * (1 - 1 / p))
    (hMertens : ∀ i ∈ I,
      |∑ p ∈ primesUpTo (b i), (1 / p : ℝ) - Real.log (Real.log (b i))| ≤ C)
    (hdom : ∀ i ∈ I,
      1 + Real.log (2 * L) + Real.log (T / c) / Real.log 2 ≤
        Real.sqrt (∑ p ∈ (primesUpTo (b i)).filter (a i < ·),
          (1 / p : ℝ) * (1 - 1 / p)) / 8 - R i - C)
    (hmass : divisorVarianceMass v P n ≤ T) :
    n.primeFactors.filter (· ≤ y) ∈ kubiliusBlockBadEvent y I a b R L := by
  let S : Finset ℕ := n.primeFactors.filter (· ≤ y)
  change S ∈ kubiliusBlockBadEvent y I a b R L
  by_contra hgood
  change ¬ (2 * L < ((S ∩ primesUpTo y).card : ℝ) ∨
    (∀ i ∈ I,
      bernoulliCenteredSum ((primesUpTo (b i)).filter (a i < ·))
          (fun p ↦ (1 / p : ℝ)) S <
        Real.sqrt (∑ p ∈ (primesUpTo (b i)).filter (a i < ·),
          (1 / p : ℝ) * (1 - 1 / p)) / 8) ∨
    ∃ i ∈ I,
      bernoulliCenteredSum (primesUpTo (a i)) (fun p ↦ (1 / p : ℝ)) S ≤ -R i) at hgood
  have hcardNot : ¬ 2 * L < ((S ∩ primesUpTo y).card : ℝ) := by
    intro h
    exact hgood (Or.inl h)
  have hblocksNot : ¬ (∀ i ∈ I,
      bernoulliCenteredSum ((primesUpTo (b i)).filter (a i < ·))
          (fun p ↦ (1 / p : ℝ)) S <
        Real.sqrt (∑ p ∈ (primesUpTo (b i)).filter (a i < ·),
          (1 / p : ℝ) * (1 - 1 / p)) / 8) := by
    intro h
    exact hgood (Or.inr (Or.inl h))
  have hstartsNot : ¬ (∃ i ∈ I,
      bernoulliCenteredSum (primesUpTo (a i)) (fun p ↦ (1 / p : ℝ)) S ≤ -R i) := by
    intro h
    exact hgood (Or.inr (Or.inr h))
  have hinter : S ∩ primesUpTo y = S := by
    have h := primeFactors_filter_inter_primesUpTo (n := n) (a := y) (y := y) le_rfl
    simpa only [S, primeFactorsUpTo] using h
  have hcard : (S.card : ℝ) ≤ 2 * L := by
    rw [← hinter]
    exact le_of_not_gt hcardNot
  push Not at hblocksNot
  obtain ⟨i, hi, hcrossNot⟩ := hblocksNot
  have hcross :
      Real.sqrt (∑ p ∈ (primesUpTo (b i)).filter (a i < ·),
          (1 / p : ℝ) * (1 - 1 / p)) / 8 ≤
        bernoulliCenteredSum ((primesUpTo (b i)).filter (a i < ·))
          (fun p ↦ (1 / p : ℝ)) S := hcrossNot
  have hstart : -R i <
      bernoulliCenteredSum (primesUpTo (a i)) (fun p ↦ (1 / p : ℝ)) S := by
    apply lt_of_not_ge
    intro h
    exact hstartsNot ⟨i, hi, h⟩
  have hforced := divisorVarianceMass_gt_of_kubilius_block_crossing
    v c hc hv0 hv hn (hPa i hi) (hab i hi) (hby i hi) hL hcard hstart hcross
      (hV i hi) (hMertens i hi) (hdom i hi)
  exact (not_lt_of_ge hmass) hforced

/-- Once `x ≥ 1`, its natural floor loses at most a factor of two.  This elementary floor
estimate is the convenient way to control both logarithms of the natural Kubilius cutoffs. -/
theorem half_le_natFloor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hlt := Nat.lt_floor_add_one x
  have hfloorOne : (1 : ℝ) ≤ ⌊x⌋₊ := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
      rw [Ne, Nat.floor_eq_zero]
      linarith)
  linarith

/-- The natural cutoff `⌊exp((log M)^s)⌋` has double logarithm within `log 2` of
`s * log log M`.  The explicit growth hypothesis is intentionally separated from the eventual
schedule proof: every fixed positive `s` satisfies it for all sufficiently large `M`. -/
theorem log_log_natFloor_exp_log_rpow_bounds {M : ℕ} {s : ℝ}
    (hM : 3 ≤ M) (hs : 0 < s)
    (hgrowth : 2 * Real.log 2 ≤ Real.rpow (Real.log M) s) :
    let z := ⌊Real.exp (Real.rpow (Real.log M) s)⌋₊
    2 ≤ z ∧
      s * Real.log (Real.log M) - Real.log 2 ≤ Real.log (Real.log z) ∧
      Real.log (Real.log z) ≤ s * Real.log (Real.log M) := by
  let x : ℝ := Real.log M ^ s
  let z : ℕ := ⌊Real.exp x⌋₊
  have hlogMpos : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hxpos : 0 < x := by
    exact Real.rpow_pos_of_pos hlogMpos s
  change 2 * Real.log 2 ≤ x at hgrowth
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexpOne : 1 ≤ Real.exp x := Real.one_le_exp hxpos.le
  have hhalf : Real.exp x / 2 ≤ (z : ℝ) := half_le_natFloor hexpOne
  have hzTwoReal : (2 : ℝ) ≤ z := by
    calc
      (2 : ℝ) ≤ Real.exp x / 2 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        calc
          (2 : ℝ) * 2 = Real.exp (2 * Real.log 2) := by
            calc
              (2 : ℝ) * 2 = 4 := by norm_num
              _ = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
              _ = Real.exp (2 * Real.log 2) := by
                congr 1
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
                norm_num
          _ ≤ Real.exp x := Real.exp_le_exp.mpr hgrowth
      _ ≤ z := hhalf
  have hzTwo : 2 ≤ z := by exact_mod_cast hzTwoReal
  have hzpos : (0 : ℝ) < z := by positivity
  have hlogzLower : x / 2 ≤ Real.log z := by
    calc
      x / 2 ≤ x - Real.log 2 := by linarith
      _ = Real.log (Real.exp x / 2) := by
        rw [Real.log_div (Real.exp_ne_zero x) (by norm_num), Real.log_exp]
      _ ≤ Real.log z := Real.log_le_log (by positivity) hhalf
  have hfloorUpper : (z : ℝ) ≤ Real.exp x := Nat.floor_le (Real.exp_pos x).le
  have hlogzUpper : Real.log z ≤ x := by
    simpa only [Real.log_exp] using Real.log_le_log hzpos hfloorUpper
  have hxhalfpos : 0 < x / 2 := by positivity
  have hlogzpos : 0 < Real.log z := hxhalfpos.trans_le hlogzLower
  have hlogx : Real.log x = s * Real.log (Real.log M) := by
    simpa only [x] using Real.log_rpow hlogMpos s
  refine ⟨hzTwo, ?_, ?_⟩
  · calc
      s * Real.log (Real.log M) - Real.log 2 = Real.log (x / 2) := by
        rw [Real.log_div hxpos.ne' (by norm_num), hlogx]
      _ ≤ Real.log (Real.log z) := Real.log_le_log hxhalfpos hlogzLower
  · calc
      Real.log (Real.log z) ≤ Real.log x := Real.log_le_log hlogzpos hlogzUpper
      _ = s * Real.log (Real.log M) := hlogx

/-- Natural FDEK-style cutoffs inherit monotonicity in their exponent. -/
theorem natFloor_exp_log_rpow_mono {M : ℕ} {s t : ℝ}
    (hM : 3 ≤ M) (hst : s ≤ t) :
    ⌊Real.exp (Real.rpow (Real.log M) s)⌋₊ ≤
      ⌊Real.exp (Real.rpow (Real.log M) t)⌋₊ := by
  exact Nat.floor_le_floor (exp_log_rpow_mono hM hst)

/-- Every fixed positive natural cutoff exponent eventually has the sharp double-log bounds above,
also after a fixed additive shift of the sample endpoint. -/
theorem eventually_log_log_natFloor_exp_log_rpow_bounds (a : ℕ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ N : ℕ in atTop,
      let M := N + a
      let z := ⌊Real.exp (Real.rpow (Real.log M) s)⌋₊
      2 ≤ z ∧
        s * Real.log (Real.log M) - Real.log 2 ≤ Real.log (Real.log z) ∧
        Real.log (Real.log z) ≤ s * Real.log (Real.log M) := by
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log ((N + a : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat a))
  have hpowTop : Tendsto
      (fun N : ℕ ↦ Real.rpow (Real.log ((N + a : ℕ) : ℝ)) s) atTop atTop :=
    (tendsto_rpow_atTop hs).comp hlogTop
  filter_upwards [eventually_ge_atTop 3,
      hpowTop.eventually_ge_atTop (2 * Real.log 2)] with N hN hgrowth
  exact log_log_natFloor_exp_log_rpow_bounds (show 3 ≤ N + a by omega) hs hgrowth

/-- The deterministic collision cutoff is eventually below the natural version of every fixed
positive Kubilius cutoff. -/
theorem eventually_collisionCutoff_le_natFloor_exp_log_rpow_add (a : ℕ)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ N : ℕ in atTop,
      collisionCutoff N ≤ ⌊Real.exp (Real.rpow (Real.log (N + a)) s)⌋₊ := by
  filter_upwards [eventually_collisionCutoff_le_exp_log_rpow_add a hs] with N hN
  exact Nat.le_floor hN

/-- Exponents for `K` consecutive geometric blocks.  The final block ends at exponent `1/4`,
leaving ample room below the Kubilius cutoff at exponent `1/2`. -/
noncomputable def kubiliusGeometricExponent (K i : ℕ) (r : ℝ) : ℝ :=
  r ^ i / (4 * r ^ K)

theorem kubiliusGeometricExponent_pos {K i : ℕ} {r : ℝ} (hr : 0 < r) :
    0 < kubiliusGeometricExponent K i r := by
  exact div_pos (pow_pos hr _) (mul_pos (by norm_num) (pow_pos hr _))

theorem kubiliusGeometricExponent_mono {K i j : ℕ} {r : ℝ}
    (hr : 1 ≤ r) (hij : i ≤ j) :
    kubiliusGeometricExponent K i r ≤ kubiliusGeometricExponent K j r := by
  unfold kubiliusGeometricExponent
  exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hr hij)
    (mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans hr) _))

theorem kubiliusGeometricExponent_succ {K i : ℕ} {r : ℝ} (hr : r ≠ 0) :
    kubiliusGeometricExponent K (i + 1) r =
      r * kubiliusGeometricExponent K i r := by
  unfold kubiliusGeometricExponent
  rw [pow_succ]
  field_simp

theorem kubiliusGeometricExponent_end {K : ℕ} {r : ℝ} (hr : r ≠ 0) :
    kubiliusGeometricExponent K K r = 1 / 4 := by
  unfold kubiliusGeometricExponent
  field_simp

theorem kubiliusGeometricExponent_le_quarter {K i : ℕ} {r : ℝ}
    (hr : 1 ≤ r) (hi : i ≤ K) :
    kubiliusGeometricExponent K i r ≤ 1 / 4 := by
  calc
    kubiliusGeometricExponent K i r ≤ kubiliusGeometricExponent K K r :=
      kubiliusGeometricExponent_mono hr hi
    _ = 1 / 4 := kubiliusGeometricExponent_end (ne_of_gt (zero_lt_one.trans_le hr))

/-- The natural prime cutoff at one geometric schedule coordinate. -/
noncomputable def kubiliusGeometricCutoff (M K : ℕ) (r : ℝ) (i : ℕ) : ℕ :=
  ⌊Real.exp (Real.rpow (Real.log M) (kubiliusGeometricExponent K i r))⌋₊

theorem kubiliusGeometricCutoff_mono {M K i j : ℕ} {r : ℝ}
    (hM : 3 ≤ M) (hr : 1 ≤ r) (hij : i ≤ j) :
    kubiliusGeometricCutoff M K r i ≤ kubiliusGeometricCutoff M K r j := by
  exact natFloor_exp_log_rpow_mono hM (kubiliusGeometricExponent_mono hr hij)

/-- Prime blocks whose earlier endpoint is below the later start are disjoint. -/
theorem primeBlocks_disjoint_of_end_le_start {a b c d : ℕ} (hbc : b ≤ c) :
    Disjoint ((primesUpTo b).filter (a < ·)) ((primesUpTo d).filter (c < ·)) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  have hpb : p ≤ b := by
    have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    simp only [Finset.mem_range] at this
    omega
  have hcp : c < p := (Finset.mem_filter.mp hq).2
  omega

/-- Distinct blocks in the geometric schedule are pairwise disjoint. -/
theorem kubiliusGeometricBlocks_disjoint {M K : ℕ} {r : ℝ}
    (hM : 3 ≤ M) (hr : 1 ≤ r) {i j : ℕ} (hij : i ≠ j) :
    Disjoint
      ((primesUpTo (kubiliusGeometricCutoff M K r (i + 1))).filter
        (kubiliusGeometricCutoff M K r i < ·))
      ((primesUpTo (kubiliusGeometricCutoff M K r (j + 1))).filter
        (kubiliusGeometricCutoff M K r j < ·)) := by
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact primeBlocks_disjoint_of_end_le_start
      (kubiliusGeometricCutoff_mono hM hr (by omega : i + 1 ≤ j))
  · exact (primeBlocks_disjoint_of_end_le_start
      (kubiliusGeometricCutoff_mono hM hr (by omega : j + 1 ≤ i))).symm

/-- Mertens' theorem gives a linear-in-`log log M` variance lower bound on every geometric
schedule block.  The only discretization loss is the explicit `log 2` from natural flooring. -/
theorem mertens_kubiliusGeometricBlock_variance_lower :
    ∃ C : ℝ, ∀ (M K i : ℕ) (r : ℝ), 3 ≤ M → 1 < r →
      2 * Real.log 2 ≤
        Real.rpow (Real.log M) (kubiliusGeometricExponent K i r) →
      2 * Real.log 2 ≤
        Real.rpow (Real.log M) (kubiliusGeometricExponent K (i + 1) r) →
      (1 / 2 : ℝ) *
          ((r - 1) * kubiliusGeometricExponent K i r * Real.log (Real.log M) -
            Real.log 2 - 2 * C) ≤
        ∑ p ∈ (primesUpTo (kubiliusGeometricCutoff M K r (i + 1))).filter
            (kubiliusGeometricCutoff M K r i < ·),
          (1 / p : ℝ) * (1 - 1 / p) := by
  obtain ⟨C, hC⟩ := mertens_primeVariance_block_lower
  refine ⟨C, fun M K i r hM hr hgrowi hgrowsucc ↦ ?_⟩
  let si := kubiliusGeometricExponent K i r
  let sj := kubiliusGeometricExponent K (i + 1) r
  let a := kubiliusGeometricCutoff M K r i
  let b := kubiliusGeometricCutoff M K r (i + 1)
  have hri : (1 : ℝ) ≤ r := hr.le
  have hsi : 0 < si := kubiliusGeometricExponent_pos (zero_lt_one.trans hr)
  have hsj : 0 < sj := kubiliusGeometricExponent_pos (zero_lt_one.trans hr)
  have hai := log_log_natFloor_exp_log_rpow_bounds hM hsi hgrowi
  have hbj := log_log_natFloor_exp_log_rpow_bounds hM hsj hgrowsucc
  change 2 ≤ a ∧
    si * Real.log (Real.log M) - Real.log 2 ≤ Real.log (Real.log a) ∧
    Real.log (Real.log a) ≤ si * Real.log (Real.log M) at hai
  change 2 ≤ b ∧
    sj * Real.log (Real.log M) - Real.log 2 ≤ Real.log (Real.log b) ∧
    Real.log (Real.log b) ≤ sj * Real.log (Real.log M) at hbj
  have hab : a ≤ b := kubiliusGeometricCutoff_mono hM hri (by omega)
  have hMertens := hC a b hai.1 hab
  have hsucc : sj = r * si := by
    exact kubiliusGeometricExponent_succ (ne_of_gt (zero_lt_one.trans hr))
  change (1 / 2 : ℝ) *
      ((r - 1) * si * Real.log (Real.log M) - Real.log 2 - 2 * C) ≤ _
  change (1 / 2 : ℝ) *
      (Real.log (Real.log b) - Real.log (Real.log a) - 2 * C) ≤ _ at hMertens
  have haiUpper := hai.2.2
  have hbjLower := hbj.2.1
  rw [hsucc] at hbjLower
  nlinarith

/-- The variance of every geometric schedule prefix is at most its exponent times
`log log M`, plus one fixed Mertens constant. -/
theorem mertens_kubiliusGeometricPrefix_variance_upper :
    ∃ C : ℝ, ∀ (M K i : ℕ) (r : ℝ), 3 ≤ M → 0 < r →
      2 * Real.log 2 ≤
        Real.rpow (Real.log M) (kubiliusGeometricExponent K i r) →
      ∑ p ∈ primesUpTo (kubiliusGeometricCutoff M K r i),
          (1 / p : ℝ) * (1 - 1 / p) ≤
        kubiliusGeometricExponent K i r * Real.log (Real.log M) + C := by
  obtain ⟨C, hC⟩ := mertens_primeVariance_prefix_upper
  refine ⟨C, fun M K i r hM hr hgrowth ↦ ?_⟩
  let s := kubiliusGeometricExponent K i r
  let a := kubiliusGeometricCutoff M K r i
  have hs : 0 < s := kubiliusGeometricExponent_pos hr
  have ha := log_log_natFloor_exp_log_rpow_bounds hM hs hgrowth
  change 2 ≤ a ∧
    s * Real.log (Real.log M) - Real.log 2 ≤ Real.log (Real.log a) ∧
    Real.log (Real.log a) ≤ s * Real.log (Real.log M) at ha
  have hprefix := hC a ha.1
  change _ ≤ Real.log (Real.log a) + C at hprefix
  change _ ≤ s * Real.log (Real.log M) + C
  linarith [ha.2.2]

/-- One nonnegative constant simultaneously controls every Mertens estimate used by the
Kubilius schedule.  The three preceding existence theorems may a priori choose different
constants; taking their maximum here keeps the final asymptotic assembly from carrying three
independent bookkeeping parameters. -/
theorem exists_mertens_kubiliusUnified_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ y : ℕ, 2 ≤ y →
        |∑ p ∈ primesUpTo y, (1 / p : ℝ) - Real.log (Real.log y)| ≤ C) ∧
      (∀ (M K i : ℕ) (r : ℝ), 3 ≤ M → 1 < r →
        2 * Real.log 2 ≤
          Real.rpow (Real.log M) (kubiliusGeometricExponent K i r) →
        2 * Real.log 2 ≤
          Real.rpow (Real.log M) (kubiliusGeometricExponent K (i + 1) r) →
        (1 / 2 : ℝ) *
            ((r - 1) * kubiliusGeometricExponent K i r * Real.log (Real.log M) -
              Real.log 2 - 2 * C) ≤
          ∑ p ∈ (primesUpTo (kubiliusGeometricCutoff M K r (i + 1))).filter
              (kubiliusGeometricCutoff M K r i < ·),
            (1 / p : ℝ) * (1 - 1 / p)) ∧
      (∀ (M K i : ℕ) (r : ℝ), 3 ≤ M → 0 < r →
        2 * Real.log 2 ≤
          Real.rpow (Real.log M) (kubiliusGeometricExponent K i r) →
        ∑ p ∈ primesUpTo (kubiliusGeometricCutoff M K r i),
            (1 / p : ℝ) * (1 - 1 / p) ≤
          kubiliusGeometricExponent K i r * Real.log (Real.log M) + C) := by
  obtain ⟨C₀, hC₀⟩ := mertens_primeReciprocalSum_bound
  obtain ⟨C₁, hC₁⟩ := mertens_kubiliusGeometricBlock_variance_lower
  obtain ⟨C₂, hC₂⟩ := mertens_kubiliusGeometricPrefix_variance_upper
  let C : ℝ := max 0 (max C₀ (max C₁ C₂))
  have hC0 : 0 ≤ C := le_max_left _ _
  have hC₀C : C₀ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC₁C : C₁ ≤ C :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hC₂C : C₂ ≤ C :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨C, hC0, ?_, ?_, ?_⟩
  · intro y hy
    exact (hC₀ y hy).trans hC₀C
  · intro M K i r hM hr hgi hgis
    have h := hC₁ M K i r hM hr hgi hgis
    nlinarith
  · intro M K i r hM hr hgi
    exact (hC₂ M K i r hM hr hgi).trans (add_le_add_right hC₂C _)

/-- Scalar heart of the geometric-block choice.  A block variance with the Mertens lower bound
dominates both the negative prefix allowance and the logarithmic walk cap once `r` is chosen on
the `B²` scale.  Keeping this square-root calculation separate makes the eventual schedule proof
purely an exercise in sending `log log M` to infinity. -/
theorem kubiliusBlock_variance_and_domination
    {s L r B C c T V : ℝ} (hs : 0 < s) (hL : 0 < L) (hB : 0 ≤ B)
    (hscale : (32 * B) ^ 2 ≤ r - 1)
    (hloss : Real.log 2 + 2 * C ≤ (r - 1) * s * L / 2)
    (hVlower : (1 / 2 : ℝ) * ((r - 1) * s * L - Real.log 2 - 2 * C) ≤ V)
    (hunit : 1 ≤ (r - 1) * s * L / 4)
    (hcap : 1 + Real.log (2 * L) + Real.log (T / c) / Real.log 2 + C ≤
      B * Real.sqrt (s * L)) :
    1 ≤ V ∧
      1 + Real.log (2 * L) + Real.log (T / c) / Real.log 2 ≤
        Real.sqrt V / 8 - B * Real.sqrt (s * L) - C := by
  have hsL : 0 ≤ s * L := (mul_pos hs hL).le
  have hr : 0 ≤ r - 1 := hscale.trans' (sq_nonneg (32 * B))
  have hquarter : (r - 1) * s * L / 4 ≤ V := by
    nlinarith
  have hV : 0 ≤ V := le_trans (by positivity : (0 : ℝ) ≤ 1) (hunit.trans hquarter)
  have hBsqrt : 0 ≤ 16 * B * Real.sqrt (s * L) := by positivity
  have hsq : (16 * B * Real.sqrt (s * L)) ^ 2 ≤ V := by
    have hsqrtSq := Real.sq_sqrt hsL
    have hcoeff : 256 * B ^ 2 ≤ (r - 1) / 4 := by
      nlinarith [hscale]
    have hmul := mul_le_mul_of_nonneg_right hcoeff hsL
    nlinarith
  have hsqrt : 16 * B * Real.sqrt (s * L) ≤ Real.sqrt V := by
    exact (Real.le_sqrt hBsqrt hV).2 hsq
  constructor
  · exact hunit.trans hquarter
  · have htwo : 2 * B * Real.sqrt (s * L) ≤ Real.sqrt V / 8 := by
      linarith
    linarith

/-- The walk cap remains negligible on the square-root scale after adding any fixed Mertens
constant. -/
theorem eventually_walk_cap_add_const_le_sqrt (c T C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop,
      1 + Real.log (2 * L) + Real.log (T / c) / Real.log 2 + C ≤
        δ * Real.sqrt L := by
  have hcap := eventually_walk_cap_le_sqrt c T (δ / 2) (half_pos hδ)
  have hsqrt := Real.tendsto_sqrt_atTop.eventually_ge_atTop (2 * C / δ)
  filter_upwards [hcap, hsqrt] with L hcapL hsqrtL
  have hmul := mul_le_mul_of_nonneg_left hsqrtL (half_pos hδ).le
  have hC : C ≤ (δ / 2) * Real.sqrt L := by
    calc
      C = (δ / 2) * (2 * C / δ) := by field_simp
      _ ≤ (δ / 2) * Real.sqrt L := hmul
  linarith

/-- With `Rᵢ = B √(sᵢ log log M)`, every block-start Chebyshev term is eventually at most
`2 / B²`, uniformly over the fixed finite geometric schedule. -/
theorem eventually_kubiliusGeometric_startError_le
    (a₀ K : ℕ) (C B r : ℝ) (hB : 0 < B) (hr : 1 ≤ r)
    (hprefix : ∀ (M K i : ℕ) (r : ℝ), 3 ≤ M → 0 < r →
      2 * Real.log 2 ≤
        Real.rpow (Real.log M) (kubiliusGeometricExponent K i r) →
      ∑ p ∈ primesUpTo (kubiliusGeometricCutoff M K r i),
          (1 / p : ℝ) * (1 - 1 / p) ≤
        kubiliusGeometricExponent K i r * Real.log (Real.log M) + C) :
    ∀ᶠ N : ℕ in atTop,
      let M := N + a₀
      let L := Real.log (Real.log M)
      ∀ i ∈ Finset.range K,
        (∑ p ∈ primesUpTo (kubiliusGeometricCutoff M K r i),
            (1 / p : ℝ) * (1 - 1 / p)) /
              (B * Real.sqrt (kubiliusGeometricExponent K i r * L)) ^ 2 ≤
          2 / B ^ 2 := by
  let s₀ := kubiliusGeometricExponent K 0 r
  have hrs : 0 < r := zero_lt_one.trans_le hr
  have hs₀ : 0 < s₀ := kubiliusGeometricExponent_pos hrs
  have hLtop : Tendsto (fun N : ℕ ↦ Real.log (Real.log ((N + a₀ : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat a₀)))
  have hCsmall := hLtop.eventually_ge_atTop (C / s₀)
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log ((N + a₀ : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat a₀))
  have hgrow₀ := ((tendsto_rpow_atTop hs₀).comp hlogTop).eventually_ge_atTop
    (2 * Real.log 2)
  filter_upwards [eventually_ge_atTop 3, hCsmall, hgrow₀] with N hN hCL hgrow
  dsimp only
  let M := N + a₀
  let L := Real.log (Real.log M)
  have hM : 3 ≤ M := by simp only [M]; omega
  have hlogM1 : (1 : ℝ) ≤ Real.log M := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
      _ ≤ Real.log M := Real.log_le_log (by norm_num) (by exact_mod_cast hM)
  have hL0 : 0 ≤ L := Real.log_nonneg hlogM1
  have hCs₀L : C ≤ s₀ * L := by
    have := mul_le_mul_of_nonneg_left hCL hs₀.le
    rwa [mul_div_cancel₀ C hs₀.ne'] at this
  intro i hi
  have hsi : s₀ ≤ kubiliusGeometricExponent K i r :=
    kubiliusGeometricExponent_mono hr (Nat.zero_le i)
  have hgrowi : 2 * Real.log 2 ≤
      Real.rpow (Real.log M) (kubiliusGeometricExponent K i r) := by
    exact hgrow.trans (Real.rpow_le_rpow_of_exponent_le hlogM1 hsi)
  have hnum := hprefix M K i r hM hrs hgrowi
  let s := kubiliusGeometricExponent K i r
  have hs : 0 < s := kubiliusGeometricExponent_pos hrs
  have hsiL : s₀ * L ≤ s * L := mul_le_mul_of_nonneg_right hsi hL0
  have hCsiL : C ≤ s * L := hCs₀L.trans hsiL
  have hrootSq : (Real.sqrt (s * L)) ^ 2 = s * L :=
    Real.sq_sqrt (mul_nonneg hs.le hL0)
  have hden : 0 < (B * Real.sqrt (s * L)) ^ 2 := by
    have hL : 0 < L := by
      have hlogMgt : (1 : ℝ) < Real.log M := by
        calc
          (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ < Real.log 3 := Real.strictMonoOn_log (Real.exp_pos 1) (by norm_num)
            Real.exp_one_lt_three
          _ ≤ Real.log M := Real.log_le_log (by norm_num) (by exact_mod_cast hM)
      exact Real.log_pos hlogMgt
    positivity
  change _ / (B * Real.sqrt (s * L)) ^ 2 ≤ 2 / B ^ 2
  apply (div_le_iff₀ hden).2
  rw [mul_pow, hrootSq]
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  calc
    (∑ p ∈ primesUpTo (kubiliusGeometricCutoff M K r i),
        (1 / p : ℝ) * (1 - 1 / p)) ≤ 2 * (s * L) := by nlinarith
    _ = 2 / B ^ 2 * (B ^ 2 * (s * L)) := by field_simp

/-- At the Kubilius cutoff `y = floor(exp(sqrt(log M)))`, both the terminal-cardinality
Chebyshev term and the mean condition in `kubiliusMass_blockBadEvent_le` have uniform elementary
bounds. -/
theorem eventually_kubiliusHalfCutoff_bounds
    (a₀ : ℕ) (C : ℝ)
    (hMertens : ∀ y : ℕ, 2 ≤ y →
      |∑ p ∈ primesUpTo y, (1 / p : ℝ) - Real.log (Real.log y)| ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      let M := N + a₀
      let L := Real.log (Real.log M)
      let y := ⌊Real.exp (Real.rpow (Real.log M) (1 / 2 : ℝ))⌋₊
      let D := L / 2
      2 ≤ y ∧ y ≤ M ∧ 0 < D ∧
        (∑ p ∈ primesUpTo y, (1 / p : ℝ)) + D ≤ 2 * L ∧
        (∑ p ∈ primesUpTo y, (1 / p : ℝ) * (1 - 1 / p)) / D ^ 2 ≤ 4 / L := by
  have hdouble := eventually_log_log_natFloor_exp_log_rpow_bounds a₀
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hLtop : Tendsto (fun N : ℕ ↦ Real.log (Real.log ((N + a₀ : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat a₀)))
  have hCsmall := hLtop.eventually_ge_atTop (2 * C)
  filter_upwards [hdouble, hCsmall, eventually_ge_atTop 3] with N hybounds hLC hN
  dsimp only
  let M := N + a₀
  let L := Real.log (Real.log M)
  let y := ⌊Real.exp (Real.rpow (Real.log M) (1 / 2 : ℝ))⌋₊
  let D := L / 2
  change 2 ≤ y ∧ (1 / 2 : ℝ) * L - Real.log 2 ≤ Real.log (Real.log y) ∧
    Real.log (Real.log y) ≤ (1 / 2 : ℝ) * L at hybounds
  have hM : 3 ≤ M := by simp only [M]; omega
  have hlogM1 : (1 : ℝ) < Real.log M := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.strictMonoOn_log (Real.exp_pos 1) (by norm_num)
        Real.exp_one_lt_three
      _ ≤ Real.log M := Real.log_le_log (by norm_num) (by exact_mod_cast hM)
  have hL : 0 < L := Real.log_pos hlogM1
  have hD : 0 < D := by simp only [D]; positivity
  have hyM : y ≤ M := by
    have hfloor : (y : ℝ) ≤ Real.exp (Real.rpow (Real.log M) (1 / 2 : ℝ)) :=
      Nat.floor_le (Real.exp_pos _).le
    have hpow : Real.rpow (Real.log M) (1 / 2 : ℝ) ≤ Real.log M := by
      calc
        Real.rpow (Real.log M) (1 / 2 : ℝ) ≤ Real.rpow (Real.log M) 1 :=
          Real.rpow_le_rpow_of_exponent_le hlogM1.le
            (show (1 / 2 : ℝ) ≤ 1 by norm_num)
        _ = Real.log M := Real.rpow_one _
    have hexp : Real.exp (Real.rpow (Real.log M) (1 / 2 : ℝ)) ≤ (M : ℝ) := by
      calc
        Real.exp (Real.rpow (Real.log M) (1 / 2 : ℝ)) ≤ Real.exp (Real.log M) :=
          Real.exp_le_exp.mpr hpow
        _ = M := Real.exp_log (by positivity)
    exact_mod_cast hfloor.trans hexp
  have hmean := hMertens y hybounds.1
  have hmeanUpper : (∑ p ∈ primesUpTo y, (1 / p : ℝ)) ≤ L / 2 + C := by
    have := (abs_le.mp hmean).2
    nlinarith [hybounds.2.2]
  have hCL : C ≤ L / 2 := by
    change 2 * C ≤ L at hLC
    linarith
  have hvariance :
      (∑ p ∈ primesUpTo y, (1 / p : ℝ) * (1 - 1 / p)) ≤
        ∑ p ∈ primesUpTo y, (1 / p : ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_le
    have hq : (0 : ℝ) ≤ 1 / p := by positivity
    nlinarith
  refine ⟨hybounds.1, hyM, hD, ?_, ?_⟩
  · linarith
  · have hnum :
        (∑ p ∈ primesUpTo y, (1 / p : ℝ) * (1 - 1 / p)) ≤ L := by
      exact hvariance.trans (by linarith)
    change _ / (L / 2) ^ 2 ≤ 4 / L
    apply (div_le_iff₀ (sq_pos_of_pos (half_pos hL))).2
    have hLne : L ≠ 0 := hL.ne'
    calc
      (∑ p ∈ primesUpTo y, (1 / p : ℝ) * (1 - 1 / p)) ≤ L := hnum
      _ = 4 / L * (L / 2) ^ 2 := by field_simp <;> norm_num

/-- The explicit error in `KubiliusTV` vanishes at the half-power cutoff.  The proof only uses
`u ≥ sqrt(log M)`: for `u ≥ 2`, the superexponential term `u⁻ᵘ` is already bounded by `1/u`. -/
theorem tendsto_kubiliusHalfCutoff_error (a₀ : ℕ) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun N : ℕ ↦
      let M := N + a₀
      let y := ⌊Real.exp (Real.rpow (Real.log M) (1 / 2 : ℝ))⌋₊
      let u := Real.log M / Real.log y
      C * (Real.rpow u (-u) + Real.rpow M (-(1 / 2 : ℝ))))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let A : ℝ := 4 * C / ε + 2
  have hA : 2 < A := by
    dsimp only [A]
    have : 0 < 4 * C / ε := div_pos (mul_pos (by norm_num) hC) hε
    linarith
  have hMtop : Tendsto (fun N : ℕ ↦ ((N + a₀ : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat a₀)
  have hsqrtM := (Real.tendsto_sqrt_atTop.comp hMtop).eventually_ge_atTop A
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log ((N + a₀ : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hMtop
  have hsqrtLog := (Real.tendsto_sqrt_atTop.comp hlogTop).eventually_ge_atTop A
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (hsqrtM.and (hsqrtLog.and (eventually_ge_atTop 3)))
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨hsqrtM_N, hsqrtLog_N, hN3⟩ := hN₀ N hN
  let M : ℕ := N + a₀
  let y : ℕ := ⌊Real.exp (Real.rpow (Real.log M) (1 / 2 : ℝ))⌋₊
  let u : ℝ := Real.log M / Real.log y
  change A ≤ Real.sqrt (M : ℝ) at hsqrtM_N
  change A ≤ Real.sqrt (Real.log (M : ℝ)) at hsqrtLog_N
  have hM3 : 3 ≤ M := by simp only [M]; omega
  have hlogM1 : (1 : ℝ) < Real.log M := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.strictMonoOn_log (Real.exp_pos 1) (by norm_num)
        Real.exp_one_lt_three
      _ ≤ Real.log M := Real.log_le_log (by norm_num) (by exact_mod_cast hM3)
  have hsqrtLog_pos : 0 < Real.sqrt (Real.log M) := Real.sqrt_pos.2 (by positivity)
  have hexpOne : 1 ≤ Real.exp (Real.rpow (Real.log M) (1 / 2 : ℝ)) :=
    Real.one_le_exp (Real.rpow_nonneg (by positivity) _)
  have hyhalf : Real.exp (Real.rpow (Real.log M) (1 / 2 : ℝ)) / 2 ≤ (y : ℝ) :=
    half_le_natFloor hexpOne
  have hy2real : (2 : ℝ) ≤ y := by
    have hgrowth : 2 * Real.log 2 ≤ Real.rpow (Real.log M) (1 / 2 : ℝ) := by
      have hAtwo : (2 : ℝ) < A := hA
      have hlog2lt : Real.log 2 < 1 := by
        calc
          Real.log 2 < Real.log (Real.exp 1) :=
            Real.strictMonoOn_log (by norm_num) (Real.exp_pos 1) Real.exp_one_gt_two
          _ = 1 := Real.log_exp 1
      calc
        2 * Real.log 2 ≤ 2 := (by linarith : 2 * Real.log 2 < 2).le
        _ ≤ Real.sqrt (Real.log M) := (hA.trans_le hsqrtLog_N).le
        _ = Real.rpow (Real.log M) (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    calc
      (2 : ℝ) ≤ Real.exp (Real.rpow (Real.log M) (1 / 2 : ℝ)) / 2 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        calc
          (2 : ℝ) * 2 = Real.exp (2 * Real.log 2) := by
            calc
              (2 : ℝ) * 2 = 4 := by norm_num
              _ = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
              _ = Real.exp (2 * Real.log 2) := by
                congr 1
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
                norm_num
          _ ≤ _ := Real.exp_le_exp.mpr hgrowth
      _ ≤ y := hyhalf
  have hy2 : 2 ≤ y := by exact_mod_cast hy2real
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hyupper : (y : ℝ) ≤ Real.exp (Real.rpow (Real.log M) (1 / 2 : ℝ)) :=
    Nat.floor_le (Real.exp_pos _).le
  have hlogyUpper : Real.log y ≤ Real.sqrt (Real.log M) := by
    calc
      Real.log y ≤ Real.rpow (Real.log M) (1 / 2 : ℝ) := by
        simpa only [Real.log_exp] using Real.log_le_log (by positivity) hyupper
      _ = Real.sqrt (Real.log M) := (Real.sqrt_eq_rpow _).symm
  have hsqrtSq : Real.sqrt (Real.log M) ^ 2 = Real.log M :=
    Real.sq_sqrt (by positivity)
  have huLower : Real.sqrt (Real.log M) ≤ u := by
    change Real.sqrt (Real.log M) ≤ Real.log M / Real.log y
    apply (le_div_iff₀ hlogy).2
    calc
      Real.sqrt (Real.log M) * Real.log y ≤
          Real.sqrt (Real.log M) * Real.sqrt (Real.log M) :=
        mul_le_mul_of_nonneg_left hlogyUpper (Real.sqrt_nonneg _)
      _ = Real.log M := by nlinarith [hsqrtSq]
  have huA : A ≤ u := hsqrtLog_N.trans huLower
  have hu1 : 1 ≤ u := le_trans (by linarith [hA] : (1 : ℝ) ≤ A) huA
  have hurpow : Real.rpow u (-u) ≤ 1 / u := by
    calc
      Real.rpow u (-u) ≤ Real.rpow u (-1) :=
        Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
      _ = (Real.rpow u 1)⁻¹ := Real.rpow_neg (zero_le_one.trans hu1) 1
      _ = u⁻¹ := congrArg Inv.inv (Real.rpow_one u)
      _ = 1 / u := by rw [one_div]
  have hinvu : 1 / u ≤ 1 / A := one_div_le_one_div_of_le (by linarith [hA]) huA
  have hinvM : Real.rpow M (-(1 / 2 : ℝ)) ≤ 1 / A := by
    calc
      Real.rpow (M : ℝ) (-(1 / 2 : ℝ)) =
          (Real.rpow (M : ℝ) (1 / 2 : ℝ))⁻¹ := Real.rpow_neg (by positivity) _
      _ = (Real.sqrt M)⁻¹ := congrArg Inv.inv (Real.sqrt_eq_rpow _).symm
      _ = 1 / Real.sqrt M := by rw [one_div]
      _ ≤ 1 / A := one_div_le_one_div_of_le (by linarith [hA]) hsqrtM_N
  have hAinv : 1 / A < ε / (2 * C) := by
    rw [one_div_lt (by linarith [hA]) (by positivity : 0 < ε / (2 * C))]
    dsimp only [A]
    field_simp
    nlinarith
  have herror : C * (Real.rpow u (-u) + Real.rpow M (-(1 / 2 : ℝ))) < ε := by
    have huSmall : Real.rpow u (-u) < ε / (2 * C) := (hurpow.trans hinvu).trans_lt hAinv
    have hMSmall : Real.rpow M (-(1 / 2 : ℝ)) < ε / (2 * C) := hinvM.trans_lt hAinv
    have hsum : Real.rpow u (-u) + Real.rpow M (-(1 / 2 : ℝ)) < ε / C := by
      calc
        Real.rpow u (-u) + Real.rpow M (-(1 / 2 : ℝ)) <
            2 * (ε / (2 * C)) := by linarith
        _ = ε / C := by field_simp
    calc
      C * (Real.rpow u (-u) + Real.rpow M (-(1 / 2 : ℝ))) < C * (ε / C) :=
        mul_lt_mul_of_pos_left hsum hC
      _ = ε := by field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · exact herror
  · exact mul_nonneg hC.le (add_nonneg (Real.rpow_nonneg (zero_le_one.trans hu1) _)
      (Real.rpow_nonneg (by positivity) _))

open Classical in
/-- Literature input: the Kubilius-model total-variation bound (Tenenbaum 1999, Théorème 1.1 and
(1.7), as quoted by Ford, arXiv 2408.03803v4, Theorem A), at `ε = 1/2`, projected to divisibility
indicators.  A named hypothesis, not an axiom. -/
def KubiliusTV : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N y : ℕ, 2 ≤ y → y ≤ N → ∀ A : Set (Finset ℕ),
    |(((Finset.Icc 1 N).filter (fun n => n.primeFactors.filter (· ≤ y) ∈ A)).card : ℝ) / N -
        kubiliusMass y A| ≤
      C * (Real.rpow (Real.log N / Real.log y) (-(Real.log N / Real.log y)) +
        Real.rpow N (-(1 / 2 : ℝ)))

/-- **Step 2 from the Kubilius model** (FDEK-free).  Same conclusion as
`divisorVariance_diverges_at_ln2`. -/
theorem divisorVariance_diverges_at_ln2_of_kubilius (hK : KubiliusTV)
    (v : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hv0 : ∀ m, 0 ≤ v m)
    (hv : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-Real.log 2) ≤ v m)
    (a₀ : ℕ) (T : ℝ) :
    Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n =>
        divisorVarianceMass v (collisionCutoff N) (n + a₀) ≤ T)).card : ℝ) / N)
      atTop (𝓝 0) := by
  sorry

/-- The candidate positive answer, FDEK-free: from the Kubilius model alone. -/
theorem ebPowerCandidateNormal_of_kubilius (hK : KubiliusTV) : EBPowerCandidateNormal := by
  intro a ha0 ha Ω _ μ _ X hX
  obtain ⟨c, hc, hvar⟩ := exists_powerDelta_variance_lower ha0 ha
  apply ebRandom_ae_normal_of_divisorVariance_diverges μ (powerDelta a) X hX
  intro a₀ T
  exact divisorVariance_diverges_at_ln2_of_kubilius hK
    (fun m ↦ powerDelta a m * (1 - powerDelta a m)) c hc
    (fun m ↦ mul_nonneg (hX.1 m).1 (sub_nonneg.mpr (hX.1 m).2))
    hvar a₀ T

end NormalNumbers.ErdosBorweinEndpointKub
