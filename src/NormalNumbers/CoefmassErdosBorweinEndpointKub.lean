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
