import NormalNumbers.PrimeModelKMTGradedModel
import NormalNumbers.PrimeModelJointLawGraded

/-!
# Theorem A: the graded finite window bound

Lap 6 of `KICKOFF-2026-09-22-multicutoff-lean.md`; spec `papers/ROUND2-multicutoff-fable.md` §2.
The five legs proved in laps 6a–6e are assembled by the triangle inequality

    ‖W‖ ≤ ‖W − W_{y⃗}‖ + ‖W_{y⃗} − M‖ + ‖M‖.

* `‖W − W_{y⃗}‖` — E1, `KMT.windowMean_sub_windowMeanLeG_le` (per-site cutoffs);
* `W_{y⃗} = ∑_t ν(t) F(t)` — `KMT.windowMeanLeG_eq_sum` (graded phase factorisation);
* `‖∑ ν F − ∑ μ F‖` — E4, `JointLaw.joint_phase_errorG` (per-shift retained box; the per-atom
  lower estimate is the sieve input `hlower`, supplied downstream by
  `BlockSieve.graded_brun_lower`);
* `‖∑ μ F‖` — E5, `KMT.norm_model_expectation_le_graded`; the contraction is collected only
  from the `S`-primes `≤ y_{j₀}`, so the tiers above the least nontrivial site are free.

`window_bound_graded_const` specialises to the constant schedule, where `∑_j a_j ≤ 4π|h|/3`
recovers the coefficient of `window_bound_regime_h`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.KMT

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.PhaseAlgebra NormalNumbers.PrimeModel.PhaseFactor
open NormalNumbers.PrimeModel.JointLaw NormalNumbers.PrimeModel.Params

variable (S : ℕ → Prop) [DecidablePred S]

/-- **Theorem A** (Fable §2): the graded finite window bound. -/
theorem window_bound_graded (k : ℕ) (y : Fin k → ℕ) (Y : ℕ) (hk : 1 ≤ k)
    (h : ℤ) (hntw : NontrivialWindow k h) (x : ℕ) (hx : 0 < x)
    (hky : ∀ j, k ≤ y j) (hyY : ∀ j, y j ≤ Y)
    (hmono : ∀ i j : Fin k, i ≤ j → y j ≤ y i)
    (hylog : 2 ≤ Real.log Y)
    {T : Fin k → ℝ} (hT : ∀ j, 1 ≤ T j)
    {η Rsq : ℝ} (hη : 0 ≤ η) (hRsq : 0 ≤ Rsq)
    (hlower : ∀ t : JointState k (midPrimes S k Y) (primorial k),
      (1 - η) * jointModel (Fin (primorial k)) k
          (primeRecip (primeOf (midPrimes S k Y))) t - Rsq / x
        ≤ empLaw (midPrimes S k Y) (primorial k) x t) :
    ∃ j₀ : Fin k,
      ‖windowMeanS S k h x‖
        ≤ (∑ j : Fin k, siteBudget h j.val * (2 * recipSumIoc S (y j) x + (k : ℝ) / x))
          + (2 * (∑ j : Fin k, Real.exp 20 / (T j) ^ (1 / (2 * Real.log Y)))
              + 2 * η
              + 2 * ((primorial k : ℕ) : ℝ) * (∏ j : Fin k, (Nat.floor (T j) : ℝ)) * Rsq / x)
          + Real.exp (2 * k)
              * Real.exp (- ∑ p ∈ (midPrimes S k Y).filter (fun p => p ≤ y j₀),
                  (1 : ℝ) / (p : ℝ)) := by
  classical
  set Q : ℕ := primorial k with hQ_def
  have hQpos : 0 < Q := primorial_pos k
  haveI : NeZero Q := ⟨hQpos.ne'⟩
  set P : Finset ℕ := midPrimes S k Y with hP_def
  have hP : ∀ p ∈ P, Nat.Prime p ∧ k < p ∧ p ≤ Y := fun p hp => by
    obtain ⟨h1, -, h3, h4⟩ := (mem_midPrimes S).mp hp
    exact ⟨h1, h3, h4⟩
  have hx1 : 1 ≤ x := hx
  have hE1 := windowMean_sub_windowMeanLeG_le S k y h x hx1
  have hWy := windowMeanLeG_eq_sum S k y Y hk hky hyY h x hx
  have hE4 := joint_phase_errorG P Q x hk hylog hP hQpos hx hT hη hRsq hlower
    (testFG S k y Y h Q) (norm_testFG_le S k y Y h Q)
  obtain ⟨j₀, hE5⟩ := norm_model_expectation_le_graded S k y Y hk h hntw Q hmono
  refine ⟨j₀, ?_⟩
  have htri : ‖windowMeanS S k h x‖
      ≤ ‖windowMeanS S k h x - windowMeanLeG S k y h x‖
        + ‖(∑ t : JointState k P Q, (empLaw P Q x t : ℂ) * testFG S k y Y h Q t)
            - ∑ t : JointState k P Q,
                (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ) * testFG S k y Y h Q t‖
        + ‖∑ t : JointState k P Q,
            (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ) * testFG S k y Y h Q t‖ := by
    rw [← hWy]
    calc ‖windowMeanS S k h x‖
        = ‖(windowMeanS S k h x - windowMeanLeG S k y h x)
            + ((windowMeanLeG S k y h x - ∑ t : JointState k P Q,
                (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ) * testFG S k y Y h Q t)
              + ∑ t : JointState k P Q,
                (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ)
                  * testFG S k y Y h Q t)‖ := by
          congr 1; ring
      _ ≤ _ := by
          refine (norm_add_le _ _).trans ?_
          have := norm_add_le (windowMeanLeG S k y h x - ∑ t : JointState k P Q,
                (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ) * testFG S k y Y h Q t)
            (∑ t : JointState k P Q,
                (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ) * testFG S k y Y h Q t)
          linarith
  calc ‖windowMeanS S k h x‖ ≤ _ := htri
    _ ≤ _ := by
        refine add_le_add (add_le_add hE1 ?_) hE5
        exact hE4

/-- The constant schedule recovers the coefficient of `window_bound_regime_h`. -/
theorem sum_siteBudget_const_le (h : ℤ) (k : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∑ j : Fin k, siteBudget h j.val * R ≤ (4 * Real.pi * |(h : ℝ)| / 3) * R := by
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_siteBudget_le h k) hR

end NormalNumbers.PrimeModel.KMT

#print axioms NormalNumbers.PrimeModel.KMT.window_bound_graded
