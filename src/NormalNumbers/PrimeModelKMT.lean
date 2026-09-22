import NormalNumbers.PrimeModelPhaseFactor
import NormalNumbers.PrimeModelJointLaw
import NormalNumbers.PrimeModelParameters
import NormalNumbers.PrimeModelErrorBudget

/-!
# Prime model, assembly part E: the frozen `KMT_quant₂` and its consequence

`papers/prime-model-assembly-2026-09-22.md`.  Assembles parts A–D into the literal frozen
statement `KMT_quant₂ C₁ C₂` with `C₁ k = exp(4k)`, `C₂ k = exp(exp(k+7))`, and feeds it to
the existing block construction `exists_sparse_normal_of_KMT_quant₂`.

    ‖W‖ ≤ ‖W − W_y‖ + ‖W_y − M‖ + ‖M‖
        ≤ [4k·recipSumIoc + 2k²/x]                               (E1, part B)
          + [2 k e^{20}/T^{1/(2 log y)} + 4e^{−σ/2} + 2Q⌊T⌋^k R²/x]  (E4, part C)
          + e^{2k} exp(−∑_{p∈P} 1/p)                             (E5, part A)

and every bracket is absorbed by the frozen right-hand side (part D).  Regime R1
(`ε > 1/(7680k)`) uses the trivial bound and `brun_large_epsilon_absorbed`.

The result is uniform in `S` and in `h`; the only use of `h` is the least nontrivial site.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.KMT

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.PhaseAlgebra NormalNumbers.PrimeModel.PhaseFactor
open NormalNumbers.PrimeModel.JointLaw NormalNumbers.PrimeModel.Params

variable (S : ℕ → Prop) [DecidablePred S]

/-- The test function on the joint state space: residue factor times state factor. -/
noncomputable def testF (k y : ℕ) (h : ℤ) (Q : ℕ) :
    JointState k (midPrimes S k y) Q → ℂ :=
  fun t => residuePhase S k h t.1.val * statePhase S k y h t.2

lemma norm_testF_le (k y : ℕ) (h : ℤ) (Q : ℕ) (t : JointState k (midPrimes S k y) Q) :
    ‖testF S k y h Q t‖ ≤ 1 := by
  unfold testF
  rw [norm_mul]
  exact mul_le_one₀ (norm_residuePhase_le S k h _) (norm_nonneg _) (norm_statePhase_le S k y h _)

/-- `W_y = ∑_t empLaw t · testF t` (phase factorisation + fibre-sum identity). -/
theorem windowMeanLe_eq_sum (k y : ℕ) (hk : 1 ≤ k) (h : ℤ) (x : ℕ) (hx : 0 < x) :
    windowMeanLe S y k h x
      = ∑ t : JointState k (midPrimes S k y) (primorial k),
          (empLaw (midPrimes S k y) (primorial k) x t : ℂ) * testF S k y h (primorial k) t := by
  have hQ : 0 < primorial k := primorial_pos k
  rw [← prefixMean_eq_sum_empLaw (midPrimes S k y) (primorial k) x hQ hx]
  unfold windowMeanLe prefixMean
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  show (∏ j : Fin k, zPhase h k j ^ omegaLe S y (n + j.val + 1)) = _
  rw [phase_factorisation S k y hk h n]
  rfl

/-- The model expectation factorises: `∑_t jointModel t · testF t = (avg residue) · ∏_i (1 + A/p_i)`. -/
theorem model_expectation_eq (k y : ℕ) (h : ℤ) (Q : ℕ) [NeZero Q] :
    ∑ t : JointState k (midPrimes S k y) Q,
        (jointModel (Fin Q) k (primeRecip (primeOf (midPrimes S k y))) t : ℂ) * testF S k y h Q t
      = ((∑ r : Fin Q, residuePhase S k h r.val) / (Q : ℂ))
          * ∏ i : {q // q ∈ midPrimes S k y},
              (1 + (∑ j : Fin k, (zPhase h k j - 1)) / ((i : ℕ) : ℂ)) := by
  rw [← radical_phase_product_prime k (primeOf (midPrimes S k y)) (fun _ => zPhase h k)]
  rw [Fintype.sum_prod_type]
  simp only [jointModel, testF, Fintype.card_fin]
  rw [div_mul_eq_mul_div, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [statePhase]
  push_cast
  ring

/-- `‖∑ jointModel · testF‖ ≤ e^{2k} exp(−∑_{p∈P} 1/p)`. -/
theorem norm_model_expectation_le (k y : ℕ) (hk : 1 ≤ k) (h : ℤ) (hntw : NontrivialWindow k h)
    (Q : ℕ) [NeZero Q] :
    ‖∑ t : JointState k (midPrimes S k y) Q,
        (jointModel (Fin Q) k (primeRecip (primeOf (midPrimes S k y))) t : ℂ) * testF S k y h Q t‖
      ≤ Real.exp (2 * k)
          * Real.exp (- ∑ i : {q // q ∈ midPrimes S k y}, (1 : ℝ) / ((i : ℕ) : ℝ)) := by
  rw [model_expectation_eq S k y h Q, norm_mul]
  obtain ⟨j₀, hj₀⟩ := exists_site_re_nonpos k h hntw
  have hinj : Function.Injective (primeOf (midPrimes S k y)) := Subtype.val_injective
  have hkp : ∀ i : {q // q ∈ midPrimes S k y}, k < primeOf (midPrimes S k y) i :=
    fun i => ((mem_midPrimes S).mp i.2).2.2.1
  have hmodel := model_phase_norm_le (primeOf (midPrimes S k y)) hinj hk hkp (zPhase h k)
    (norm_zPhase h k) j₀ hj₀
  have havg : ‖(∑ r : Fin Q, residuePhase S k h r.val) / (Q : ℂ)‖ ≤ 1 := by
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
    rw [norm_div, Complex.norm_natCast, div_le_one hQpos]
    calc ‖∑ r : Fin Q, residuePhase S k h r.val‖
        ≤ ∑ r : Fin Q, ‖residuePhase S k h r.val‖ := norm_sum_le _ _
      _ ≤ ∑ _r : Fin Q, (1 : ℝ) := Finset.sum_le_sum (fun r _ => norm_residuePhase_le S k h _)
      _ = Q := by simp
  calc ‖(∑ r : Fin Q, residuePhase S k h r.val) / (Q : ℂ)‖
        * ‖∏ i : {q // q ∈ midPrimes S k y},
            (1 + (∑ j : Fin k, (zPhase h k j - 1)) / ((i : ℕ) : ℂ))‖
      ≤ 1 * (Real.exp (2 * k)
          * Real.exp (- ∑ i : {q // q ∈ midPrimes S k y}, (1 : ℝ) / ((i : ℕ) : ℝ))) :=
        mul_le_mul havg hmodel (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **The main-regime bound**, with every error term written out. -/
theorem window_bound_regime {k x : ℕ} {ε : ℝ} (h : ℤ) (hntw : NontrivialWindow k h)
    (hR : Regime x k ε) :
    ‖windowMeanS S k h x‖
      ≤ 24 * (k : ℝ) * (Real.sqrt (Real.log (1 / ε))
            * Real.sqrt (2 * recipSumIoc S (yOf x ε) x))
        + Real.exp (3 * k) * Real.exp (- recipSumLe S (yOf x ε))
        + (2 * (k : ℝ) ^ 2 + 2 * (k : ℝ) * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ k)
            * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := by
  classical
  have hk : 1 ≤ k := hR.hk
  have hx0 : 0 < x := by have := hR.hx; omega
  have hx1 : 1 ≤ x := hx0
  set y := yOf x ε with hy_def
  set σ := sigmaOf x ε with hσ_def
  set T := TOf x k with hT_def
  set Q := primorial k with hQ_def
  set P := midPrimes S k y with hP_def
  have hQpos : 0 < Q := primorial_pos k
  haveI : NeZero Q := ⟨hQpos.ne'⟩
  -- the three pieces
  have hE1 := windowMean_sub_windowMeanLe_le S y k h x hx1
  have hWy := windowMeanLe_eq_sum S k y hk h x hx0
  have hE5 := norm_model_expectation_le S k y hk h hntw Q
  have hP' : ∀ p ∈ P, Nat.Prime p ∧ k < p ∧ p ≤ y := fun p hp => by
    obtain ⟨h1, _, h3, h4⟩ := (mem_midPrimes S).mp hp
    exact ⟨h1, h3, h4⟩
  have hQcop : ∀ p ∈ P, Nat.Coprime Q p := fun p hp =>
    primorial_coprime_of_lt (hP' p hp).1 (hP' p hp).2.1
  have hE4 := joint_phase_error P Q x hk (yOf_ge_exp_two hR) (log_yOf_ge_two hR)
    (sigmaOf_thresholds hR).1 (sigmaOf_thresholds hR).2 hP' hQpos hQcop hx0 (TOf_ge_one hR)
    (testF S k y h Q) (norm_testF_le S k y h Q)
  -- absorption of each error
  have habs1 := recipSumIoc_cs hR S
  have habs2 := inv_x_le_expTerm hR
  have habs3 := tail_absorbed hR
  have habs4 := sieve_absorbed hR
  have habs5 := remainder_absorbed hR
  have hrec := recipSumLe_le_sum_midPrimes S k y
  have hE5' : Real.exp (2 * k)
      * Real.exp (- ∑ i : {q // q ∈ P}, (1 : ℝ) / ((i : ℕ) : ℝ))
      ≤ Real.exp (3 * k) * Real.exp (- recipSumLe S y) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hexp0 : 0 ≤ Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := (Real.exp_pos _).le
  -- combine
  have htri : ‖windowMeanS S k h x‖
      ≤ ‖windowMeanS S k h x - windowMeanLe S y k h x‖
        + ‖(∑ t : JointState k P Q, (empLaw P Q x t : ℂ) * testF S k y h Q t)
            - ∑ t : JointState k P Q,
                (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ) * testF S k y h Q t‖
        + ‖∑ t : JointState k P Q,
            (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ) * testF S k y h Q t‖ := by
    rw [← hWy]
    calc ‖windowMeanS S k h x‖
        = ‖(windowMeanS S k h x - windowMeanLe S y k h x)
            + ((windowMeanLe S y k h x - ∑ t : JointState k P Q,
                (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ) * testF S k y h Q t)
              + ∑ t : JointState k P Q,
                (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ) * testF S k y h Q t)‖ := by
          congr 1; ring
      _ ≤ _ := by
          refine (norm_add_le _ _).trans ?_
          have := norm_add_le (windowMeanLe S y k h x - ∑ t : JointState k P Q,
                (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ) * testF S k y h Q t)
            (∑ t : JointState k P Q,
                (jointModel (Fin Q) k (primeRecip (primeOf P)) t : ℂ) * testF S k y h Q t)
          linarith
  have hx2 : 2 * (k : ℝ) ^ 2 / x = 2 * (k : ℝ) ^ 2 * (1 / (x : ℝ)) := by ring
  have hk2 : (0 : ℝ) ≤ 2 * (k : ℝ) ^ 2 := by positivity
  have hrem : 2 * (Q : ℝ) * (Nat.floor T : ℝ) ^ k * ((y : ℝ) ^ σ) ^ 2 / x
      = 2 * (((primorial k : ℕ) : ℝ) * (Nat.floor (TOf x k) : ℝ) ^ k
          * ((yOf x ε : ℝ) ^ sigmaOf x ε) ^ 2 / x) := by
    simp only [hQ_def, hT_def, hy_def, hσ_def]; ring
  have htail : 2 * ((k : ℝ) * Real.exp 20 / T ^ (1 / (2 * Real.log y)))
      ≤ 2 * ((k : ℝ) * Real.exp 20 * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε))) := by
    have := habs3; simp only [hT_def, hy_def] at this ⊢; linarith
  have hsieve : 4 * Real.exp (-σ / 2) ≤ 4 * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := by
    have := habs4; simp only [hσ_def] at this ⊢; linarith
  have hremainder : 2 * (Q : ℝ) * (Nat.floor T : ℝ) ^ k * ((y : ℝ) ^ σ) ^ 2 / x
      ≤ 2 * ((4 : ℝ) ^ k * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε))) := by
    rw [hrem]; linarith [habs5]
  have hinvx : 2 * (k : ℝ) ^ 2 / x ≤ 2 * (k : ℝ) ^ 2 * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := by
    rw [hx2]; exact mul_le_mul_of_nonneg_left habs2 hk2
  calc ‖windowMeanS S k h x‖
      ≤ _ := htri
    _ ≤ (4 * k * recipSumIoc S y x + 2 * (k : ℝ) ^ 2 / x)
        + (2 * ((k : ℝ) * Real.exp 20 / T ^ (1 / (2 * Real.log y)))
          + 4 * Real.exp (-σ / 2)
          + 2 * (Q : ℝ) * (Nat.floor T : ℝ) ^ k * ((y : ℝ) ^ σ) ^ 2 / x)
        + Real.exp (2 * k) * Real.exp (- ∑ i : {q // q ∈ P}, (1 : ℝ) / ((i : ℕ) : ℝ)) :=
        add_le_add (add_le_add hE1 hE4) hE5
    _ ≤ _ := by
        nlinarith [habs1, hinvx, htail, hsieve, hremainder, hE5', hexp0, hk0]

/-- **The literal frozen statement.**  `KMT_quant₂ C₁ C₂` with `C₁ k = exp(4k)`,
`C₂ k = exp(exp(k+7))`, uniformly in the prime set `S` and the frequency `h`. -/
theorem KMT_quant₂_primeModel : KMT_quant₂ C₁ C₂ := by
  intro S _ J h hh hntw x hx ε hε1 hε2
  have hJ : 1 ≤ J := by
    obtain ⟨j, hj1, hjJ, _⟩ := hntw
    omega
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hexp0 : 0 ≤ Real.exp (-1 / (8 * (J : ℝ) ^ 2 * ε)) := (Real.exp_pos _).le
  have hdist0 : 0 ≤ Real.sqrt (Real.log (1 / ε))
      * Real.sqrt (2 * recipSumIoc S ⌊(x : ℝ) ^ ε⌋₊ x)
      + Real.exp (- recipSumLe S ⌊(x : ℝ) ^ ε⌋₊) := by positivity
  have hC₁0 : 0 ≤ C₁ J := (Real.exp_pos _).le
  by_cases hreg : ε ≤ 1 / (7680 * J)
  · -- regime R2: the main bound
    have hR : Regime x J ε := ⟨hx, hJ, hε1, hreg⟩
    have hmain := window_bound_regime S h hntw hR
    have hc1 := const_one_le hJ
    have hc2 := const_two_le hJ
    have hy : yOf x ε = ⌊(x : ℝ) ^ ε⌋₊ := rfl
    rw [hy] at hmain
    have hs0 : 0 ≤ Real.sqrt (Real.log (1 / ε))
        * Real.sqrt (2 * recipSumIoc S ⌊(x : ℝ) ^ ε⌋₊ x) := by positivity
    have he0 : 0 ≤ Real.exp (- recipSumLe S ⌊(x : ℝ) ^ ε⌋₊) := (Real.exp_pos _).le
    have hJ0 : (0 : ℝ) ≤ 24 * J := by positivity
    have h3 : 0 ≤ Real.exp (3 * J) := (Real.exp_pos _).le
    nlinarith [hmain, hc1, hc2, hs0, he0, hexp0, hJ0, h3]
  · -- regime R1: trivial bound
    push_neg at hreg
    have htriv := norm_windowMeanS_le_one S J h x
    have habs := NormalNumbers.PrimeModel.brun_large_epsilon_absorbed (J : ℝ) ε hJr hreg
    have hC₂ := exp_960_le_C₂ J
    calc ‖windowMeanS S J h x‖ ≤ 1 := htriv
      _ ≤ Real.exp 960 * Real.exp (-1 / (8 * (J : ℝ) ^ 2 * ε)) := habs
      _ ≤ C₂ J * Real.exp (-1 / (8 * (J : ℝ) ^ 2 * ε)) :=
          mul_le_mul_of_nonneg_right hC₂ hexp0
      _ ≤ _ := by nlinarith [hdist0, hC₁0]

/-- **Unconditional sparse normality.**  There is a prime set `S` with `∑_{p∈S} 1/p = ∞` whose
base-4 Lambert constant `∑_{p∈S} 1/(4^p − 1)` is normal in base 4. -/
theorem exists_sparse_normal_unconditional :
    ∃ (S : ℕ → Prop) (_ : DecidablePred S),
      DivergentRecip S ∧ IsNormal 4 (subsetLambert S 4) :=
  exists_sparse_normal_of_KMT_quant₂ C₁ C₂ growth_C₁ growth_C₂ KMT_quant₂_primeModel

end NormalNumbers.PrimeModel.KMT
