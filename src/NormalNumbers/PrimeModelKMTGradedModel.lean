import NormalNumbers.PrimeModelKMTGraded
import NormalNumbers.PrimeModelPhaseFactorGraded

/-!
# Theorem A: the graded test function and the graded model expectation

Lap 6d of `KICKOFF-2026-09-22-multicutoff-lean.md`.  This is the graded mirror of
`PrimeModelKMT.testF` / `windowMeanLe_eq_sum` / `model_expectation_eq` /
`norm_model_expectation_le`:

* `testFG` — residue factor times the **graded** state phase `statePhaseG`;
* `windowMeanLeG_eq_sum` — `W_{y⃗} = ∑_t empLaw(t) · testFG(t)` (graded phase factorisation
  plus the fibre-sum identity);
* `model_expectation_eqG` — the model expectation factorises as
  `((1/Q)∑_r g₁(r)) · ∏_p (1 + A_{d_p}/p)` with the **per-prime** defect, because
  `Radical.radical_phase_product_prime` is already stated for a per-prime site vector;
* `norm_model_expectation_le_graded` — **Theorem A, leg E5, in place**:
  `‖M‖ ≤ e^{2k} · exp(−∑_{p ∈ P, p ≤ y_{j₀}} 1/p)`.  Only the primes below the cutoff of the
  least nontrivial site contribute to the contraction; the tiers above it are free.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.KMT

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.PhaseAlgebra NormalNumbers.PrimeModel.PhaseFactor
open NormalNumbers.PrimeModel.JointLaw NormalNumbers.PrimeModel.Params

variable (S : ℕ → Prop) [DecidablePred S]

/-- The graded test function on the joint state space. -/
noncomputable def testFG (k : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ) (Q : ℕ) :
    JointState k (midPrimes S k Y) Q → ℂ :=
  fun t => residuePhase S k h t.1.val * statePhaseG S k y Y h t.2

theorem norm_testFG_le (k : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ) (Q : ℕ)
    (t : JointState k (midPrimes S k Y) Q) : ‖testFG S k y Y h Q t‖ ≤ 1 := by
  unfold testFG
  rw [norm_mul]
  exact mul_le_one₀ (norm_residuePhase_le S k h _) (norm_nonneg _)
    (norm_statePhaseG_le S k y Y h _)

/-- `W_{y⃗} = ∑_t empLaw(t) · testFG(t)`. -/
theorem windowMeanLeG_eq_sum (k : ℕ) (y : Fin k → ℕ) (Y : ℕ) (hk : 1 ≤ k)
    (hky : ∀ j, k ≤ y j) (hyY : ∀ j, y j ≤ Y) (h : ℤ) (x : ℕ) (hx : 0 < x) :
    windowMeanLeG S k y h x
      = ∑ t : JointState k (midPrimes S k Y) (primorial k),
          (empLaw (midPrimes S k Y) (primorial k) x t : ℂ)
            * testFG S k y Y h (primorial k) t := by
  have hQ : 0 < primorial k := primorial_pos k
  rw [← prefixMean_eq_sum_empLaw (midPrimes S k Y) (primorial k) x hQ hx]
  unfold windowMeanLeG prefixMean
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  show (∏ j : Fin k, zPhase h k j ^ omegaLe S (y j) (n + j.val + 1)) = _
  rw [phase_factorisationG S k y Y hk hky hyY h n]
  rfl

/-- The graded model expectation factorises with a **per-prime** defect. -/
theorem model_expectation_eqG (k : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ) (Q : ℕ) [NeZero Q] :
    ∑ t : JointState k (midPrimes S k Y) Q,
        (jointModel (Fin Q) k (primeRecip (primeOf (midPrimes S k Y))) t : ℂ)
          * testFG S k y Y h Q t
      = ((∑ r : Fin Q, residuePhase S k h r.val) / (Q : ℂ))
          * ∏ i : {q // q ∈ midPrimes S k Y},
              (1 + (∑ j : Fin k, (zSee k y h (i : ℕ) j - 1)) / ((i : ℕ) : ℂ)) := by
  rw [← radical_phase_product_prime k (primeOf (midPrimes S k Y))
    (fun i => zSee k y h (i : ℕ))]
  rw [Fintype.sum_prod_type]
  simp only [jointModel, testFG, statePhaseG, Fintype.card_fin]
  rw [div_mul_eq_mul_div, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  push_cast
  ring

/-- **Theorem A, leg E5 in place.**  The contraction is collected only from the `S`-primes in
`(k, y_{j₀}]`: the tiers above the least nontrivial site's cutoff are free. -/
theorem norm_model_expectation_le_graded (k : ℕ) (y : Fin k → ℕ) (Y : ℕ) (hk : 1 ≤ k) (h : ℤ)
    (hntw : NontrivialWindow k h) (Q : ℕ) [NeZero Q]
    (hmono : ∀ i j : Fin k, i ≤ j → y j ≤ y i) :
    ∃ j₀ : Fin k,
      ‖∑ t : JointState k (midPrimes S k Y) Q,
          (jointModel (Fin Q) k (primeRecip (primeOf (midPrimes S k Y))) t : ℂ)
            * testFG S k y Y h Q t‖
        ≤ Real.exp (2 * k)
            * Real.exp (- ∑ p ∈ (midPrimes S k Y).filter (fun p => p ≤ y j₀),
                (1 : ℝ) / (p : ℝ)) := by
  classical
  obtain ⟨j₀, hj₀⟩ := exists_site_re_nonpos k h hntw
  refine ⟨j₀, ?_⟩
  rw [model_expectation_eqG S k y Y h Q, norm_mul]
  set P : Finset ℕ := midPrimes S k Y with hP
  set p : {q // q ∈ P} → ℕ := primeOf P with hp
  have hinj : Function.Injective p := Subtype.val_injective
  have hkp : ∀ i : {q // q ∈ P}, k < p i := fun i => ((mem_midPrimes S).mp i.2).2.2.1
  -- the per-prime defect is a prefix defect
  choose dsee hdsee using fun q : ℕ => exists_prefix_count k y hmono q
  have hrewrite : ∀ i : {q // q ∈ P},
      (∑ j : Fin k, (zSee k y h (i : ℕ) j - 1)) = prefixA (zPhase h k) (dsee (i : ℕ)) :=
    fun i => sum_zSee_sub_one_eq_prefixA k y h (i : ℕ) (dsee (i : ℕ)) (hdsee (i : ℕ))
  -- the good set: the primes that reach `j₀`
  set G : Finset {q // q ∈ P} := Finset.univ.filter (fun i => (i : ℕ) ≤ y j₀) with hG
  have hGmem : ∀ i ∈ G, j₀.val < dsee (i : ℕ) := by
    intro i hi
    exact (hdsee (i : ℕ) j₀).1 (Finset.mem_filter.1 hi).2
  have hmodel := model_phase_norm_le_graded p hinj hk hkp (zPhase h k) (norm_zPhase h k)
    (fun i => dsee (p i)) hj₀ G hGmem
  have havg : ‖(∑ r : Fin Q, residuePhase S k h r.val) / (Q : ℂ)‖ ≤ 1 := by
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
    rw [norm_div, Complex.norm_natCast, div_le_one hQpos]
    calc ‖∑ r : Fin Q, residuePhase S k h r.val‖
        ≤ ∑ r : Fin Q, ‖residuePhase S k h r.val‖ := norm_sum_le _ _
      _ ≤ ∑ _r : Fin Q, (1 : ℝ) := Finset.sum_le_sum (fun r _ => norm_residuePhase_le S k h _)
      _ = Q := by simp
  -- the sum over `G` is the reciprocal sum of the primes below `y_{j₀}`
  have hGsum : ∑ i ∈ G, (1 : ℝ) / ((p i : ℕ) : ℝ)
      = ∑ q ∈ P.filter (fun q => q ≤ y j₀), (1 : ℝ) / (q : ℝ) := by
    rw [hG, Finset.sum_filter, Finset.sum_filter]
    exact Finset.sum_coe_sort P (fun q => if q ≤ y j₀ then (1 : ℝ) / (q : ℝ) else 0)
  rw [hGsum] at hmodel
  calc ‖(∑ r : Fin Q, residuePhase S k h r.val) / (Q : ℂ)‖
        * ‖∏ i : {q // q ∈ P},
            (1 + (∑ j : Fin k, (zSee k y h (i : ℕ) j - 1)) / ((i : ℕ) : ℂ))‖
      ≤ 1 * (Real.exp (2 * k)
          * Real.exp (- ∑ q ∈ P.filter (fun q => q ≤ y j₀), (1 : ℝ) / (q : ℝ))) := by
        refine mul_le_mul havg ?_ (norm_nonneg _) zero_le_one
        rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hrewrite i])]
        exact hmodel
    _ = _ := one_mul _

end NormalNumbers.PrimeModel.KMT
