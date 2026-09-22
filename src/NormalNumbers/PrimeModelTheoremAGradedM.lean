import NormalNumbers.PrimeModelTheoremAGraded
import NormalNumbers.PrimeModelPhaseFactorSplit

/-!
# Theorem A on the graded state, with the split at `m ≥ k`

Leaf **G4′** of the graded-state regrade.  `window_bound_gradedG` splits the primes at `k`, so
its state primes satisfy only `k < q`.  The graded sieve needs `2 d_q ≤ q` with `d_q ≤ k`, i.e.
`q > 2k` — this is the paper's `Q = primorial (2k)` (Fable §2 E5, Astra §4).  So the version of
Theorem A that `JointLaw.empLawG_lower_atom` can actually be plugged into is the one split at
`m = 2k`, and that is what this file assembles, on top of `phase_factorisationGM`.

Everything is the `m`-indexed mirror of `PrimeModelTheoremAGraded`:

* `testFGM`, `windowMeanLeGM_eq_sumG` — the empirical side (the truncation identity
  `statePhaseGM_truncState` is again `zSee = 1` above the cutoff);
* `model_expectation_eqGM`, `norm_model_expectation_le_gradedM` — leg E5 at the split `m`; the
  contraction is still collected from the `S`-primes `≤ y_{j₀}`;
* `sum_jointModelGM_testFG_eq` — the model transfer;
* **`window_bound_gradedGM`** — the headline.  Its `hlower` is literally the conclusion of
  `JointLaw.empLawG_lower_atom` at `P = midPrimes S m Y`, `Q = primorial m`.

The class-count hypothesis is now **local to the state primes** (`hdp` ranges over
`q ∈ midPrimes S m Y`), which is what lets the caller clip `d_q` to `0` below `2k` and so satisfy
the sieve's global `2 d_q ≤ q`.  The schedule's monotonicity is therefore passed separately.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel

namespace PhaseFactor

open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState

variable (S : ℕ → Prop) [DecidablePred S]

/-- **The empirical transfer identity at the split `m`.** -/
theorem statePhaseGM_truncState (k m : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ) (dp : ℕ → ℕ)
    (hdp : ∀ q ∈ midPrimes S m Y, ∀ j : Fin k, q ≤ y j ↔ (j : ℕ) < dp q)
    (s : {q // q ∈ midPrimes S m Y} → Option (Fin k)) :
    statePhaseGM S k m y Y h (truncState k dp (midPrimes S m Y) s)
      = statePhaseGM S k m y Y h s := by
  classical
  unfold statePhaseGM
  refine Finset.prod_congr rfl fun i _ => ?_
  cases hsi : s i with
  | none =>
      have hn : truncState k dp (midPrimes S m Y) s i = none := by
        unfold truncState; rw [hsi]; rfl
      rw [hn]
  | some t =>
      by_cases ht : (t : ℕ) < dp (i : ℕ)
      · rw [truncState_eq_some_iff.mpr ⟨hsi, ht⟩]
      · have hnone : truncState k dp (midPrimes S m Y) s i = none :=
          truncState_eq_none_iff.mpr (fun u hu => by
            rw [hsi] at hu; rw [← Option.some.inj hu]; omega)
        have hz : zSee k y h (i : ℕ) t = 1 := by
          rw [zSee, if_neg (fun hc => ht ((hdp (i : ℕ) i.2 t).1 hc))]
        rw [hnone]
        simp [hz]

end PhaseFactor

end NormalNumbers.PrimeModel

namespace NormalNumbers.PrimeModel.KMT

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.PhaseAlgebra NormalNumbers.PrimeModel.PhaseFactor
open NormalNumbers.PrimeModel.JointLaw NormalNumbers.PrimeModel.Params

variable (S : ℕ → Prop) [DecidablePred S]

/-- The graded test function at the split `m`. -/
noncomputable def testFGM (k m : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ) (Q : ℕ) :
    JointState k (midPrimes S m Y) Q → ℂ :=
  fun t => residuePhaseM S k m h t.1.val * statePhaseGM S k m y Y h t.2

theorem norm_testFGM_le (k m : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ) (Q : ℕ)
    (t : JointState k (midPrimes S m Y) Q) : ‖testFGM S k m y Y h Q t‖ ≤ 1 := by
  unfold testFGM
  rw [norm_mul]
  exact mul_le_one₀ (norm_residuePhaseM_le S k m h _) (norm_nonneg _)
    (norm_statePhaseGM_le S k m y Y h _)

/-- `W_{y⃗}` is the graded empirical average of `testFGM`. -/
theorem windowMeanLeGM_eq_sumG (k m : ℕ) (y : Fin k → ℕ) (Y : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m)
    (dp : ℕ → ℕ) (hdp : ∀ q ∈ midPrimes S m Y, ∀ j : Fin k, q ≤ y j ↔ (j : ℕ) < dp q)
    (hmy : ∀ j, m ≤ y j) (hyY : ∀ j, y j ≤ Y) (h : ℤ) (x : ℕ) (hx : 0 < x) :
    windowMeanLeG S k y h x
      = ∑ t : JointState k (midPrimes S m Y) (primorial m),
          (empLawG (midPrimes S m Y) (primorial m) x k dp t : ℂ)
            * testFGM S k m y Y h (primorial m) t := by
  have hQ : 0 < primorial m := primorial_pos m
  rw [← prefixMean_eq_sum_empLawG (midPrimes S m Y) (primorial m) x k dp hQ hx]
  unfold windowMeanLeG prefixMean
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  show (∏ j : Fin k, zPhase h k j ^ omegaLe S (y j) (n + j.val + 1)) = _
  rw [phase_factorisationGM S k m y Y hk hkm hmy hyY h n]
  show _ = residuePhaseM S k m h _
      * statePhaseGM S k m y Y h (actualStateG k dp (midPrimes S m Y) n)
  rw [actualStateG, statePhaseGM_truncState S k m y Y h dp hdp]

/-- The graded model expectation at the split `m`, with a per-prime defect. -/
theorem model_expectation_eqGM (k m : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ) (Q : ℕ) [NeZero Q] :
    ∑ t : JointState k (midPrimes S m Y) Q,
        (jointModel (Fin Q) k (primeRecip (primeOf (midPrimes S m Y))) t : ℂ)
          * testFGM S k m y Y h Q t
      = ((∑ r : Fin Q, residuePhaseM S k m h r.val) / (Q : ℂ))
          * ∏ i : {q // q ∈ midPrimes S m Y},
              (1 + (∑ j : Fin k, (zSee k y h (i : ℕ) j - 1)) / ((i : ℕ) : ℂ)) := by
  rw [← radical_phase_product_prime k (primeOf (midPrimes S m Y))
    (fun i => zSee k y h (i : ℕ))]
  rw [Fintype.sum_prod_type]
  simp only [jointModel, testFGM, statePhaseGM, Fintype.card_fin]
  rw [div_mul_eq_mul_div, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  push_cast
  ring

/-- **Leg E5 at the split `m`.** -/
theorem norm_model_expectation_le_gradedM (k m : ℕ) (y : Fin k → ℕ) (Y : ℕ) (hk : 1 ≤ k)
    (hkm : k ≤ m) (h : ℤ) (hntw : NontrivialWindow k h) (Q : ℕ) [NeZero Q]
    (hmono : ∀ i j : Fin k, i ≤ j → y j ≤ y i) :
    ∃ j₀ : Fin k,
      ‖∑ t : JointState k (midPrimes S m Y) Q,
          (jointModel (Fin Q) k (primeRecip (primeOf (midPrimes S m Y))) t : ℂ)
            * testFGM S k m y Y h Q t‖
        ≤ Real.exp (2 * k)
            * Real.exp (- ∑ p ∈ (midPrimes S m Y).filter (fun p => p ≤ y j₀),
                (1 : ℝ) / (p : ℝ)) := by
  classical
  obtain ⟨j₀, hj₀⟩ := exists_site_re_nonpos k h hntw
  refine ⟨j₀, ?_⟩
  rw [model_expectation_eqGM S k m y Y h Q, norm_mul]
  set P : Finset ℕ := midPrimes S m Y with hP
  set p : {q // q ∈ P} → ℕ := primeOf P with hp
  have hinj : Function.Injective p := Subtype.val_injective
  have hkp : ∀ i : {q // q ∈ P}, k < p i := fun i =>
    lt_of_le_of_lt hkm ((mem_midPrimes S).mp i.2).2.2.1
  choose dsee hdsee using fun q : ℕ => exists_prefix_count k y hmono q
  have hrewrite : ∀ i : {q // q ∈ P},
      (∑ j : Fin k, (zSee k y h (i : ℕ) j - 1)) = prefixA (zPhase h k) (dsee (i : ℕ)) :=
    fun i => sum_zSee_sub_one_eq_prefixA k y h (i : ℕ) (dsee (i : ℕ)) (hdsee (i : ℕ))
  set G : Finset {q // q ∈ P} := Finset.univ.filter (fun i => (i : ℕ) ≤ y j₀) with hG
  have hGmem : ∀ i ∈ G, j₀.val < dsee (i : ℕ) := by
    intro i hi
    exact (hdsee (i : ℕ) j₀).1 (Finset.mem_filter.1 hi).2
  have hmodel := model_phase_norm_le_graded p hinj hk hkp (zPhase h k) (norm_zPhase h k)
    (fun i => dsee (p i)) hj₀ G hGmem
  have havg : ‖(∑ r : Fin Q, residuePhaseM S k m h r.val) / (Q : ℂ)‖ ≤ 1 := by
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
    rw [norm_div, Complex.norm_natCast, div_le_one hQpos]
    calc ‖∑ r : Fin Q, residuePhaseM S k m h r.val‖
        ≤ ∑ r : Fin Q, ‖residuePhaseM S k m h r.val‖ := norm_sum_le _ _
      _ ≤ ∑ _r : Fin Q, (1 : ℝ) :=
          Finset.sum_le_sum (fun r _ => norm_residuePhaseM_le S k m h _)
      _ = Q := by simp
  have hGsum : ∑ i ∈ G, (1 : ℝ) / ((p i : ℕ) : ℝ)
      = ∑ q ∈ P.filter (fun q => q ≤ y j₀), (1 : ℝ) / (q : ℝ) := by
    rw [hG, Finset.sum_filter, Finset.sum_filter]
    exact Finset.sum_coe_sort P (fun q => if q ≤ y j₀ then (1 : ℝ) / (q : ℝ) else 0)
  rw [hGsum] at hmodel
  calc ‖(∑ r : Fin Q, residuePhaseM S k m h r.val) / (Q : ℂ)‖
        * ‖∏ i : {q // q ∈ P},
            (1 + (∑ j : Fin k, (zSee k y h (i : ℕ) j - 1)) / ((i : ℕ) : ℂ))‖
      ≤ 1 * (Real.exp (2 * k)
          * Real.exp (- ∑ q ∈ P.filter (fun q => q ≤ y j₀), (1 : ℝ) / (q : ℝ))) := by
        refine mul_le_mul havg ?_ (norm_nonneg _) zero_le_one
        rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hrewrite i])]
        exact hmodel
    _ = _ := one_mul _

/-- **The model transfer at the split `m`.** -/
theorem sum_jointModelGM_testFG_eq (k m : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ) (Q : ℕ) [NeZero Q]
    (dp : ℕ → ℕ) (hdpk : ∀ q, dp q ≤ k)
    (hdp : ∀ q ∈ midPrimes S m Y, ∀ j : Fin k, q ≤ y j ↔ (j : ℕ) < dp q) :
    ∑ t : JointState k (midPrimes S m Y) Q,
        (jointModelG (Fin Q) k (fun i : {q // q ∈ midPrimes S m Y} => dp (i : ℕ))
          (primeRecip (primeOf (midPrimes S m Y))) t : ℂ) * testFGM S k m y Y h Q t
      = ∑ t : JointState k (midPrimes S m Y) Q,
        (jointModel (Fin Q) k (primeRecip (primeOf (midPrimes S m Y))) t : ℂ)
          * testFGM S k m y Y h Q t := by
  classical
  set P : Finset ℕ := midPrimes S m Y with hP
  have hz : ∀ i : {q // q ∈ P}, ∀ j : Fin k,
      dp (i : ℕ) ≤ (j : ℕ) → zSee k y h (i : ℕ) j = 1 := by
    intro i j hij
    rw [zSee, if_neg (fun hc => absurd ((hdp (i : ℕ) i.2 j).1 hc) (by omega))]
  have key := radical_phase_productG_eq (ι := {q // q ∈ P}) k
    (fun i : {q // q ∈ P} => dp (i : ℕ)) (fun i => hdpk (i : ℕ))
    (primeRecip (primeOf P)) (fun i => zSee k y h (i : ℕ)) hz
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hgen : ∀ w : ({q // q ∈ P} → Option (Fin k)) → ℝ,
      (∑ s : {q // q ∈ P} → Option (Fin k),
        ((w s / (Fintype.card (Fin Q) : ℝ) : ℝ) : ℂ)
          * (residuePhaseM S k m h r.val * ∏ i : {q // q ∈ P},
              localPhase k (zSee k y h (i : ℕ)) (s i)))
        = (residuePhaseM S k m h r.val / (Fintype.card (Fin Q) : ℂ))
            * ∑ s : {q // q ∈ P} → Option (Fin k),
                ((w s : ℝ) : ℂ) * ∏ i : {q // q ∈ P},
                  localPhase k (zSee k y h (i : ℕ)) (s i) := by
    intro w
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    push_cast
    ring
  simp only [jointModelG, jointModel, testFGM, statePhaseGM]
  rw [hgen (fun s => weightG k (fun i : {q // q ∈ P} => dp (i : ℕ))
      (primeRecip (primeOf P)) s),
    hgen (fun s => weight k (primeRecip (primeOf P)) s), key]

/-- **Theorem A on the graded state, split at `m ≥ k`** (G4′).  The per-atom hypothesis is
exactly the conclusion of `JointLaw.empLawG_lower_atom` at `P = midPrimes S m Y`,
`Q = primorial m`; with `m = 2k` the sieve's `2 d_q ≤ q` is available for a class count clipped
to `0` below `2k`, which is why the class-count equivalence `hdp` is only required on the state
primes. -/
theorem window_bound_gradedGM (k m : ℕ) (y : Fin k → ℕ) (Y : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m)
    (h : ℤ) (hntw : NontrivialWindow k h) (x : ℕ) (hx : 0 < x)
    (dp : ℕ → ℕ) (hdpk : ∀ q, dp q ≤ k)
    (hdp : ∀ q ∈ midPrimes S m Y, ∀ j : Fin k, q ≤ y j ↔ (j : ℕ) < dp q)
    (hmono : ∀ i j : Fin k, i ≤ j → y j ≤ y i)
    (hmy : ∀ j, m ≤ y j) (hyY : ∀ j, y j ≤ Y)
    (hylog : ∀ j, 2 ≤ Real.log (y j))
    {T : Fin k → ℝ} (hT : ∀ j, 1 ≤ T j)
    {η Rsq : ℝ} (hη : 0 ≤ η) (hRsq : 0 ≤ Rsq)
    (hlower : ∀ t : JointState k (midPrimes S m Y) (primorial m),
      (1 - η) * jointModelG (Fin (primorial m)) k
          (fun i : {q // q ∈ midPrimes S m Y} => dp (i : ℕ))
          (primeRecip (primeOf (midPrimes S m Y))) t - Rsq / x
        ≤ empLawG (midPrimes S m Y) (primorial m) x k dp t) :
    ∃ j₀ : Fin k,
      ‖windowMeanS S k h x‖
        ≤ (∑ j : Fin k, siteBudget h j.val * (2 * recipSumIoc S (y j) x + (k : ℝ) / x))
          + (2 * (∑ j : Fin k, Real.exp 20 / (T j) ^ (1 / (2 * Real.log (y j))))
              + 2 * η
              + 2 * ((primorial m : ℕ) : ℝ) * (∏ j : Fin k, (Nat.floor (T j) : ℝ)) * Rsq / x)
          + Real.exp (2 * k)
              * Real.exp (- ∑ p ∈ (midPrimes S m Y).filter (fun p => p ≤ y j₀),
                  (1 : ℝ) / (p : ℝ)) := by
  classical
  set Q : ℕ := primorial m with hQ_def
  have hQpos : 0 < Q := primorial_pos m
  haveI : NeZero Q := ⟨hQpos.ne'⟩
  set P : Finset ℕ := midPrimes S m Y with hP_def
  have hP : ∀ p ∈ P, Nat.Prime p ∧ k < p := fun p hp => by
    obtain ⟨h1, -, h3, -⟩ := (mem_midPrimes S).mp hp
    exact ⟨h1, lt_of_le_of_lt hkm h3⟩
  have hx1 : 1 ≤ x := hx
  have hE1 := windowMean_sub_windowMeanLeG_le S k y h x hx1
  have hWy := windowMeanLeGM_eq_sumG S k m y Y hk hkm dp hdp hmy hyY h x hx
  have hE4 := joint_phase_errorGG P Q x (y := fun j => ((y j : ℕ) : ℝ)) hk dp
    (fun q _ => hdpk q)
    (fun j => by
      have : 0 < y j := lt_of_lt_of_le hk (le_trans hkm (hmy j))
      exact_mod_cast this)
    hylog hP
    (fun j q hq hj => by exact_mod_cast (hdp q hq j).2 hj)
    hQpos hx hT hη hRsq hlower
    (testFGM S k m y Y h Q) (norm_testFGM_le S k m y Y h Q)
  have hmodel := sum_jointModelGM_testFG_eq S k m y Y h Q dp hdpk hdp
  obtain ⟨j₀, hE5'⟩ := norm_model_expectation_le_gradedM S k m y Y hk hkm h hntw Q hmono
  set MG : ℂ := ∑ t : JointState k P Q,
      (jointModelG (Fin Q) k (fun i : {q // q ∈ P} => dp (i : ℕ))
        (primeRecip (primeOf P)) t : ℂ) * testFGM S k m y Y h Q t with hMG
  set EG : ℂ := ∑ t : JointState k P Q,
      (empLawG P Q x k dp t : ℂ) * testFGM S k m y Y h Q t with hEG
  have hE5 : ‖MG‖ ≤ Real.exp (2 * k)
      * Real.exp (- ∑ p ∈ P.filter (fun p => p ≤ y j₀), (1 : ℝ) / (p : ℝ)) := by
    rw [hmodel]; exact hE5'
  refine ⟨j₀, ?_⟩
  have htri : ‖windowMeanS S k h x‖
      ≤ ‖windowMeanS S k h x - windowMeanLeG S k y h x‖ + ‖EG - MG‖ + ‖MG‖ := by
    calc ‖windowMeanS S k h x‖
        = ‖(windowMeanS S k h x - windowMeanLeG S k y h x) + ((EG - MG) + MG)‖ := by
          rw [← hWy]; congr 1; ring
      _ ≤ ‖windowMeanS S k h x - windowMeanLeG S k y h x‖ + ‖(EG - MG) + MG‖ :=
          norm_add_le _ _
      _ ≤ _ := by
          have := norm_add_le (EG - MG) MG
          linarith
  calc ‖windowMeanS S k h x‖ ≤ _ := htri
    _ ≤ _ := add_le_add (add_le_add hE1 hE4) hE5

end NormalNumbers.PrimeModel.KMT

#print axioms NormalNumbers.PrimeModel.KMT.window_bound_gradedGM
