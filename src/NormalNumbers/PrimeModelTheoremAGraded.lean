import NormalNumbers.PrimeModelTheoremA
import NormalNumbers.PrimeModelJointGraded

/-!
# Theorem A on the graded state

Leaf **G4** of the graded-state regrade (`PENDING_WORK.md`, 2026-09-22 route correction).

`window_bound_graded` (lap 6) closes its E4 leg against the *ungraded* joint law: every prime is
offered all `k` shifts, so the per-atom hypothesis `hlower` must be supplied at the constant class
count and the shift-`j` Markov moment must run over the whole prime range.  Both are fatal — see
the review-lap refutation recorded in `DIRECTION.md`.

This file re-runs the assembly against the **graded** law of G3 (`empLawG`, `jointModelG`) at the
band-dependent class count `d_q = #{j : q ≤ y_j}`, which is the count `empLawG_lower_atom`
delivers, and against the graded box tail of G2, which gives the sharp per-site exponent
`1/(2 log y_j)`.

The two structural identities that make the regrade free:

* `statePhaseG_truncState` — the empirical transfer.  A prime assigned to a shift it does not
  reach carries the site factor `zSee = 1`, so the state phase does not see the truncation:
  `statePhaseG (truncState d s) = statePhaseG s`.  Hence `windowMeanLeG` is *also* the
  `empLawG`-average of `testFG` (`windowMeanLeG_eq_sumG`).
* `sum_jointModelG_testFG_eq` — the model transfer.  By `radical_phase_productG_eq` the graded and
  ungraded model expectations of `testFG` are equal, so leg E5
  (`norm_model_expectation_le_graded`) is reused verbatim.

Headline: `window_bound_gradedG`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel

/-! ## The band-dependent class count -/

namespace PhaseFactor

/-- For a decreasing schedule there is a class count `d_q ≤ k` with `q ≤ y_j ↔ j < d_q`. -/
theorem exists_dp_schedule (k : ℕ) (y : Fin k → ℕ)
    (hmono : ∀ i j : Fin k, i ≤ j → y j ≤ y i) :
    ∃ dp : ℕ → ℕ, (∀ q, dp q ≤ k) ∧ ∀ q, ∀ j : Fin k, q ≤ y j ↔ (j : ℕ) < dp q := by
  classical
  choose d hd using fun q : ℕ => exists_prefix_count k y hmono q
  refine ⟨fun q => min (d q) k, fun q => min_le_right _ _, fun q j => ?_⟩
  show q ≤ y j ↔ (j : ℕ) < min (d q) k
  rw [hd q j]
  have := j.isLt
  omega

/-- The schedule is decreasing as soon as the class count exists. -/
theorem mono_of_dp {k : ℕ} {y : Fin k → ℕ} {dp : ℕ → ℕ}
    (hdp : ∀ q, ∀ j : Fin k, q ≤ y j ↔ (j : ℕ) < dp q) :
    ∀ i j : Fin k, i ≤ j → y j ≤ y i := by
  intro i j hij
  have hj : (j : ℕ) < dp (y j) := (hdp (y j) j).1 le_rfl
  exact (hdp (y j) i).2 (lt_of_le_of_lt (by exact_mod_cast hij) hj)

end PhaseFactor

/-! ## The empirical transfer -/

namespace PhaseFactor

open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState

variable (S : ℕ → Prop) [DecidablePred S]

/-- **G4a, the empirical transfer identity.**  Truncating a state to each prime's own class count
does not change the graded state phase: a shift a prime does not reach carries the factor `1`. -/
theorem statePhaseG_truncState (k : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ) (dp : ℕ → ℕ)
    (hdp : ∀ q, ∀ j : Fin k, q ≤ y j ↔ (j : ℕ) < dp q)
    (s : {q // q ∈ midPrimes S k Y} → Option (Fin k)) :
    statePhaseG S k y Y h (truncState k dp (midPrimes S k Y) s) = statePhaseG S k y Y h s := by
  classical
  unfold statePhaseG
  refine Finset.prod_congr rfl fun i _ => ?_
  cases hsi : s i with
  | none =>
      have hn : truncState k dp (midPrimes S k Y) s i = none := by
        unfold truncState; rw [hsi]; rfl
      rw [hn]
  | some t =>
      by_cases ht : (t : ℕ) < dp (i : ℕ)
      · rw [truncState_eq_some_iff.mpr ⟨hsi, ht⟩]
      · have hnone : truncState k dp (midPrimes S k Y) s i = none :=
          truncState_eq_none_iff.mpr (fun u hu => by
            rw [hsi] at hu; rw [← Option.some.inj hu]; omega)
        have hz : zSee k y h (i : ℕ) t = 1 := by
          rw [zSee, if_neg (fun hc => ht ((hdp (i : ℕ) t).1 hc))]
        rw [hnone]
        simp [hz]

end PhaseFactor

/-! ## The graded fibre-sum identity -/

namespace JointLaw

open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState

variable {k : ℕ} (P : Finset ℕ) (Q x : ℕ)

/-- Fibre-sum identity for the graded empirical law. -/
theorem prefixMean_eq_sum_empLawG (k : ℕ) (dp : ℕ → ℕ) (hQ : 0 < Q) (hx : 0 < x)
    (F : JointState k P Q → ℂ) :
    (∑ n ∈ range x, F (⟨n % Q, Nat.mod_lt n hQ⟩, actualStateG k dp P n)) / (x : ℂ)
      = ∑ t : JointState k P Q, (empLawG P Q x k dp t : ℂ) * F t := by
  classical
  have key := Finset.sum_fiberwise_of_maps_to
    (g := fun n => ((⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q), actualStateG k dp P n))
    (s := range x) (t := (Finset.univ : Finset (JointState k P Q)))
    (fun n _ => Finset.mem_univ _)
    (fun n => F ((⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q), actualStateG k dp P n))
  have hfib : ∀ t : JointState k P Q,
      ((range x).filter
          (fun n => ((⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q), actualStateG k dp P n) = t))
        = ((range x).filter (fun n => n % Q = t.1.val ∧ actualStateG k dp P n = t.2)) := by
    intro t
    refine Finset.filter_congr fun n _ => ?_
    simp [Prod.ext_iff, Fin.ext_iff]
  have hinner : ∀ t : JointState k P Q,
      (∑ n ∈ (range x).filter
          (fun n => ((⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q), actualStateG k dp P n) = t),
          F ((⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q), actualStateG k dp P n))
        = (((range x).filter
            (fun n => n % Q = t.1.val ∧ actualStateG k dp P n = t.2)).card : ℂ) * F t := by
    intro t
    rw [Finset.sum_congr rfl (fun n hn => by rw [(Finset.mem_filter.mp hn).2]),
      Finset.sum_const, nsmul_eq_mul, hfib t]
  rw [← key, Finset.sum_congr rfl (fun t _ => hinner t), Finset.sum_div]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold empLawG
  push_cast
  ring

end JointLaw

/-! ## The graded E4 leg -/

namespace JointLaw

open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.BrunCount

variable {k : ℕ} (P : Finset ℕ) (Q x : ℕ)

/-- **G4b, Theorem A leg E4 on the graded law.**  The Markov moment at shift `j` now runs over
site `j`'s own primes, so the discarded-radical term carries the sharp exponent
`1/(2 log y_j)` — this is what closes the second wall of the review lap. -/
theorem joint_phase_errorGG {y : Fin k → ℝ} (hk : 1 ≤ k) {T : Fin k → ℝ} {η Rsq : ℝ}
    (dp : ℕ → ℕ) (hdpk : ∀ q ∈ P, dp q ≤ k)
    (hy0 : ∀ j, 0 < y j) (hylog : ∀ j, 2 ≤ Real.log (y j))
    (hP : ∀ p ∈ P, Nat.Prime p ∧ k < p)
    (hle : ∀ j : Fin k, ∀ q ∈ P, (j : ℕ) < dp q → (q : ℝ) ≤ y j)
    (hQ : 0 < Q) (hx : 0 < x) (hT : ∀ j, 1 ≤ T j)
    (hη : 0 ≤ η) (hRsq : 0 ≤ Rsq)
    (hlower : ∀ t : JointState k P Q,
      (1 - η) * jointModelG (Fin Q) k (fun i : {q // q ∈ P} => dp (i : ℕ))
          (primeRecip (primeOf P)) t - Rsq / x ≤ empLawG P Q x k dp t)
    (F : JointState k P Q → ℂ) (hF : ∀ t, ‖F t‖ ≤ 1) :
    ‖(∑ t : JointState k P Q, (empLawG P Q x k dp t : ℂ) * F t)
        - ∑ t : JointState k P Q,
            (jointModelG (Fin Q) k (fun i : {q // q ∈ P} => dp (i : ℕ))
              (primeRecip (primeOf P)) t : ℂ) * F t‖
      ≤ 2 * (∑ j : Fin k, Real.exp 20 / (T j) ^ (1 / (2 * Real.log (y j))))
        + 2 * η
        + 2 * (Q : ℝ) * (∏ j : Fin k, (Nat.floor (T j) : ℝ)) * Rsq / x := by
  classical
  have hQne : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  set dpi : {q // q ∈ P} → ℕ := fun i => dp (i : ℕ) with hdpi
  have hppos : ∀ i : {q // q ∈ P}, 0 < primeOf P i := fun i => (hP i.1 i.2).1.pos
  have hprime : ∀ i : {q // q ∈ P}, (primeOf P i).Prime := fun i => (hP i.1 i.2).1
  have hkp : ∀ i : {q // q ∈ P}, k ≤ primeOf P i := fun i => (hP i.1 i.2).2.le
  have hinj : Function.Injective (primeOf P) := Subtype.val_injective
  have hdk : ∀ i : {q // q ∈ P}, dpi i ≤ k := fun i => hdpk i.1 i.2
  have hdple : ∀ i : {q // q ∈ P}, dpi i ≤ primeOf P i := fun i =>
    le_trans (hdk i) (hkp i)
  set B : Finset (JointState k P Q) := Finset.univ ×ˢ retainedBoxG k (primeOf P) T with hB
  have hmain := finite_phase_of_lower_atoms
    (jointModelG (Fin Q) k dpi (primeRecip (primeOf P))) (empLawG P Q x k dp) B
    η (fun _ => Rsq / x)
    (fun i => jointModelG_nonneg hppos hdple i) (fun i => empLawG_nonneg P Q x k dp i)
    (jointModelG_mass_one (Fin Q) k dpi hdk (primeOf P)) (empLawG_mass_one P Q x k dp hQ hx)
    hη (fun i _ => by positivity)
    (fun i _ => hlower i)
    F hF
  have htail : ∑ i ∈ Bᶜ, jointModelG (Fin Q) k dpi (primeRecip (primeOf P)) i
      ≤ ∑ j : Fin k, Real.exp 20 / (T j) ^ (1 / (2 * Real.log (y j))) := by
    have h1 := jointModelG_tailG (Fin Q) k dpi (primeOf P) T
    have h2 := radical_box_tailGG_exp20 k (dp := dpi) (T := T) (y := y)
      hdk hinj hprime hkp hy0 hylog
      (fun j i hji => hle j i.1 i.2 hji) hT
    rw [hB]
    convert h1.trans_le h2 using 2
    ext a
    simp
  have hcardB : (B.card : ℝ) ≤ (Q : ℝ) * ∏ j : Fin k, (Nat.floor (T j) : ℝ) := by
    rw [hB, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    push_cast
    exact mul_le_mul_of_nonneg_left (retainedBoxG_card_le hprime hinj k hT) (by positivity)
  have he0 : (0 : ℝ) ≤ Rsq / x := by positivity
  have hsume : ∑ _i ∈ B, Rsq / x = (B.card : ℝ) * (Rsq / x) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hterm : (B.card : ℝ) * (Rsq / x)
      ≤ (Q : ℝ) * (∏ j : Fin k, (Nat.floor (T j) : ℝ)) * (Rsq / x) :=
    mul_le_mul_of_nonneg_right hcardB he0
  rw [hsume] at hmain
  have hshape : 2 * (Q : ℝ) * (∏ j : Fin k, (Nat.floor (T j) : ℝ)) * Rsq / x
      = 2 * ((Q : ℝ) * (∏ j : Fin k, (Nat.floor (T j) : ℝ)) * (Rsq / x)) := by ring
  rw [hshape]
  linarith

end JointLaw

end NormalNumbers.PrimeModel

namespace NormalNumbers.PrimeModel.KMT

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.PhaseAlgebra NormalNumbers.PrimeModel.PhaseFactor
open NormalNumbers.PrimeModel.JointLaw NormalNumbers.PrimeModel.Params

variable (S : ℕ → Prop) [DecidablePred S]

/-- `W_{y⃗}` is also the **graded** empirical average of `testFG`. -/
theorem windowMeanLeG_eq_sumG (k : ℕ) (y : Fin k → ℕ) (Y : ℕ) (hk : 1 ≤ k) (dp : ℕ → ℕ)
    (hdp : ∀ q, ∀ j : Fin k, q ≤ y j ↔ (j : ℕ) < dp q)
    (hky : ∀ j, k ≤ y j) (hyY : ∀ j, y j ≤ Y) (h : ℤ) (x : ℕ) (hx : 0 < x) :
    windowMeanLeG S k y h x
      = ∑ t : JointState k (midPrimes S k Y) (primorial k),
          (empLawG (midPrimes S k Y) (primorial k) x k dp t : ℂ)
            * testFG S k y Y h (primorial k) t := by
  have hQ : 0 < primorial k := primorial_pos k
  rw [← prefixMean_eq_sum_empLawG (midPrimes S k Y) (primorial k) x k dp hQ hx]
  unfold windowMeanLeG prefixMean
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  show (∏ j : Fin k, zPhase h k j ^ omegaLe S (y j) (n + j.val + 1)) = _
  rw [phase_factorisationG S k y Y hk hky hyY h n]
  show _ = residuePhase S k h _ * statePhaseG S k y Y h (actualStateG k dp (midPrimes S k Y) n)
  rw [actualStateG, statePhaseG_truncState S k y Y h dp hdp]

/-- **G4c, the model transfer.**  Grading the model does not move the expectation of `testFG`,
because `zSee` is trivial above each prime's cutoff. -/
theorem sum_jointModelG_testFG_eq (k : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ) (Q : ℕ) [NeZero Q]
    (dp : ℕ → ℕ) (hdpk : ∀ q, dp q ≤ k)
    (hdp : ∀ q, ∀ j : Fin k, q ≤ y j ↔ (j : ℕ) < dp q) :
    ∑ t : JointState k (midPrimes S k Y) Q,
        (jointModelG (Fin Q) k (fun i : {q // q ∈ midPrimes S k Y} => dp (i : ℕ))
          (primeRecip (primeOf (midPrimes S k Y))) t : ℂ) * testFG S k y Y h Q t
      = ∑ t : JointState k (midPrimes S k Y) Q,
        (jointModel (Fin Q) k (primeRecip (primeOf (midPrimes S k Y))) t : ℂ)
          * testFG S k y Y h Q t := by
  classical
  set P : Finset ℕ := midPrimes S k Y with hP
  have hz : ∀ i : {q // q ∈ P}, ∀ j : Fin k,
      dp (i : ℕ) ≤ (j : ℕ) → zSee k y h (i : ℕ) j = 1 := by
    intro i j hij
    rw [zSee, if_neg (fun hc => absurd ((hdp (i : ℕ) j).1 hc) (by omega))]
  have key := radical_phase_productG_eq (ι := {q // q ∈ P}) k
    (fun i : {q // q ∈ P} => dp (i : ℕ)) (fun i => hdpk (i : ℕ))
    (primeRecip (primeOf P)) (fun i => zSee k y h (i : ℕ)) hz
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hgen : ∀ w : ({q // q ∈ P} → Option (Fin k)) → ℝ,
      (∑ s : {q // q ∈ P} → Option (Fin k),
        ((w s / (Fintype.card (Fin Q) : ℝ) : ℝ) : ℂ)
          * (residuePhase S k h r.val * ∏ i : {q // q ∈ P},
              localPhase k (zSee k y h (i : ℕ)) (s i)))
        = (residuePhase S k h r.val / (Fintype.card (Fin Q) : ℂ))
            * ∑ s : {q // q ∈ P} → Option (Fin k),
                ((w s : ℝ) : ℂ) * ∏ i : {q // q ∈ P},
                  localPhase k (zSee k y h (i : ℕ)) (s i) := by
    intro w
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    push_cast
    ring
  simp only [jointModelG, jointModel, testFG, statePhaseG]
  rw [hgen (fun s => weightG k (fun i : {q // q ∈ P} => dp (i : ℕ))
      (primeRecip (primeOf P)) s),
    hgen (fun s => weight k (primeRecip (primeOf P)) s), key]

/-- **Theorem A on the graded state** (G4).  Same five legs as `window_bound_graded`, but the
per-atom hypothesis is taken on the **graded** law at the band-dependent class count
`d_q = #{j : q ≤ y_j}` (the count `JointLaw.empLawG_lower_atom` supplies), and the
discarded-radical term carries the per-site exponent `1/(2 log y_j)`. -/
theorem window_bound_gradedG (k : ℕ) (y : Fin k → ℕ) (Y : ℕ) (hk : 1 ≤ k)
    (h : ℤ) (hntw : NontrivialWindow k h) (x : ℕ) (hx : 0 < x)
    (dp : ℕ → ℕ) (hdpk : ∀ q, dp q ≤ k)
    (hdp : ∀ q, ∀ j : Fin k, q ≤ y j ↔ (j : ℕ) < dp q)
    (hky : ∀ j, k ≤ y j) (hyY : ∀ j, y j ≤ Y)
    (hylog : ∀ j, 2 ≤ Real.log (y j))
    {T : Fin k → ℝ} (hT : ∀ j, 1 ≤ T j)
    {η Rsq : ℝ} (hη : 0 ≤ η) (hRsq : 0 ≤ Rsq)
    (hlower : ∀ t : JointState k (midPrimes S k Y) (primorial k),
      (1 - η) * jointModelG (Fin (primorial k)) k
          (fun i : {q // q ∈ midPrimes S k Y} => dp (i : ℕ))
          (primeRecip (primeOf (midPrimes S k Y))) t - Rsq / x
        ≤ empLawG (midPrimes S k Y) (primorial k) x k dp t) :
    ∃ j₀ : Fin k,
      ‖windowMeanS S k h x‖
        ≤ (∑ j : Fin k, siteBudget h j.val * (2 * recipSumIoc S (y j) x + (k : ℝ) / x))
          + (2 * (∑ j : Fin k, Real.exp 20 / (T j) ^ (1 / (2 * Real.log (y j))))
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
  have hP : ∀ p ∈ P, Nat.Prime p ∧ k < p := fun p hp => by
    obtain ⟨h1, -, h3, -⟩ := (mem_midPrimes S).mp hp
    exact ⟨h1, h3⟩
  have hmono : ∀ i j : Fin k, i ≤ j → y j ≤ y i := mono_of_dp hdp
  have hx1 : 1 ≤ x := hx
  have hE1 := windowMean_sub_windowMeanLeG_le S k y h x hx1
  have hWy := windowMeanLeG_eq_sumG S k y Y hk dp hdp hky hyY h x hx
  have hE4 := joint_phase_errorGG P Q x (y := fun j => ((y j : ℕ) : ℝ)) hk dp
    (fun q _ => hdpk q)
    (fun j => by
      have : 0 < y j := lt_of_lt_of_le hk (hky j)
      exact_mod_cast this)
    hylog hP
    (fun j q hq hj => by exact_mod_cast (hdp q j).2 hj)
    hQpos hx hT hη hRsq hlower
    (testFG S k y Y h Q) (norm_testFG_le S k y Y h Q)
  have hmodel := sum_jointModelG_testFG_eq S k y Y h Q dp hdpk hdp
  obtain ⟨j₀, hE5'⟩ := norm_model_expectation_le_graded S k y Y hk h hntw Q hmono
  have hE5 : ‖∑ t : JointState k P Q,
      (jointModelG (Fin Q) k (fun i : {q // q ∈ P} => dp (i : ℕ))
        (primeRecip (primeOf P)) t : ℂ) * testFG S k y Y h Q t‖
      ≤ Real.exp (2 * k)
          * Real.exp (- ∑ p ∈ P.filter (fun p => p ≤ y j₀), (1 : ℝ) / (p : ℝ)) := by
    rw [hmodel]; exact hE5'
  refine ⟨j₀, ?_⟩
  set MG : ℂ := ∑ t : JointState k P Q,
      (jointModelG (Fin Q) k (fun i : {q // q ∈ P} => dp (i : ℕ))
        (primeRecip (primeOf P)) t : ℂ) * testFG S k y Y h Q t with hMG
  set EG : ℂ := ∑ t : JointState k P Q,
      (empLawG P Q x k dp t : ℂ) * testFG S k y Y h Q t with hEG
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

#print axioms NormalNumbers.PrimeModel.KMT.window_bound_gradedG
