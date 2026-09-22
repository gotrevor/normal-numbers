import NormalNumbers.PrimeModelKMT

/-!
# Fixed-frequency window bound: phase-weighted transfer error

`windowMean_sub_windowMeanLe_le` (E1) bounds each site of the window product by
`‖z^{a+c} − z^a‖ ≤ 2c`, discarding the phase.  With the phase kept,
`‖z_j^{a+c} − z_j^a‖ ≤ c‖z_j − 1‖ ≤ c · 4π|h|/4^{j+1}`, and `∑_j 4π|h|/4^{j+1} ≤ 4π|h|/3`, so

    ‖W − W_y‖ ≤ (4π|h|/3) · (2 · recipSumIoc S y x + k/x)

with **no factor `k`** on the fresh mass (Astra, mail 20260922T190221Z).  Equivalent route: with
`A(n) = ∑_j ω_S(n+j+1)/4^{j+1}` and `A_y` its `≤y` truncation, `A − A_y = ∑_j ω_{>y}(n+j+1)/4^{j+1}
≥ 0`, and `norm_ePhase_sub` gives the same bound directly.

`window_bound_regime_h` is `window_bound_regime` with this E1 in place of the Cauchy–Schwarz
step; the frozen `KMT_quant₂` (uniform in `h`) is untouched.  The wiring consumes `KMT_along`,
which is a fixed-`h` statement, so this is exactly what the family theorems need.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.KMT

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel NormalNumbers.PrimeModel.PhaseAlgebra
open NormalNumbers.PrimeModel.PhaseFactor NormalNumbers.PrimeModel.JointLaw
open NormalNumbers.PrimeModel.Params
open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState

variable (S : ℕ → Prop) [DecidablePred S]

/-! ### Helpers for the phase-weighted E1 -/

/-- The per-site phase budget `4π|h|/4^{j+1}`. -/
private noncomputable def cq (h : ℤ) (j : ℕ) : ℝ :=
  4 * Real.pi * |(h : ℝ)| * ((1 : ℝ) / 4) ^ (j + 1)

private lemma cq_nonneg (h : ℤ) (j : ℕ) : 0 ≤ cq h j := by
  unfold cq; positivity

private lemma geom_quarter_sum (k : ℕ) :
    ∑ j ∈ Finset.range k, ((1 : ℝ) / 4) ^ (j + 1) ≤ 1 / 3 := by
  have heq : ∀ m : ℕ, ∑ j ∈ Finset.range m, ((1 : ℝ) / 4) ^ (j + 1)
      = (1 - ((1 : ℝ) / 4) ^ m) / 3 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  rw [heq k]
  have : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ k := by positivity
  linarith

private lemma sum_cq_le (h : ℤ) (k : ℕ) :
    ∑ j : Fin k, cq h j.val ≤ 4 * Real.pi * |(h : ℝ)| / 3 := by
  have h1 : ∑ j : Fin k, cq h j.val = ∑ j ∈ Finset.range k, cq h j :=
    Fin.sum_univ_eq_sum_range (fun j => cq h j) k
  have h2 : ∑ j ∈ Finset.range k, cq h j
      = (4 * Real.pi * |(h : ℝ)|) * ∑ j ∈ Finset.range k, ((1 : ℝ) / 4) ^ (j + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by unfold cq; ring
  rw [h1, h2]
  have hc : (0 : ℝ) ≤ 4 * Real.pi * |(h : ℝ)| := by positivity
  nlinarith [geom_quarter_sum k]

private lemma norm_zPhase_sub_one_le (h : ℤ) (k : ℕ) (j : Fin k) :
    ‖zPhase h k j - 1‖ ≤ cq h j.val := by
  have hz0 : ePhase (0 : ℝ) = 1 := by simp [ePhase]
  have hb := norm_ePhase_sub ((h : ℝ) / (4 : ℝ) ^ (j.val + 1)) 0
  rw [hz0] at hb
  have habs : |(h : ℝ) / (4 : ℝ) ^ (j.val + 1) - 0| = |(h : ℝ)| * ((1 : ℝ) / 4) ^ (j.val + 1) := by
    rw [sub_zero, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ (j.val + 1)),
      div_pow, one_pow]
    ring
  rw [habs] at hb
  have hzeq : zPhase h k j = ePhase ((h : ℝ) / (4 : ℝ) ^ (j.val + 1)) := rfl
  rw [hzeq]
  refine hb.trans (le_of_eq ?_)
  unfold cq; ring

private lemma norm_pow_sub_pow_le' (z : ℂ) (hz : ‖z‖ = 1) (a c : ℕ) {B : ℝ}
    (hB : ‖z - 1‖ ≤ B) : ‖z ^ (a + c) - z ^ a‖ ≤ (c : ℝ) * B := by
  have hrw : z ^ (a + c) - z ^ a = z ^ a * (z ^ c - 1) := by ring
  rw [hrw, norm_mul, norm_pow, hz, one_pow, one_mul]
  refine (norm_pow_sub_one_le z hz c).trans ?_
  exact mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg c)

/-- Phase-weighted E1. -/
theorem windowMean_sub_windowMeanLe_le_h (y k : ℕ) (h : ℤ) (x : ℕ) (hx : 1 ≤ x) :
    ‖windowMeanS S k h x - windowMeanLe S y k h x‖
      ≤ (4 * Real.pi * |(h : ℝ)| / 3) * (2 * recipSumIoc S y x + (k : ℝ) / x) := by
  classical
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hx0
  have hR0 : 0 ≤ recipSumIoc S y x := by
    unfold recipSumIoc
    exact Finset.sum_nonneg fun i _ => by positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have key : ∀ n : ℕ,
      ‖ePhase ((h : ℝ) * truncTailS S k n)
        - ∏ j : Fin k, zPhase h k j ^ omegaLe S y (n + j.val + 1)‖
        ≤ ∑ j : Fin k, cq h j.val * (omegaGt S y (n + j.val + 1) : ℝ) := by
    intro n
    rw [window_term_eq]
    refine le_trans (norm_prod_sub_prod_le Finset.univ _ _ ?_ ?_) ?_
    · intro i _; rw [norm_pow, norm_zPhase, one_pow]
    · intro i _; rw [norm_pow, norm_zPhase, one_pow]
    · refine Finset.sum_le_sum fun i _ => ?_
      rw [omegaSN_eq_omegaLe_add_omegaGt S y]
      refine le_trans (norm_pow_sub_pow_le' _ (norm_zPhase h k i) _ _
        (norm_zPhase_sub_one_le h k i)) (le_of_eq ?_)
      ring
  rw [windowMeanS, windowMeanLe, prefixMean, prefixMean, div_sub_div_same, norm_div,
    Complex.norm_natCast, ← Finset.sum_sub_distrib]
  rw [div_le_iff₀ hx0]
  have hmass : (0 : ℝ) ≤ 2 * (x : ℝ) * recipSumIoc S y x + k := by nlinarith
  have hnum : ‖∑ n ∈ Finset.range x,
      (ePhase ((h : ℝ) * truncTailS S k n)
        - ∏ j : Fin k, zPhase h k j ^ omegaLe S y (n + j.val + 1))‖
      ≤ (4 * Real.pi * |(h : ℝ)| / 3) * (2 * (x : ℝ) * recipSumIoc S y x + k) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun n _ => key n) ?_
    rw [Finset.sum_comm]
    have hj : ∀ j : Fin k,
        ∑ n ∈ Finset.range x, cq h j.val * (omegaGt S y (n + j.val + 1) : ℝ)
          ≤ cq h j.val * (2 * (x : ℝ) * recipSumIoc S y x + k) := by
      intro j
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_omegaGt_shift_le S y k x j.val j.isLt)
        (cq_nonneg h j.val)
    refine le_trans (Finset.sum_le_sum fun j _ => hj j) ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_cq_le h k) hmass
  refine hnum.trans (le_of_eq ?_)
  field_simp

/-- The window bound with the phase-weighted transfer term, in the same `Regime`. -/
theorem window_bound_regime_h {k x : ℕ} {ε : ℝ} (h : ℤ) (hntw : NontrivialWindow k h)
    (hR : Regime x k ε) :
    ‖windowMeanS S k h x‖
      ≤ (4 * Real.pi * |(h : ℝ)| / 3) * (2 * recipSumIoc S (yOf x ε) x + (k : ℝ) / x)
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
  have : NeZero Q := ⟨hQpos.ne'⟩
  have hE1 := windowMean_sub_windowMeanLe_le_h S y k h x hx1
  have hWy := windowMeanLe_eq_sum S k y hk (k_le_yOf hR) h x hx0
  have hE5 := norm_model_expectation_le S k y hk h hntw Q
  have hP' : ∀ p ∈ P, Nat.Prime p ∧ k < p ∧ p ≤ y := fun p hp => by
    obtain ⟨h1, _, h3, h4⟩ := (mem_midPrimes S).mp hp
    exact ⟨h1, h3, h4⟩
  have hQcop : ∀ p ∈ P, Nat.Coprime Q p := fun p hp =>
    primorial_coprime_of_lt (hP' p hp).1 (hP' p hp).2.1
  have hE4 := joint_phase_error P Q x hk (yOf_ge_exp_two hR) (log_yOf_ge_two hR)
    (sigmaOf_thresholds hR).1 (sigmaOf_thresholds hR).2 hP' hQpos hQcop hx0 (TOf_ge_one hR)
    (testF S k y h Q) (norm_testF_le S k y h Q)
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
  have h2k2 : 0 ≤ 2 * (k : ℝ) ^ 2 * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := by positivity
  calc ‖windowMeanS S k h x‖
      ≤ _ := htri
    _ ≤ ((4 * Real.pi * |(h : ℝ)| / 3) * (2 * recipSumIoc S y x + (k : ℝ) / x))
        + (2 * ((k : ℝ) * Real.exp 20 / T ^ (1 / (2 * Real.log y)))
          + 4 * Real.exp (-σ / 2)
          + 2 * (Q : ℝ) * (Nat.floor T : ℝ) ^ k * ((y : ℝ) ^ σ) ^ 2 / x)
        + Real.exp (2 * k) * Real.exp (- ∑ i : {q // q ∈ P}, (1 : ℝ) / ((i : ℕ) : ℝ)) :=
        add_le_add (add_le_add hE1 hE4) hE5
    _ ≤ _ := by
        have hdist : (2 * (k : ℝ) ^ 2 + 2 * (k : ℝ) * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ k)
            * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε))
            = 2 * (k : ℝ) ^ 2 * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε))
              + 2 * ((k : ℝ) * Real.exp 20 * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)))
              + 4 * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε))
              + 2 * ((4 : ℝ) ^ k * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε))) := by ring
        rw [hdist]
        linarith

end NormalNumbers.PrimeModel.KMT
