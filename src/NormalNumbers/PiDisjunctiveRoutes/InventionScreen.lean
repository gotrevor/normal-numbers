/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Invention screen: three proposed sources of leverage that did not pass

Read `../../../MAZE.md` and `docs/pi-routes/invention-screen.md`.
These are elementary screening controls, not new pi-disjunctivity routes.
No statement below refutes all rational approximation, finite-state, or averaging
arguments.  In particular, failure of an absolute-error certificate does not
imply failure of proximity modulo one or disagreement of actual digits.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.InventionScreen

/-! ## Whole-period transfer versus approximation accuracy -/

/-- The usual absolute-error certificate for transporting a rational orbit
through `T` shifts.  Even this coarse threshold can fail before word margins enter. -/
def AbsoluteShadowBudget (b T : ℕ) (x r : ℝ) : Prop :=
  (b : ℝ) ^ T * |x - r| < 1

/-- A rational approximation lower bound limits the shifts accessible by an
absolute-error certificate.  The lower bound is an explicit hypothesis; no
particular irrationality-measure theorem for pi is silently assumed. -/
@[blueprint (title := "Approximation lower bounds obstruct full-period absolute-error transport")]
theorem not_absoluteShadowBudget_of_lower_bound
    (b T q μ : ℕ) (x : ℝ) (p : ℤ) (c : ℝ)
    (hq : 0 < q) (hc : 0 < c)
    (hlower : c / (q : ℝ) ^ μ ≤ |x - (p : ℝ) / q|)
    (hperiod : (q : ℝ) ^ μ ≤ c * (b : ℝ) ^ T) :
    ¬ AbsoluteShadowBudget b T x ((p : ℝ) / q) := by
  have hqp : (0 : ℝ) < (q : ℝ) ^ μ := by positivity
  have hlo := (div_le_iff₀ hqp).mp hlower
  have hprod := mul_le_mul_of_nonneg_right hperiod (abs_nonneg (x - (p : ℝ) / q))
  intro hbudget
  unfold AbsoluteShadowBudget at hbudget
  have hsmall := mul_lt_mul_of_pos_left hbudget hc
  nlinarith

/-- Exact scale controls.  Exponent 8 is illustrative, not a claimed pi bound.
The long horizon fails the budget test; the short horizon escapes that test. -/
theorem shadow_scale_controls :
    (101 : ℝ) ^ 8 ≤ 2 ^ 100 ∧ (2 : ℝ) ^ 10 < 101 ^ 8 := by norm_num

/-- The unrestricted proposed transport step: quadratic approximation accuracy
would suffice to certify the full q-1 horizon.  This is false. -/
def QuadraticAccuracyFullPeriodTransfer : Prop :=
  ∀ (q : ℕ) (p : ℤ) (x : ℝ), 2 ≤ q →
    |x - (p : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
    AbsoluteShadowBudget 2 (q - 1) x ((p : ℝ) / q)

theorem not_quadraticAccuracyFullPeriodTransfer :
    ¬ QuadraticAccuracyFullPeriodTransfer := by
  intro h
  have hc := h 11 1 (1 / 11 + 1 / 121) (by norm_num) (by norm_num)
  norm_num [AbsoluteShadowBudget] at hc

/-- The negative control really uses a full-period denominator: ord_11(2)=10.
The failure is the accuracy budget, not a denominator with a short period. -/
theorem denominator_eleven_full_period :
    2 ^ 10 % 11 = 1 ∧ ∀ t ∈ Finset.Ico 1 10, 2 ^ t % 11 ≠ 1 := by decide

/-! ## Recognizing a forbidden language does not countably specify its paths -/

def AvoidsAdjacentOnes (s : ℕ → Bool) : Prop :=
  ∀ n, s n = false ∨ s (n + 1) = false

/-- Place an arbitrary bit at each even position and zero at each odd position. -/
def separated (s : ℕ → Bool) (n : ℕ) : Bool :=
  if n % 2 = 0 then s (n / 2) else false

theorem separated_even (s : ℕ → Bool) (n : ℕ) :
    separated s (2 * n) = s n := by simp [separated]

theorem separated_avoids (s : ℕ → Bool) : AvoidsAdjacentOnes (separated s) := by
  intro n
  by_cases h : n % 2 = 0
  · right
    have h' : (n + 1) % 2 ≠ 0 := by omega
    simp [separated, h']
  · left
    simp [separated, h]

def CountableAvoiderCatalogue : Prop :=
  ∃ F : ℕ → ℕ → Bool, ∀ s, AvoidsAdjacentOnes s → ∃ n, s = F n

/-- Diagonal control against ANY countable catalogue, not just a particular
finite-state model.  Arbitrary paths must not be confused with finitely described
generators.  This is a stream statement, not a theorem about pi's actual stream. -/
@[blueprint (title := "A forbidden binary word does not give a countable catalogue of streams")]
theorem not_countableAvoiderCatalogue : ¬ CountableAvoiderCatalogue := by
  rintro ⟨F, hF⟩
  let s : ℕ → Bool := fun n => !(F n (2 * n))
  obtain ⟨n, hn⟩ := hF (separated s) (separated_avoids s)
  have he := congrFun hn (2 * n)
  rw [separated_even] at he
  dsimp [s] at he
  cases h : F n (2 * n) <;> simp [h] at he

/-! ## Averaging does not specialize to a prescribed parameter -/

/-- A proposed uniform mass-to-point estimate for nonnegative polynomials. -/
def UniformPolynomialEndpointBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Polynomial ℝ,
    (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ P.eval t) →
    P.eval 1 ≤ C * (∫ t in (0 : ℝ)..1, P.eval t)

/-- An analytic known-answer control: height one with integral 1/(n+1).
No limiting or almost-everywhere theorem is needed for this exact identity. -/
theorem polynomial_spike_control (n : ℕ) :
    ((Polynomial.X : Polynomial ℝ) ^ n).eval 1 = 1 ∧
    (∫ t in (0 : ℝ)..1, ((Polynomial.X : Polynomial ℝ) ^ n).eval t) =
      1 / ((n : ℝ) + 1) := by
  simp [integral_pow]

/-- Small average alone cannot give a uniform pointwise bound, even for
nonnegative polynomials.  Degree/derivative-sensitive estimates are not refuted. -/
@[blueprint (title := "Analytic parameter averages do not uniformly control a specified value")]
theorem not_uniformPolynomialEndpointBound : ¬ UniformPolynomialEndpointBound := by
  rintro ⟨C, hC, h⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hp := h (Polynomial.X ^ n) (by
    intro t ht
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    exact pow_nonneg ht.1 n)
  obtain ⟨heval, hint⟩ := polynomial_spike_control n
  rw [heval, hint] at hp
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlt : C * (1 / ((n : ℝ) + 1)) < 1 := by
    rw [mul_one_div, div_lt_one hnpos]
    linarith
  linarith

/-- A two-sided control removes any concern about the endpoint in the polynomial
example: a positive Gaussian on the whole real line has value one at the interior
point zero and any prescribed positive total mass. -/
@[blueprint (title := "Positive Gaussian averages can be arbitrarily small at fixed unit point value")]
theorem gaussian_spike_control (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧
      Real.exp (-B * (0 : ℝ) ^ 2) = 1 ∧
      (∀ t : ℝ, 0 < Real.exp (-B * t ^ 2)) ∧
      (∫ t : ℝ, Real.exp (-B * t ^ 2)) = ε := by
  refine ⟨Real.pi / ε ^ 2, by positivity, by simp, fun t => Real.exp_pos _, ?_⟩
  rw [integral_gaussian]
  have hratio : Real.pi / (Real.pi / ε ^ 2) = ε ^ 2 := by
    field_simp
  rw [hratio, Real.sqrt_sq hε.le]

end NormalNumbers.PiDisjunctiveRoutes.InventionScreen
