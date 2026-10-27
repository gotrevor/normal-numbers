/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.MasterLnTwoBase3
import NormalNumbers.DisjunctiveCorollaries
import NormalNumbers.WallRational
import NormalNumbers.GrowingLocalizedLog

/-!
# Three mechanism checks for ln(2)

Read `../../../MAZE.md` and `docs/ln-two-routes/screen.md`.
Definitions of propositions below are open inputs or explicitly unproved
experiment records, not theorems.  None proves disjunctivity of ln(2).
-/

namespace NormalNumbers.LnTwoRoutes

open Filter

/-! ## 1. Accelerating the kick without losing track of rational shifts -/

def betaKick (m n : ℕ) : ℚ :=
  (m.factorial : ℚ) / ∏ j ∈ Finset.range (m + 1), (n + j : ℚ)

def alternatingHarmonic (m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range m, (-1 : ℚ) ^ j / (j + 1)

/-- Euler's beta-integral identity, 99% confidence, not proved here.
Integrate u^m/(1+u) on [0,1], using polynomial division and the
geometric expansion of 1/(2-t) after t=1-u. -/
@[blueprint (title := "Euler-accelerated logarithm: explicit identity input")]
def AcceleratedLogIdentity : Prop :=
  ∀ m : ℕ, HasSum
    (fun n : ℕ => (betaKick m (n + 1) : ℝ) / 2 ^ (n + 1))
    ((-1 : ℝ) ^ m * (Real.log 2 - (alternatingHarmonic m : ℝ)))

def clonePotential (m n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range m, (-1 : ℚ) ^ j * betaKick j n

def cloneKick (m n : ℕ) : ℚ :=
  2 * clonePotential m n - clonePotential m (n + 1)

/-- Finite exact telescoping; this part does not depend on an analytic identity. -/
theorem binary_coboundary_sum (F : ℕ → ℚ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (2 * F (k + 1) - F (k + 2)) / 2 ^ (k + 1)) =
      F 1 - F (N + 1) / 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [pow_succ]
    field_simp
    ring

theorem clone_partial_sum (m N : ℕ) :
    (∑ k ∈ Finset.range N, cloneKick m (k + 1) / 2 ^ (k + 1)) =
      clonePotential m 1 - clonePotential m (N + 1) / 2 ^ N :=
  binary_coboundary_sum (clonePotential m) N

/-- All-order rational controls, 99% confidence; analytic parts remain unproved.
The finite difference identity is Delta^m(1/n)=(-1)^m betaKick(m,n).
For every chosen order, the positive kick matches 1/n to that order but its
weighted sum is rational.  This does NOT refute an irrational-or-disjunctive
claim with exact rational-function hypotheses. -/
def FiniteJetRationalControls : Prop :=
  ∀ m : ℕ, 0 < m →
    clonePotential m 1 = alternatingHarmonic m ∧
    (∀ n : ℕ, 0 < n →
      cloneKick m n = 1 / (n : ℚ) - (-1 : ℚ) ^ m * betaKick m n ∧
      0 < cloneKick m n ∧
      |cloneKick m n - 1 / (n : ℚ)| ≤ (m.factorial : ℚ) / (n : ℚ) ^ (m + 1)) ∧
    HasSum (fun n : ℕ => (cloneKick m (n + 1) : ℝ) / 2 ^ (n + 1))
      (alternatingHarmonic m : ℝ)

theorem rational_clone_not_disjunctive (b m : ℕ) :
    ¬ IsDisjunctive b (alternatingHarmonic m : ℝ) := by
  intro h
  exact h.irrational ⟨alternatingHarmonic m, rfl⟩

/-- Reopening requires a visit estimate for the exact accelerated logarithm,
with the rational shifts and their denominator cost retained. -/
def AcceleratedWindowSupply : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 →
    ∃ m n : ℕ,
      orbit 2 ((alternatingHarmonic m : ℝ) + (-1 : ℝ) ^ m *
        ∑' k : ℕ, (betaKick m (k + 1) : ℝ) / 2 ^ (k + 1)) n ∈ Set.Ico a c

/-! ## 2. Integer combinations of logarithmic Pade forms -/

def padePair : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | 1 => (3, 2)
  | n + 2 =>
    let prev := padePair n
    let curr := padePair (n + 1)
    ((3 * (2 * (n + 1) + 1) * curr.1 - (n + 1) * prev.1) / (n + 2),
     (3 * (2 * (n + 1) + 1) * curr.2 - (n + 1) * prev.2) / (n + 2))

def DyadicSynthesis (n width : ℕ) : Prop :=
  ∃ (u : ℕ → ℤ) (m : ℕ) (z : ℤ),
    (∑ j ∈ Finset.range width, (u j : ℚ) * (padePair (n + j)).1) = 2 ^ m ∧
    (∑ j ∈ Finset.range width, (u j : ℚ) * (padePair (n + j)).2) = z

/-- Classical recurrence determinant; stated, not proved in this screen. -/
def PadeWronskian : Prop :=
  ∀ n : ℕ, (padePair n).1 * (padePair (n + 1)).2 -
    (padePair (n + 1)).1 * (padePair n).2 = 2 / (n + 1)

theorem pade_five_six_data :
    padePair 5 = (1683, 34997 / 30) ∧ padePair 6 = (8989, 62307 / 10) := by
  norm_num [padePair]

/-- A genuine denominator obstruction even though gcd(1683,8989)=1.
The premise says that the constant term of the combination is integral. -/
@[blueprint (title := "Adjacent logarithmic Pade forms can forbid every dyadic coefficient")]
theorem pade_five_six_no_dyadic (u v z : ℤ) (m : ℕ)
    (hB : 34997 * u + 186921 * v = 30 * z) :
    1683 * u + 8989 * v ≠ 2 ^ m := by
  intro hA
  have hd : (5 : ℤ) ∣ 2 ^ m := by
    refine ⟨24 * z - 27661 * u - 147739 * v, ?_⟩
    linear_combination 4 * hB - hA
  have hp : Prime (5 : ℤ) := by norm_num
  have := hp.dvd_of_dvd_pow hd
  norm_num at this

/-- The same construction is possible at the small positive-control pair. -/
theorem pade_dyadic_positive_control :
    (-4 : ℚ) * (padePair 1).1 + (padePair 2).1 = 1 ∧
    (-4 : ℚ) * (padePair 1).2 + (padePair 2).2 = 1 := by
  norm_num [padePair]

/-- The modular certificate used by the finite probe, for arbitrary windows.
The common-denominator-scaled constants are C; integral constant term means
sum u*C = D*z.  No coefficient-size restriction is used. -/
theorem no_dyadic_of_prime_certificate (s : Finset ℕ) (A C u : ℕ → ℤ)
    (p D c z : ℤ) (m : ℕ) (hp : Prime p) (hp2 : ¬ p ∣ 2)
    (hD : p ∣ D) (hC : ∀ j ∈ s, p ∣ A j - c * C j)
    (hz : ∑ j ∈ s, u j * C j = D * z) :
    (∑ j ∈ s, u j * A j) ≠ 2 ^ m := by
  intro heq
  have hd : p ∣ ∑ j ∈ s, u j * (A j - c * C j) :=
    Finset.dvd_sum (fun j hj => (hC j hj).mul_left (u j))
  have hid : (∑ j ∈ s, u j * (A j - c * C j)) =
      (∑ j ∈ s, u j * A j) - c * ∑ j ∈ s, u j * C j := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hid, hz, heq] at hd
  have hzdiv : p ∣ c * (D * z) := (hD.mul_right z).mul_left c
  have hpow : p ∣ 2 ^ m := by
    simpa only [sub_add_cancel] using hd.add hzdiv
  exact hp2 (hp.dvd_of_dvd_pow hpow)

/-- Finite exact modular-certificate probe; NOT an all-n obstruction theorem.
Widths count terms, so width two means the pair at n,n+1. -/
def PadeShortWindowProbe : Prop :=
  (∀ n ∈ Finset.Icc 3 79, ¬ DyadicSynthesis n 2) ∧
  (∀ n ∈ Finset.Icc 5 79, ¬ DyadicSynthesis n 3) ∧
  (∀ n ∈ Finset.Icc 11 79, ¬ DyadicSynthesis n 10)

/-- Complete finite grid, including the constructive positive controls. -/
def PadeGridProbe : Prop :=
  ∀ n ∈ Finset.Icc 1 79,
    (DyadicSynthesis n 2 ↔ n ∈ ([1, 2] : List ℕ)) ∧
    (DyadicSynthesis n 3 ↔ n ∈ ([1, 2, 4] : List ℕ)) ∧
    (DyadicSynthesis n 5 ↔ n ∈ ([1, 2, 3, 4, 6] : List ℕ)) ∧
    (DyadicSynthesis n 10 ↔ n ≤ 10)

/-- Actual integer witnesses were produced by the probe at these four windows.
This finite statement remains unproved in Lean. -/
def PadeWideWindowProbe : Prop :=
  ∀ n ∈ ([4, 8, 16, 32] : List ℕ), DyadicSynthesis n n

def padeErrorBudget (n width : ℕ) (u : ℕ → ℤ) : ℚ :=
  ∑ j ∈ Finset.range width, (|u j| : ℚ) / 5 ^ (n + j)

/-- The probe supplies witnesses to this finite existential claim.  Their
large budgets do not establish a lower bound for other possible witnesses. -/
def PadeWideBudgetProbe : Prop :=
  ∀ n ∈ ([4, 8, 16, 32] : List ℕ), ∃ (u : ℕ → ℤ) (z : ℤ),
    (∑ j ∈ Finset.range n, (u j : ℚ) * (padePair (n + j)).1) = 2 ∧
    (∑ j ∈ Finset.range n, (u j : ℚ) * (padePair (n + j)).2) = z ∧
    1 < padeErrorBudget n n u

/-- Classical integral enclosure, 99% confidence, not proved here.
The error is integral_0^1 (t(1-t)/(1+t))^n/(1+t) dt; its positive
integrand is at most (1/5)^n/(1+t). -/
def PadeErrorEnvelope : Prop :=
  ∀ n : ℕ, 0 < (padePair n).1 * Real.log 2 - (padePair n).2 ∧
    (padePair n).1 * Real.log 2 - (padePair n).2 ≤ 1 / (5 : ℝ) ^ n

/-- A concrete, weaker research test: arbitrarily cheap dyadic synthesis.
With PadeErrorEnvelope this would force arbitrarily close approaches to an
integer along the binary orbit.  It would not alone give all digit words.
Neither truth nor an efficient construction is asserted. -/
def PadeCheapDyadic : Prop :=
  ∀ k : ℕ, ∃ (n width m : ℕ) (u : ℕ → ℤ) (z : ℤ),
    (∑ j ∈ Finset.range width, (u j : ℚ) * (padePair (n + j)).1) = 2 ^ m ∧
    (∑ j ∈ Finset.range width, (u j : ℚ) * (padePair (n + j)).2) = z ∧
    padeErrorBudget n width u < 1 / (2 : ℚ) ^ k

/-- A useful synthesis needs small, word-targeted error as well as a dyadic
coefficient.  Feasibility of the two integer equations alone is insufficient.
No construction supplying these certificates uniformly in the interval is known. -/
def PadeWindowSupply : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 →
    ∃ (n width m : ℕ) (u : ℕ → ℤ) (z : ℤ),
      (∑ j ∈ Finset.range width, (u j : ℚ) * (padePair (n + j)).1) = 2 ^ m ∧
      (∑ j ∈ Finset.range width, (u j : ℚ) * (padePair (n + j)).2) = z ∧
      a < ∑ j ∈ Finset.range width,
        (u j : ℝ) * ((padePair (n + j)).1 * Real.log 2 - (padePair (n + j)).2) ∧
      (∑ j ∈ Finset.range width,
        (u j : ℝ) * ((padePair (n + j)).1 * Real.log 2 - (padePair (n + j)).2)) < c

/-! ## 3. Transfer from normal localized logarithms -/

/-- Normality survives arbitrary finite prefixes of zero. -/
theorem normal_tail_hidden (y : ℝ) (hy : IsNormal 2 y) (K : ℕ) :
    IsNormal 2 (y / (2 : ℝ) ^ K) := by
  have h := isNormal_rat_mul_add 2 (by norm_num) y (1 / (2 : ℚ) ^ K) 0
    (by positivity) hy
  simpa [Rat.cast_div, Rat.cast_pow, div_eq_mul_inv, mul_comm] using h

theorem normal_tail_bound (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (K : ℕ) :
    0 ≤ y / (2 : ℝ) ^ K ∧ y / (2 : ℝ) ^ K ≤ 1 / (2 : ℝ) ^ K := by
  constructor
  · positivity
  · exact div_le_div_of_nonneg_right hy1 (by positivity)

theorem zero_not_disjunctive : ¬ IsDisjunctive 2 (0 : ℝ) := by
  intro h
  exact h.irrational ⟨0, by norm_num⟩

noncomputable def localizedLog (P : ℕ) : ℝ :=
  GrowingLocalizedLog.zetaY (fun _ => P)

/-- Elementary tail estimate, 99% confidence, not proved here.  Every index
through P is retained; bound all the omitted terms by the Mercator tail. -/
def LocalizedShadow : Prop :=
  ∀ P : ℕ, 0 ≤ Real.log 2 - localizedLog P ∧
    Real.log 2 - localizedLog P ≤ 1 / (((P : ℝ) + 1) * 2 ^ P)

/-- Open quantitative crux: visitation must precede loss of shadow precision.
Normality for each fixed P gives visits without this coupling to P. -/
def LocalizedWindowSupply : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 →
    ∃ P n : ℕ,
      a + 2 ^ n / (((P : ℝ) + 1) * 2 ^ P) < orbit 2 (localizedLog P) n ∧
      orbit 2 (localizedLog P) n < c - 2 ^ n / (((P : ℝ) + 1) * 2 ^ P)

end NormalNumbers.LnTwoRoutes
