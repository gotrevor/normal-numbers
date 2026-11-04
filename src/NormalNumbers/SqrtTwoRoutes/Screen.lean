/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import NormalNumbers.Disjunctive

/-!
# Screening arithmetic mechanisms for binary sqrt(2)

Read `../../../MAZE.md` and `docs/sqrt-two-routes/screen.md`.
These are scoped controls, not a refutation of disjunctivity or of all Pell,
carry, or sieve methods.  The definitions named `...Supply` are open inputs.
-/

namespace NormalNumbers.SqrtTwoRoutes

def pellPair : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => let a := pellPair n; (a.1 + 2 * a.2, a.1 + a.2)

def pellP (n : ℕ) : ℤ := (pellPair n).1
def pellQ (n : ℕ) : ℤ := (pellPair n).2

@[simp] theorem pellP_zero : pellP 0 = 1 := rfl
@[simp] theorem pellQ_zero : pellQ 0 = 0 := rfl
@[simp] theorem pellP_succ (n : ℕ) : pellP (n + 1) = pellP n + 2 * pellQ n := rfl
@[simp] theorem pellQ_succ (n : ℕ) : pellQ (n + 1) = pellP n + pellQ n := rfl

theorem pell_norm (n : ℕ) : pellP n ^ 2 - 2 * pellQ n ^ 2 = (-1) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih => simp only [pellP_succ, pellQ_succ, pow_succ]; nlinarith [ih]

theorem pell_det (n : ℕ) :
    pellP n * pellQ (n + 1) - pellP (n + 1) * pellQ n = (-1) ^ n := by
  simp only [pellP_succ, pellQ_succ]
  nlinarith [pell_norm n]

theorem pell_positive (n : ℕ) :
    0 < pellP n ∧ 0 ≤ pellQ n ∧ pellQ n ≤ pellP n := by
  induction n with
  | zero => norm_num
  | succ n ih => simp only [pellP_succ, pellQ_succ]; omega

theorem pell_denominator_growth (m : ℕ) : (2 : ℤ) ^ m ≤ pellQ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pellQ_succ (m + 1), pow_succ]
    have := pell_positive (m + 1)
    omega

def coeffU (n : ℕ) (P Q : ℤ) : ℤ :=
  (-1) ^ n * (P * pellQ (n + 1) - Q * pellP (n + 1))

def coeffV (n : ℕ) (P Q : ℤ) : ℤ :=
  (-1) ^ n * (Q * pellP n - P * pellQ n)

theorem unimodular_synthesis (p q r s d P Q : ℤ)
    (hd : d ^ 2 = 1) (hdet : p * s - r * q = d) :
    (d * (P * s - Q * r)) * p + (d * (Q * p - P * q)) * r = P ∧
    (d * (P * s - Q * r)) * q + (d * (Q * p - P * q)) * s = Q := by
  constructor
  · calc
      _ = (d * d) * P := by rw [← hdet]; ring
      _ = P := by rw [← pow_two, hd, one_mul]
  · calc
      _ = (d * d) * Q := by rw [← hdet]; ring
      _ = Q := by rw [← pow_two, hd, one_mul]

/-- Every integer numerator and denominator can be synthesized at EVERY
adjacent Pell pair.  Feasibility selects no dyadic positions. -/
@[blueprint (title := "Every integer target has an adjacent Pell certificate")]
theorem pell_synthesis (n : ℕ) (P Q : ℤ) :
    coeffU n P Q * pellP n + coeffV n P Q * pellP (n + 1) = P ∧
    coeffU n P Q * pellQ n + coeffV n P Q * pellQ (n + 1) = Q := by
  apply unimodular_synthesis _ _ _ _ _ _ _ _ (pell_det n)
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

noncomputable def pellError (n : ℕ) : ℝ := pellP n - Real.sqrt 2 * pellQ n

theorem pell_error_step (n : ℕ) :
    pellError (n + 1) = (1 - Real.sqrt 2) * pellError n := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [pellError, pellP_succ, pellQ_succ]
  push_cast
  linear_combination -(pellQ n : ℝ) * hs

theorem pell_errors_opposite (n : ℕ) : pellError n * pellError (n + 1) ≤ 0 := by
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  rw [pell_error_step]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sq_nonneg (pellError n))]

/-- A rational with denominator below q+s cannot lie strictly between
unimodular neighbors with nonnegative denominators q,s.  Here the same
fact is stated directly in the integer synthesis coordinates. -/
theorem small_denominator_opposite_coefficients (q s Q u v : ℤ)
    (hq : 0 ≤ q) (hs : 0 ≤ s) (hQ : 0 ≤ Q) (hsmall : Q < q + s)
    (hden : u * q + v * s = Q) : u * v ≤ 0 := by
  by_cases hu : 0 ≤ u
  · by_cases hv : v ≤ 0
    · exact mul_nonpos_of_nonneg_of_nonpos hu hv
    · by_cases hz : u = 0
      · simp [hz]
      · have hu1 : 1 ≤ u := by omega
        have hv1 : 1 ≤ v := by omega
        nlinarith [mul_nonneg (sub_nonneg.mpr hu1) hq,
          mul_nonneg (sub_nonneg.mpr hv1) hs]
  · by_cases hv : 0 ≤ v
    · exact mul_nonpos_of_nonpos_of_nonneg (by omega) hv
    · have hu1 : u ≤ -1 := by omega
      have hv1 : v ≤ -1 := by omega
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (show u + 1 ≤ 0 by omega) hq,
        mul_nonpos_of_nonpos_of_nonneg (show v + 1 ≤ 0 by omega) hs]

theorem abs_add_of_product_nonneg (a b : ℝ) (h : 0 ≤ a * b) :
    |a + b| = |a| + |b| := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (add_nonneg ha hb)]
    · have hz : a = 0 := by nlinarith
      simp [hz]
  · have hb : b ≤ 0 := by nlinarith
    rw [abs_of_nonpos (le_of_not_ge ha), abs_of_nonpos hb,
      abs_of_nonpos (add_nonpos (le_of_not_ge ha) hb)]
    ring

noncomputable def pellCost (n : ℕ) (P Q : ℤ) : ℝ :=
  |(coeffU n P Q : ℝ) * pellError n| +
    |(coeffV n P Q : ℝ) * pellError (n + 1)|

theorem pell_signed_error (n : ℕ) (P Q : ℤ) :
    (coeffU n P Q : ℝ) * pellError n + (coeffV n P Q : ℝ) * pellError (n + 1) =
      P - Q * Real.sqrt 2 := by
  have hp : (coeffU n P Q : ℝ) * pellP n + (coeffV n P Q : ℝ) * pellP (n + 1) = P :=
    by exact_mod_cast (pell_synthesis n P Q).1
  have hq : (coeffU n P Q : ℝ) * pellQ n + (coeffV n P Q : ℝ) * pellQ (n + 1) = Q :=
    by exact_mod_cast (pell_synthesis n P Q).2
  change (coeffU n P Q : ℝ) * ((pellP n : ℝ) - Real.sqrt 2 * pellQ n) +
    (coeffV n P Q : ℝ) * ((pellP (n + 1) : ℝ) - Real.sqrt 2 * pellQ (n + 1)) = _
  linear_combination hp - Real.sqrt 2 * hq

theorem pell_cost_lower (n : ℕ) (P Q : ℤ) :
    |(P : ℝ) - Q * Real.sqrt 2| ≤ pellCost n P Q := by
  rw [← pell_signed_error n P Q]
  exact abs_add_le _ _

/-- The cost becomes EXACT as soon as the adjacent denominator sum exceeds
the target denominator.  No digit assumption or limiting argument is used. -/
theorem pell_cost_exact (n : ℕ) (P Q : ℤ) (hQ : 0 ≤ Q)
    (hsmall : Q < pellQ n + pellQ (n + 1)) :
    pellCost n P Q = |(P : ℝ) - Q * Real.sqrt 2| := by
  have huv := small_denominator_opposite_coefficients _ _ Q (coeffU n P Q) (coeffV n P Q)
    (pell_positive n).2.1 (pell_positive (n + 1)).2.1 hQ hsmall (pell_synthesis n P Q).2
  have huvR : (coeffU n P Q : ℝ) * coeffV n P Q ≤ 0 := by exact_mod_cast huv
  have hprod : 0 ≤ ((coeffU n P Q : ℝ) * pellError n) *
      ((coeffV n P Q : ℝ) * pellError (n + 1)) := by
    simpa only [mul_mul_mul_comm] using
      mul_nonneg_of_nonpos_of_nonpos huvR (pell_errors_opposite n)
  rw [← pell_signed_error n P Q, abs_add_of_product_nonneg _ _ hprod]
  rfl

/-- At index m+1, the optimal absolute error budget for ANY numerator P
and denominator 2^m is exactly the target's own error. -/
@[blueprint (title := "Pell certificates attain the dyadic residual itself")]
theorem pell_dyadic_cost_exact (m : ℕ) (P : ℤ) :
    pellCost (m + 1) P (2 ^ m) = |(P : ℝ) - 2 ^ m * Real.sqrt 2| := by
  have h := pell_denominator_growth m
  have hp := pell_positive (m + 1)
  have hq : 0 < pellQ (m + 1 + 1) := by rw [pellQ_succ]; omega
  simpa using pell_cost_exact (m + 1) P (2 ^ m) (by positivity) (by omega)

/-- A cheap adjacent-Pell certificate exists iff the given dyadic
approximation is already that good.  This is a reformulation, not a
theorem prohibiting a future uniform construction of such certificates. -/
@[blueprint (title := "Cheap Pell synthesis is equivalent to the original dyadic approximation")]
theorem cheap_pell_iff (m : ℕ) (P : ℤ) (ε : ℝ) :
    (∃ n : ℕ, pellCost n P (2 ^ m) < ε) ↔
      |(P : ℝ) - 2 ^ m * Real.sqrt 2| < ε := by
  constructor
  · rintro ⟨n, hn⟩
    exact lt_of_le_of_lt (by simpa using pell_cost_lower n P (2 ^ m)) hn
  · intro h
    exact ⟨m + 1, by rwa [pell_dyadic_cost_exact]⟩

/-- Reopening needs a signed, word-targeted construction.  Raw feasibility
and absolute budget minimization alone are exhausted by the preceding
identities.  No mechanism establishing this input is presently supplied. -/
def PellWindowSupply : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 → ∃ (m n : ℕ) (P : ℤ),
    a < -((coeffU n P (2 ^ m) : ℝ) * pellError n +
      (coeffV n P (2 ^ m) : ℝ) * pellError (n + 1)) ∧
    -((coeffU n P (2 ^ m) : ℝ) * pellError n +
      (coeffV n P (2 ^ m) : ℝ) * pellError (n + 1)) < c

/-- Even the signed window formulation is exactly the original target.
This does not prohibit a productive proof through the formulation; it
locates the missing information in a uniform visit-producing argument. -/
@[blueprint (title := "Signed Pell window supply is equivalent to sqrt(2) disjunctivity")]
theorem pell_windowSupply_iff : PellWindowSupply ↔ IsDisjunctive 2 (Real.sqrt 2) := by
  simp only [PellWindowSupply, pell_signed_error, Int.cast_pow, Int.cast_ofNat]
  constructor
  · intro h a c ha hac hc
    obtain ⟨m, n, P, hlo, hhi⟩ := h a c ha hac hc
    have he : Int.fract (Real.sqrt 2 * 2 ^ m - (P : ℝ)) =
        Real.sqrt 2 * 2 ^ m - P := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [Int.fract_sub_intCast] at he
    refine ⟨m, ?_⟩
    change a ≤ Int.fract (Real.sqrt 2 * 2 ^ m) ∧ Int.fract (Real.sqrt 2 * 2 ^ m) < c
    rw [he]
    constructor <;> linarith
  · intro h a c ha hac hc
    obtain ⟨m, hm⟩ := h ((a + c) / 2) c (by linarith) (by linarith) hc
    change (a + c) / 2 ≤ Int.fract (Real.sqrt 2 * 2 ^ m) ∧
      Int.fract (Real.sqrt 2 * 2 ^ m) < c at hm
    rw [Int.fract] at hm
    refine ⟨m, m + 1, ⌊Real.sqrt 2 * 2 ^ m⌋, ?_, ?_⟩
    · linarith [hm.1]
    · linarith [hm.2]

/-! ## Finite residue/threshold abstractions of the square-root algorithm -/

/-- Choose a fake remainder on either side of the next-bit threshold,
while preserving the norm congruence at a fixed modulus. -/
def mockRemainder (M a T : ℤ) (bit : Bool) : ℤ :=
  if bit then a + M - (a ^ 2 + a - T) % M else M - (a ^ 2 - T) % M

@[blueprint (title := "A fixed-modulus square-root state allows either next bit")]
theorem mock_remainder (M a T : ℤ) (hM : 0 < M) (ha : M ≤ a) (bit : Bool) :
    1 ≤ mockRemainder M a T bit ∧ mockRemainder M a T bit ≤ 2 * a ∧
    Int.ModEq M (a ^ 2 + mockRemainder M a T bit) T ∧
    (bit = true ↔ a + 1 ≤ mockRemainder M a T bit) := by
  have ha0 : 0 < a := lt_of_lt_of_le hM ha
  cases bit
  · change 1 ≤ M - (a ^ 2 - T) % M ∧ M - (a ^ 2 - T) % M ≤ 2 * a ∧
      Int.ModEq M (a ^ 2 + (M - (a ^ 2 - T) % M)) T ∧
      (false = true ↔ a + 1 ≤ M - (a ^ 2 - T) % M)
    have h0 := Int.emod_nonneg (a ^ 2 - T) (ne_of_gt hM)
    have h1 := Int.emod_lt_of_pos (a ^ 2 - T) hM
    refine ⟨by omega, by omega, ?_, by simp; omega⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-((a ^ 2 - T) / M) - 1, ?_⟩
    have hh := Int.emod_add_ediv_mul (a ^ 2 - T) M
    nlinarith
  · change 1 ≤ a + M - (a ^ 2 + a - T) % M ∧
      a + M - (a ^ 2 + a - T) % M ≤ 2 * a ∧
      Int.ModEq M (a ^ 2 + (a + M - (a ^ 2 + a - T) % M)) T ∧
      (true = true ↔ a + 1 ≤ a + M - (a ^ 2 + a - T) % M)
    have h0 := Int.emod_nonneg (a ^ 2 + a - T) (ne_of_gt hM)
    have h1 := Int.emod_lt_of_pos (a ^ 2 + a - T) hM
    refine ⟨by omega, by omega, ?_, by simp; omega⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-((a ^ 2 + a - T) / M) - 1, ?_⟩
    have hh := Int.emod_add_ediv_mul (a ^ 2 + a - T) M
    nlinarith

/-- Exact arithmetic update.  Combined with independently chosen mock
states with the prescribed norm modulo M, it preserves the update modulo M,
but need not preserve the update as an equality of integers. -/
theorem remainder_update_identity (a r d : ℤ) (hd : d = 0 ∨ d = 1) :
    (2 * a + d) ^ 2 + (4 * r - 4 * a * d - d) = 4 * (a ^ 2 + r) := by
  rcases hd with rfl | rfl <;> ring

/-- Proved control explicitly limited to the mod-M abstraction. -/
theorem mock_update_congruent (M a r a' r' d T : ℤ)
    (h : Int.ModEq M (a ^ 2 + r) T) (h' : Int.ModEq M (a' ^ 2 + r') (4 * T))
    (ha' : a' = 2 * a + d) (hd : d = 0 ∨ d = 1) :
    Int.ModEq M r' (4 * r - 4 * a * d - d) := by
  have hstep := h.mul_left 4
  rw [← remainder_update_identity a r d hd, ← ha'] at hstep
  exact (h'.trans hstep.symm).add_left_cancel' (a' ^ 2)

def mockPrefix (A : ℤ) (bits : ℕ → Bool) : ℕ → ℤ
  | 0 => A
  | n + 1 => 2 * mockPrefix A bits n + (if bits n then 1 else 0)

theorem mock_prefix_large (M A : ℤ) (hM : 0 < M) (hA : M ≤ A)
    (bits : ℕ → Bool) (n : ℕ) : M ≤ mockPrefix A bits n := by
  induction n with
  | zero => exact hA
  | succ n ih => simp only [mockPrefix]; split <;> omega

/-- The deliberately weakened state model: the prefix update and next-bit
threshold are exact, but the remainder update is only a congruence. -/
def MockPath (M A T : ℤ) (bits : ℕ → Bool) : Prop :=
    ∃ a r : ℕ → ℤ,
      a 0 = A ∧
      (∀ n, a (n + 1) = 2 * a n + (if bits n then 1 else 0)) ∧
      (∀ n, 1 ≤ r n ∧ r n ≤ 2 * a n ∧
        Int.ModEq M (a n ^ 2 + r n) (T * 4 ^ n) ∧
        (bits n = true ↔ a n + 1 ≤ r n)) ∧
      (∀ n, Int.ModEq M (r (n + 1))
        (4 * r n - 4 * a n * (if bits n then 1 else 0) - (if bits n then 1 else 0)))

/-- ANY prescribed infinite bit stream satisfies the norm congruence,
the positivity bounds, the bit threshold, and the update modulo M.
This is not a path of the exact integer recurrence. -/
@[blueprint (title := "Fixed-modulus remainder dynamics admits every bit stream")]
theorem every_stream_has_mock_path (M A T : ℤ) (hM : 0 < M) (hA : M ≤ A)
    (bits : ℕ → Bool) : MockPath M A T bits := by
  let a := mockPrefix A bits
  let r := fun n => mockRemainder M (a n) (T * 4 ^ n) (bits n)
  have hstate (n : ℕ) := mock_remainder M (a n) (T * 4 ^ n) hM
    (mock_prefix_large M A hM hA bits n) (bits n)
  refine ⟨a, r, rfl, fun _ => rfl, hstate, ?_⟩
  intro n
  have ht : T * (4 : ℤ) ^ (n + 1) = 4 * (T * 4 ^ n) := by rw [pow_succ]; ring
  apply mock_update_congruent M (a n) (r n) (a (n + 1)) (r (n + 1))
    (if bits n then 1 else 0) (T * 4 ^ n) (hstate n).2.2.1
  · convert (hstate (n + 1)).2.2.1 using 1
    exact ht.symm
  · rfl
  · split <;> simp

/-- The proposed filter would reject at least one future bit stream at
some fixed modulus, once the prefix is at least the modulus. -/
def FiniteResidueExclusion : Prop :=
  ∃ M A T : ℤ, 0 < M ∧ M ≤ A ∧ ∃ bits : ℕ → Bool, ¬ MockPath M A T bits

theorem not_finiteResidueExclusion : ¬ FiniteResidueExclusion := by
  rintro ⟨M, A, T, hM, hA, bits, hno⟩
  exact hno (every_stream_has_mock_path M A T hM hA bits)

/-- A genuinely stronger carry input would exclude a word-avoiding path
for the EXACT integer recurrence from its true initial state.  This is a
necessary next target, not claimed to follow from the congruence controls. -/
def ExactRemainderWordSupply : Prop :=
  ∀ (a r : ℕ → ℤ) (d : ℕ → Bool), a 0 = 1 → r 0 = 1 →
    (∀ n, 1 ≤ r n ∧ r n ≤ 2 * a n) →
    (∀ n, d n = true ↔ a n + 1 ≤ r n) →
    (∀ n, a (n + 1) = 2 * a n + (if d n then 1 else 0)) →
    (∀ n, r (n + 1) = 4 * r n - 4 * a n * (if d n then 1 else 0) -
      (if d n then 1 else 0)) →
    ∀ w : List Bool, ∃ k, ∀ j (hj : j < w.length), d (k + j) = w[j]

/-! ## Norm splitting is automatic, not a filter on possible prefixes -/

/-- Over any field, a nonzero denominator turns the norm equation into
a square root of 2.  Applied in F_p for odd p and Q=2^n, this holds for
EVERY integer P whose norm is divisible by p, not just sqrt(2)'s prefix. -/
@[blueprint (title := "Quadratic-residue norm filters are automatic for every candidate numerator")]
theorem norm_root_automatic {K : Type*} [Field K] (P Q : K)
    (hQ : Q ≠ 0) (h : P ^ 2 - 2 * Q ^ 2 = 0) : (P / Q) ^ 2 = 2 := by
  rw [div_pow, div_eq_iff (pow_ne_zero _ hQ)]
  linear_combination h

/-- The exact arithmetic proposition the splitting-only filter tests.
Its truth is proved for every candidate numerator and invertible denominator. -/
def NormSplittingFilter {K : Type*} [Field K] (P Q : K) : Prop :=
  P ^ 2 - 2 * Q ^ 2 = 0 → ∃ t : K, t ^ 2 = 2

theorem every_candidate_passes_splitting {K : Type*} [Field K]
    (P Q : K) (hQ : Q ≠ 0) : NormSplittingFilter P Q := by
  intro h
  exact ⟨P / Q, norm_root_automatic P Q hQ h⟩

/-- A concrete favorable test of the Pell sign/cost mechanism; it does
not assert an infinite visitation property. -/
theorem pell_small_control :
    pellPair 1 = (1, 1) ∧ pellPair 2 = (3, 2) ∧
    coeffU 1 3 2 = 0 ∧ coeffV 1 3 2 = 1 := by
  norm_num [pellPair, coeffU, coeffV, pellP, pellQ]

/-- Both Pell coefficients participate; the exact budget is sqrt(2)-1. -/
theorem pell_mixed_control :
    coeffU 2 1 1 = -2 ∧ coeffV 2 1 1 = 1 ∧ pellCost 2 1 1 = Real.sqrt 2 - 1 := by
  refine ⟨by norm_num [coeffU, pellP, pellQ, pellPair],
    by norm_num [coeffV, pellP, pellQ, pellPair], ?_⟩
  rw [pell_cost_exact 2 1 1 (by norm_num) (by norm_num [pellP, pellQ, pellPair])]
  norm_num only [Int.cast_one, one_mul]
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  rw [abs_of_nonpos (by linarith)]
  ring

end NormalNumbers.SqrtTwoRoutes
