/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.ReservoirComparisonRobustness

/-!
# The genuine residual denominator: approximation versus exact rigidity

The denominator budget here is the actual REDUCED denominator of the BBP
residual, not a generic exponential upper bound or an enlarged lcm.
Rounding on this grid still gives rational-target comparisons, with head
error < 1/D_n and forcing error < 1/D_{n+1}+16/D_n.
Below the reciprocal lcm of two consecutive budgets, a forcing defect must
instead vanish exactly.  With the genuine initial value this is rigidity,
not a disjunctivity theorem.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.CutoffSix

def rationalResidual (s n : ℕ) : ℚ := bbpRationalHead n - rationalReservoir s n

def residualDenominator (s n : ℕ) : ℕ := (rationalResidual s n).den

theorem residualDenominator_pos (s n : ℕ) : 0 < residualDenominator s n :=
  Rat.pos _

theorem rationalResidual_cast (s n : ℕ) :
    (rationalResidual s n : ℝ) = residualS s n := by
  simp only [rationalResidual, Rat.cast_sub, bbpRationalHead_cast,
    rationalReservoir_cast, residualS]

theorem rationalResidual_zero (s : ℕ) : rationalResidual s 0 = 0 := by
  simp [rationalResidual, bbpRationalHead, rationalReservoir]

theorem fraction_den_dvd (a : ℤ) (D : ℕ) : ((a : ℚ) / D).den ∣ D := by
  have h := Rat.den_dvd a (D : ℤ)
  rw [Rat.divInt_eq_div] at h
  exact_mod_cast h

/-- Floor rounding uses no denominator outside the prescribed budget. -/
theorem exists_fixed_denominator_close (D : ℕ) (hD : 0 < D) (y : ℝ) :
    ∃ q : ℚ, q.den ∣ D ∧ |(q : ℝ) - y| < 1 / (D : ℝ) := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  refine ⟨(⌊y * D⌋ : ℚ) / D, fraction_den_dvd _ _, ?_⟩
  push_cast
  have hlo : (⌊y * D⌋ : ℝ) / D ≤ y :=
    (div_le_iff₀ hd).mpr (Int.floor_le _)
  have hhi : y - (1 / (D : ℝ)) < (⌊y * D⌋ : ℝ) / D := by
    apply (lt_div_iff₀ hd).mpr
    have := Int.lt_floor_add_one (y * D)
    have he : (1 / (D : ℝ)) * D = 1 := by field_simp
    nlinarith
  rw [abs_sub_lt_iff]
  constructor <;> linarith [show (0 : ℝ) < 1 / (D : ℝ) by positivity]

/-- A nonzero rational with denominator dividing D has magnitude at least 1/D. -/
theorem rat_eq_zero_of_denominator_small (q : ℚ) (D : ℕ) (hD : 0 < D)
    (hden : q.den ∣ D) (hsmall : |(q : ℝ)| < 1 / (D : ℝ)) : q = 0 := by
  by_contra hq
  have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hnum : (1 : ℝ) ≤ |(q.num : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hqd : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hle : (q.den : ℝ) ≤ D := by exact_mod_cast Nat.le_of_dvd hD hden
  have he : (q : ℝ) = (q.num : ℝ) / q.den := by
    exact_mod_cast (Rat.num_div_den q).symm
  rw [he, abs_div, abs_of_pos hqd] at hsmall
  have hLower : (1 : ℝ) / D ≤ |(q.num : ℝ)| / q.den := by
    rw [div_le_div_iff₀ hDr hqd]
    nlinarith
  linarith

/-- Denominator-preserving residuals cannot cancel a reservoir pole at any
prime absent from the genuine residual denominator. -/
theorem denominator_preserving_pole (R S : ℚ) (D p : ℕ) [Fact p.Prime]
    (hS : S.den ∣ D) (hpD : ¬ p ∣ D) (hR : 1 < padicNorm p R) :
    padicNorm p (R+S) = padicNorm p R := by
  have hInt := padicNorm_le_one_of_not_dvd_den S (fun h => hpD (dvd_trans h hS))
  rw [padicNorm.add_eq_max_of_ne (by linarith), max_eq_left (by linarith)]

@[blueprint (title := "The actual reduced residual denominators admit rational-target models at the grid scale")]
theorem rational_comparison_actual_denominators (s N : ℕ) :
    ∃ q : ℚ, ∃ S : ℕ → ℚ,
      (¬ IsDisjunctive 16 (q : ℝ)) ∧
      (∀ n ≤ N, S n = rationalResidual s n) ∧
      (∀ n, (S n).den ∣ residualDenominator s n) ∧
      (∀ n, |((rationalReservoir s n + S n : ℚ) : ℝ) - comparisonHead q n| <
        1 / (residualDenominator s n : ℝ)) ∧
      (∀ n, |(((rationalReservoir s (n+1) + S (n+1) : ℚ) : ℝ) -
        16 * ((rationalReservoir s n + S n : ℚ) : ℝ)) - 16 * bbpKick n| <
        1 / (residualDenominator s (n+1) : ℝ) + 16 / (residualDenominator s n : ℝ)) := by
  classical
  let ε : ℕ → ℝ := fun n => 1 / (residualDenominator s n : ℝ)
  have hε : ∀ n, 0 < ε n := by
    intro n
    exact div_pos (by norm_num) (by exact_mod_cast residualDenominator_pos s n)
  obtain ⟨q, hq⟩ := exists_rational_target_for_prefix ε hε N
  have hClose : ∀ n, ∃ a : ℚ, a.den ∣ residualDenominator s n ∧
      |(a : ℝ) - (comparisonHead q n - (rationalReservoir s n : ℝ))| < ε n :=
    fun n => exists_fixed_denominator_close _ (residualDenominator_pos s n) _
  choose A hAden hAclose using hClose
  let S : ℕ → ℚ := fun n => if n ≤ N then rationalResidual s n else A n
  have hPrefix : ∀ n ≤ N, S n = rationalResidual s n := fun n hn => by simp [S, hn]
  have hShadow : ∀ n, |((rationalReservoir s n + S n : ℚ) : ℝ) - comparisonHead q n| < ε n := by
    intro n
    by_cases hn : n ≤ N
    · rw [hPrefix n hn]
      simpa [rationalResidual] using hq n hn
    · simp only [S, if_neg hn, Rat.cast_add]
      convert hAclose n using 1
      congr 1
      ring
  refine ⟨q, S, (fun h => h.irrational ⟨q, rfl⟩), hPrefix, ?_, hShadow, ?_⟩
  · intro n
    by_cases hn : n ≤ N
    · simp [S, hn, residualDenominator]
    · simpa [S, hn] using hAden n
  · intro n
    have h := forcing_defect_bound
      (fun n => ((rationalReservoir s n + S n : ℚ) : ℝ)) (comparisonHead q) ε hShadow n
    simpa only [comparisonHead_succ, ε, mul_one_div] using h

/-- The denominator of the recurrence defect divides this lcm, not a product
of four independently bounded denominators. -/
theorem recurrence_defect_den_dvd (S T : ℕ → ℚ) (D : ℕ → ℕ)
    (hS : ∀ n, (S n).den ∣ D n) (hT : ∀ n, (T n).den ∣ D n) (n : ℕ) :
    ((S (n+1)-T (n+1)) - 16*(S n-T n)).den ∣ Nat.lcm (D (n+1)) (D n) := by
  have hd : ∀ k, (S k-T k).den ∣ D k := fun k =>
    (Rat.sub_den_dvd_lcm _ _).trans (Nat.lcm_dvd (hS k) (hT k))
  have hm : (16*(S n-T n)).den ∣ D n := by
    exact (Rat.mul_den_dvd _ _).trans (by simpa using hd n)
  exact (Rat.sub_den_dvd_lcm _ _).trans
    (Nat.lcm_dvd ((hd (n+1)).trans (Nat.dvd_lcm_left _ _))
      (hm.trans (Nat.dvd_lcm_right _ _)))

@[blueprint (title := "Below the reciprocal-lcm threshold, denominator-controlled recurrence errors vanish exactly")]
theorem denominator_recurrence_rigid (S T : ℕ → ℚ) (D : ℕ → ℕ)
    (hD : ∀ n, 0 < D n) (hS : ∀ n, (S n).den ∣ D n)
    (hT : ∀ n, (T n).den ∣ D n) (h0 : S 0 = T 0)
    (hError : ∀ n, |(((S (n+1)-T (n+1)) - 16*(S n-T n) : ℚ) : ℝ)| <
      1 / (Nat.lcm (D (n+1)) (D n) : ℝ)) : S = T := by
  have hRec : ∀ n, (S (n+1)-T (n+1)) - 16*(S n-T n) = 0 := by
    intro n
    exact rat_eq_zero_of_denominator_small _ _
      (Nat.lcm_pos (hD (n+1)) (hD n)) (recurrence_defect_den_dvd S T D hS hT n) (hError n)
  funext n
  induction n with
  | zero => exact h0
  | succ n ih => have := hRec n; rw [ih] at this; linarith

/-- The genuine rational head has precisely the original BBP forcing. -/
theorem genuine_head_forcing (n : ℕ) :
    (bbpRationalHead (n+1) : ℝ) - 16*(bbpRationalHead n : ℝ) = 16*bbpKick n := by
  have he : ∀ k, (bbpRationalHead k : ℝ) = comparisonHead Real.pi k := by
    intro k
    rw [bbpRationalHead_cast, comparisonHead, piTail]
    ring
  rw [he, he]
  exact comparisonHead_succ _ _

noncomputable def headForcingDefect (s : ℕ) (S : ℕ → ℚ) (n : ℕ) : ℝ :=
  ((rationalReservoir s (n+1) + S (n+1) : ℚ) : ℝ) -
    16*((rationalReservoir s n + S n : ℚ) : ℝ) - 16*bbpKick n

theorem headForcingDefect_eq (s : ℕ) (S : ℕ → ℚ) (n : ℕ) :
    headForcingDefect s S n =
      (((S (n+1)-rationalResidual s (n+1)) - 16*(S n-rationalResidual s n) : ℚ) : ℝ) := by
  unfold headForcingDefect rationalResidual
  push_cast
  linear_combination genuine_head_forcing n

theorem genuine_residual_forcing (s n : ℕ) : headForcingDefect s (rationalResidual s) n = 0 := by
  rw [headForcingDefect_eq]
  simp

@[blueprint (title := "Genuine BBP denominator budgets and sub-lattice forcing error recover the exact residual")]
theorem actual_denominator_rigidity (s : ℕ) (S : ℕ → ℚ) (h0 : S 0 = 0)
    (hden : ∀ n, (S n).den ∣ residualDenominator s n)
    (hError : ∀ n, |headForcingDefect s S n| <
      1 / (Nat.lcm (residualDenominator s (n+1)) (residualDenominator s n) : ℝ)) :
    S = rationalResidual s := by
  apply denominator_recurrence_rigid S (rationalResidual s) (residualDenominator s)
    (residualDenominator_pos s) hden (fun _ => dvd_refl _)
    (by simpa only [rationalResidual_zero] using h0)
  intro n
  simpa only [headForcingDefect_eq] using hError n

theorem bounded_head_error_identifies_target (x : ℝ)
    (h : ∀ n, |(bbpRationalHead n : ℝ) - comparisonHead x n| < 1) : x = Real.pi := by
  by_contra hx
  have hd : 0 < |Real.pi - x| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hx))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hd (by norm_num : (1/16 : ℝ) < 1)
  have hp : (0 : ℝ) < 16^n := by positivity
  have he : (bbpRationalHead n : ℝ) - comparisonHead x n = 16^n*(Real.pi-x) := by
    rw [bbpRationalHead_cast, comparisonHead, piTail]
    ring
  have hSmall := h n
  rw [he, abs_mul, abs_of_pos hp] at hSmall
  have hLarge : (1 : ℝ) < |Real.pi-x| * 16^n := by
    apply (div_lt_iff₀ hp).mp
    simpa only [div_pow, one_pow] using hn
  nlinarith

/-- An approximate head/residual model with the exact reduced denominator budgets. -/
structure DenominatorControlledModel (s : ℕ) (η : ℕ → ℝ) (x : ℝ) (S : ℕ → ℚ) : Prop where
  initial : S 0 = 0
  denominators : ∀ n, (S n).den ∣ residualDenominator s n
  shadow : ∀ n, |((rationalReservoir s n + S n : ℚ) : ℝ) - comparisonHead x n| < η n
  forcing : ∀ n, |headForcingDefect s S n| < η n

/-- Proposed sufficient criterion with some positive tolerance at every index.
The following theorem proves that this criterion is equivalent to the original
pi disjunctivity target.  Choosing a tolerance below the lattice spacing merely
recovers the exact BBP sequence; it supplies no digit-distribution argument. -/
def DenominatorCouplingCriterion (s : ℕ) : Prop :=
  ∃ η : ℕ → ℝ, (∀ n, 0 < η n) ∧
    ∀ x : ℝ, ∀ S : ℕ → ℚ, DenominatorControlledModel s η x S → IsDisjunctive 16 x

@[blueprint (title := "The denominator-controlled approximate-coupling criterion is equivalent to pi disjunctivity")]
theorem denominatorCouplingCriterion_iff (s : ℕ) :
    DenominatorCouplingCriterion s ↔ IsDisjunctive 16 Real.pi := by
  constructor
  · rintro ⟨η, hη, h⟩
    apply h Real.pi (rationalResidual s)
    refine ⟨rationalResidual_zero s, fun _ => dvd_refl _, ?_, ?_⟩
    · intro n
      have he : ((rationalReservoir s n + rationalResidual s n : ℚ) : ℝ) -
          comparisonHead Real.pi n = 0 := by
        simp only [rationalResidual, add_sub_cancel]
        rw [bbpRationalHead_cast, comparisonHead, piTail]
        ring
      simpa only [he, abs_zero] using hη n
    · intro n
      simpa only [genuine_residual_forcing, abs_zero] using hη n
  · intro hpi
    let L : ℕ → ℕ := fun n => Nat.lcm (residualDenominator s (n+1)) (residualDenominator s n)
    have hL : ∀ n, (0 : ℝ) < L n := by
      intro n
      exact_mod_cast Nat.lcm_pos (residualDenominator_pos s (n+1)) (residualDenominator_pos s n)
    let η : ℕ → ℝ := fun n => min 1 (1 / (L n : ℝ))
    refine ⟨η, (fun n => lt_min (by norm_num) (div_pos (by norm_num) (hL n))), ?_⟩
    intro x S hModel
    have hRigid : S = rationalResidual s := actual_denominator_rigidity s S
      hModel.initial hModel.denominators (fun n => lt_of_lt_of_le (hModel.forcing n) (min_le_right _ _))
    have hx : x = Real.pi := by
      apply bounded_head_error_identifies_target
      intro n
      have h := hModel.shadow n
      rw [hRigid] at h
      have he : rationalReservoir s n + rationalResidual s n = bbpRationalHead n := by
        unfold rationalResidual
        ring
      rw [he] at h
      exact lt_of_lt_of_le h (min_le_left _ _)
    simpa only [hx] using hpi

end NormalNumbers.PiDisjunctiveRoutes.CutoffSix
