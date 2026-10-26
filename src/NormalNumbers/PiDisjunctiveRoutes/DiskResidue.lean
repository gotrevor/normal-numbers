/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.Disjunctive
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Route 3: integer disk residues

Route 3 of three experimental routes to disjunctivity of π.
See `NormalNumbers.PiDisjunctiveRoutes` for the shared framing and evidence tiers.
-/

namespace NormalNumbers.PiDisjunctiveRoutes

open Set

/-- Integer disk count, including the origin, axes, and boundary.
The positive quadrant is counted by integer square roots. -/
def diskCount (R : ℕ) : ℕ :=
  1 + 4 * R + 4 * ∑ j ∈ Finset.range R, Nat.sqrt (R ^ 2 - (j + 1) ^ 2)

/-- The real quadratic character modulo four, with integer values. -/
def chiFour (d : ℕ) : ℤ :=
  if d % 4 = 1 then 1 else if d % 4 = 3 then -1 else 0

/-- Classical sum-of-two-squares input, recorded as a hypothesis Prop.
Summing r₂(m) = 4 Σ_{d ∣ m} χ₄(d) for 1 ≤ m ≤ R² gives this identity.
This is an optional arithmetic handle on the disk-cover conjecture;
the geometric shadow and its conditional transfer do not assume it. -/
def DiskDivisorIdentity : Prop :=
  ∀ R : ℕ, (diskCount R : ℤ) =
    1 + 4 * ∑ d ∈ Finset.Icc 1 (R ^ 2), chiFour d * ((R ^ 2 / d : ℕ) : ℤ)

/-- Radius 4^n, modulus 8^n: area/modulus is 2^n π, while elementary
perimeter error/modulus tends to zero.  No sharp circle-problem bound is used. -/
def diskResidue (n : ℕ) : ℕ := diskCount (4 ^ n) % (8 ^ n)

noncomputable def diskPhase (n : ℕ) : ℝ :=
  (diskCount (4 ^ n) : ℝ) / (8 : ℝ) ^ n

open Real intervalIntegral in
/-- Quarter-disk area as an interval integral. -/
theorem integral_quarter_disk (R : ℝ) (hR : 0 < R) :
    ∫ x in (0:ℝ)..R, √(R ^ 2 - x ^ 2) = π * R ^ 2 / 4 := by
  have hc : Continuous fun x : ℝ => √(R ^ 2 - x ^ 2) := by fun_prop
  have hfull : ∫ x in (-R)..R, √(R ^ 2 - x ^ 2) = π * R ^ 2 / 2 := by
    have h1 := integral_comp_mul_left (a := -1) (b := 1) (fun x : ℝ => √(R ^ 2 - x ^ 2)) hR.ne'
    have h2 : ∫ x in (-1:ℝ)..1, √(R ^ 2 - (R * x) ^ 2) = R * (π / 2) := by
      rw [← integral_sqrt_one_sub_sq, ← intervalIntegral.integral_const_mul]
      congr 1; ext x
      rw [show R ^ 2 - (R * x) ^ 2 = R ^ 2 * (1 - x ^ 2) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq hR.le]
    simp only [mul_neg, mul_one] at h1
    rw [h2, smul_eq_mul] at h1
    rw [← mul_right_inj' (inv_ne_zero hR.ne'), ← h1]
    field_simp
  have hneg : ∫ x in (-R)..0, √(R ^ 2 - x ^ 2) = ∫ x in (0:ℝ)..R, √(R ^ 2 - x ^ 2) := by
    have := integral_comp_neg (a := 0) (b := R) (fun x : ℝ => √(R ^ 2 - x ^ 2))
    simp only [neg_sq, neg_zero] at this
    exact this.symm
  have hsplit := integral_add_adjacent_intervals (hc.intervalIntegrable (μ := MeasureTheory.volume) (-R) 0)
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 R)
  rw [hneg, hfull] at hsplit
  linarith

open Real in
/-- Elementary lattice count: integral comparison for the antitone quarter circle
plus the floor loss gives `|diskCount R - π R²| ≤ 5R`. -/
theorem diskCount_sub_area (R : ℕ) (hR : 1 ≤ R) :
    |(diskCount R : ℝ) - π * (R : ℝ) ^ 2| ≤ 5 * R := by
  set f : ℝ → ℝ := fun x => √((R : ℝ) ^ 2 - x ^ 2) with hf
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hanti : AntitoneOn f (Set.Icc 0 (0 + (R : ℝ))) := by
    intro x hx y hy hxy
    apply Real.sqrt_le_sqrt
    have := hx.1; nlinarith
  have hI := integral_quarter_disk (R : ℝ) hRpos
  have h1 := hanti.sum_le_integral
  have h2 := hanti.integral_le_sum
  simp only [zero_add] at h1 h2
  rw [hI] at h1 h2
  have hshift : ∑ i ∈ Finset.range R, f i =
      ∑ i ∈ Finset.range R, f ((i + 1 : ℕ) : ℝ) + R := by
    have a := Finset.sum_range_succ' (fun i : ℕ => f i) R
    have b := Finset.sum_range_succ (fun i : ℕ => f i) R
    have f0 : f ((0 : ℕ) : ℝ) = R := by simp [hf, Real.sqrt_sq hRpos.le]
    have fR : f (R : ℝ) = 0 := by simp [hf]
    rw [f0] at a; rw [fR] at b; linarith
  -- floors
  have hterm : ∀ j ∈ Finset.range R,
      ((Nat.sqrt (R ^ 2 - (j + 1) ^ 2) : ℕ) : ℝ) ≤ f ((j + 1 : ℕ) : ℝ) ∧
      f ((j + 1 : ℕ) : ℝ) < (Nat.sqrt (R ^ 2 - (j + 1) ^ 2) : ℝ) + 1 := by
    intro j hj
    have hj' : (j + 1) ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left (Finset.mem_range.1 hj) 2
    have hc : ((R ^ 2 - (j + 1) ^ 2 : ℕ) : ℝ) = (R : ℝ) ^ 2 - ((j + 1 : ℕ) : ℝ) ^ 2 := by
      push_cast [Nat.cast_sub hj']; ring
    simp only [hf, ← hc]
    exact ⟨Real.nat_sqrt_le_real_sqrt, Real.real_sqrt_lt_nat_sqrt_succ⟩
  have hF1 := Finset.sum_le_sum (fun j hj => (hterm j hj).1)
  have hF2 := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by omega))
    (fun j hj => (hterm j hj).2)
  rw [Finset.sum_add_distrib] at hF2
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hF2
  have hD : (diskCount R : ℝ) = 1 + 4 * R +
      4 * ∑ j ∈ Finset.range R, ((Nat.sqrt (R ^ 2 - (j + 1) ^ 2) : ℕ) : ℝ) := by
    simp [diskCount]
  have h1R : (1 : ℝ) ≤ R := by exact_mod_cast hR
  rw [abs_le]; constructor <;> linarith

/-- Frozen geometric bridge (proved; constant `C = 5`).
Unit lattice squares sandwich the disk between disks with radius R ± √2.
Thus |diskCount R - π R²| ≤ C R for R ≥ 1.  Set R = 4^n and divide by 8^n.
The oversampling is intentional: the trivial perimeter estimate suffices. -/
@[blueprint (title := "Oversampled integer disk counts shadow the binary orbit of π")]
theorem diskPhase_shadow :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      |diskPhase n - (2 : ℝ) ^ n * Real.pi| ≤ C / 2 ^ n := by
  refine ⟨5, by norm_num, fun n => ?_⟩
  have h := diskCount_sub_area (4 ^ n) (Nat.one_le_pow _ _ (by norm_num))
  have h8 : (0 : ℝ) < 8 ^ n := by positivity
  have e1 : diskPhase n - (2 : ℝ) ^ n * Real.pi =
      ((diskCount (4 ^ n) : ℝ) - Real.pi * ((4 ^ n : ℕ) : ℝ) ^ 2) / 8 ^ n := by
    rw [diskPhase]; push_cast
    rw [show ((4 : ℝ) ^ n) ^ 2 = 2 ^ n * 8 ^ n by
      simp only [show (8 : ℝ) = 2 * 2 * 2 by norm_num, show (4 : ℝ) = 2 * 2 by norm_num,
        mul_pow]; ring]
    field_simp
  have e2 : (5 : ℝ) / 2 ^ n = 5 * ((4 ^ n : ℕ) : ℝ) / 8 ^ n := by
    push_cast
    rw [show (8 : ℝ) ^ n = 2 ^ n * 4 ^ n by rw [← mul_pow]; norm_num]
    field_simp
  rw [e1, e2, abs_div, abs_of_pos h8]
  exact div_le_div_of_nonneg_right h h8.le

/-- Quantitative covering conjecture, entirely in natural-number arithmetic.
Every window [N,2N], once N ≥ C 4^k, hits the middle half of every k-bit
cylinder.  It asks for coverage, not uniform frequencies.
Confidence in truth: 85%, heuristic only, untested.  Square counts are a
negative control: their analogous phases tend to zero.  A proposed proof
must exploit the quadratic boundary, not just area plus perimeter error. -/
@[blueprint (title := "Low residues of expanding integer disks cover every binary cylinder")]
def DiskResidueCover : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, 0 < k → ∀ N : ℕ, C * 4 ^ k ≤ N →
    ∀ j : ℕ, j < 2 ^ k → ∃ n : ℕ, N ≤ n ∧ n ≤ 2 * N ∧
      (4 * j + 1) * 8 ^ n < 4 * 2 ^ k * diskResidue n ∧
      4 * 2 ^ k * diskResidue n < (4 * j + 3) * 8 ^ n

/-- Frozen transfer (proved).
The middle-half margin absorbs the vanishing diskPhase error.  Taking
arbitrarily large N gives arbitrarily late visits to every binary cylinder. -/
theorem pi_disjunctive_of_diskResidueCover (h : DiskResidueCover) :
    IsDisjunctive 2 Real.pi := by
  intro a c ha hac hc1
  obtain ⟨C, -, hC⟩ := h
  obtain ⟨C', -, hC'⟩ := diskPhase_shadow
  -- a dyadic cylinder of length 2^-k inside [a, c)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 / (c - a)) (by norm_num : (1 : ℝ) < 2)
  have hca : 0 < c - a := sub_pos.2 hac
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hk' : 2 ≤ (c - a) * 2 ^ k := by
    rw [div_lt_iff₀ hca] at hk; linarith
  set j : ℕ := ⌈a * 2 ^ k⌉₊ with hj
  have hj1 : a * 2 ^ k ≤ j := Nat.le_ceil _
  have hj2 : (j : ℝ) < a * 2 ^ k + 1 := Nat.ceil_lt_add_one (by positivity)
  have hjk : j < 2 ^ k := by
    have : (j : ℝ) < 2 ^ k := by nlinarith
    exact_mod_cast this
  -- a late enough window
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (4 * C' * 2 ^ k) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨n, hNn, -, hlo, hhi⟩ :=
    hC k (by rcases Nat.eq_zero_or_pos k with rfl | h <;> [simp at hk'; exact h] <;> linarith)
      (C * 4 ^ k + M) (by omega) j hjk
  refine ⟨n, ?_⟩
  have h8 : (0 : ℝ) < 8 ^ n := by positivity
  set t : ℝ := 2 ^ k with ht
  set u : ℝ := (diskResidue n : ℝ) / 8 ^ n with hu
  have hlo' : (4 * j + 1) / (4 * t) < u := by
    rw [div_lt_div_iff₀ (by positivity) h8]
    have : ((4 * j + 1) * 8 ^ n : ℝ) < 4 * 2 ^ k * diskResidue n := by exact_mod_cast hlo
    rw [← ht] at this; linarith
  have hhi' : u < (4 * j + 3) / (4 * t) := by
    rw [div_lt_div_iff₀ h8 (by positivity)]
    have : (4 * 2 ^ k * diskResidue n : ℝ) < (4 * j + 3) * 8 ^ n := by exact_mod_cast hhi
    rw [← ht] at this; linarith
  -- integer part of the disk phase
  set q : ℕ := diskCount (4 ^ n) / 8 ^ n
  have hdec : diskPhase n = q + u := by
    have := Nat.div_add_mod (diskCount (4 ^ n)) (8 ^ n)
    have hcast : (diskCount (4 ^ n) : ℝ) = (8 : ℝ) ^ n * q + (diskResidue n : ℕ) := by
      rw [diskResidue]; exact_mod_cast this.symm
    rw [diskPhase, hu, hcast]; field_simp
  -- the shadow error is below a quarter cylinder
  have hδ : C' / 2 ^ n < 1 / (4 * t) := by
    have hMn : (2 : ℝ) ^ M ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hs := hC' n
  rw [hdec, abs_le] at hs
  have hy : Real.pi * (2 : ℝ) ^ n - q ∈ Set.Ico a c := by
    have e1 : (4 * (j : ℝ) + 1) / (4 * t) - 1 / (4 * t) = j / t := by field_simp; ring
    have e2 : (4 * (j : ℝ) + 3) / (4 * t) + 1 / (4 * t) = (j + 1) / t := by field_simp; ring
    have ha' : a ≤ j / t := by rw [le_div_iff₀ h2k]; exact hj1
    have hc' : (j + 1) / t ≤ c := by rw [div_le_iff₀ h2k]; linarith
    constructor <;> linarith
  have hfr : Int.fract (Real.pi * (2 : ℝ) ^ n) = Real.pi * (2 : ℝ) ^ n - q := by
    rw [Int.fract_eq_iff]
    exact ⟨by linarith [hy.1], by linarith [hy.2], q, by push_cast; ring⟩
  show Int.fract (Real.pi * ((2 : ℕ) : ℝ) ^ n) ∈ Set.Ico a c
  push_cast; rw [hfr]; exact hy

/-- The disk convention is tested on a hand-countable known answer. -/
example : diskCount 1 = 5 := by decide +kernel
example : diskCount 2 = 13 := by decide +kernel
example : diskCount 4 = 49 := by decide +kernel
example : (diskCount 4 : ℤ) =
    1 + 4 * ∑ d ∈ Finset.Icc 1 16, chiFour d * ((16 / d : ℕ) : ℤ) := by
  decide +kernel

end NormalNumbers.PiDisjunctiveRoutes
