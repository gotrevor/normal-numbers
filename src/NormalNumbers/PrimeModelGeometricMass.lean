/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeModelFamilyGraded

/-!
# Astra §10: the geometric fresh-mass functional `F_N`

`ROUND2-multicutoff-astra.md` §10 isolates the *abstract* hypothesis behind the graded consumer:

    F_N = ∑_{j=1}^{J_N} 4^{−j} S_P(y_j, 2N) → 0.                                   (10.1)

`PENDING_WORK.md` records (10.1) as "strictly weaker than `SqrtFreshMassZero`".  This module
**proves the implication half of that claim on the schedule actually formalised**: Theorem C′'s
hypothesis forces (10.1) for the graded schedule `yG`/`JG`.  So nothing is lost by having proved
Theorem C′ first — the §10 consumer, if it is ever built, is a genuine generalisation and not a
different theorem.

The proof is the short root chain `recipSumIoc_yG_le` plus one observation: the geometric weight
absorbs the chain length.  At site `j` the chain costs `j + 2 + 2 log₂ u_N` halvings, so

    4^{−j} S_P(y_j, N) ≤ 4^{−j} (j + 2 + 2 log₂ u_N) / u_N² ≤ 2^{−j} (3 + 2 log₂ u_N) / u_N²

using `j ≤ 2^j`; summing the geometric series gives `2(3 + 2 log₂ u_N)/u_N² = O(1/u_N)`.  The
top piece `S_P(N, 2N) ≤ S_P(⌊√(2N)⌋, 2N)` is a *one-step* root chain, handled directly by `hS`.
-/

set_option linter.unusedSectionVars false

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.FamilyGraded

open NormalNumbers.PrimeLambert NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.Params NormalNumbers.PrimeModel.SqrtFresh
open NormalNumbers.PrimeModel.DensityMass NormalNumbers.PrimeModel.FamilyIter

variable (P : ℕ → Prop) [DecidablePred P]

/-- **Astra (10.1)** on the graded schedule: the geometrically weighted fresh mass. -/
noncomputable def geomFreshMass (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (JG P N), (1 / 4 : ℝ) ^ j * recipSumIoc P (yG P N j) (2 * N)

theorem geomFreshMass_nonneg (N : ℕ) : 0 ≤ geomFreshMass P N :=
  Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (recipSumIoc_nonneg P _ _)

/-- The doubling step is a one-step root chain: `⌊√(2N)⌋ ≤ N` always. -/
theorem sqrt_two_mul_le (N : ℕ) : Nat.sqrt (2 * N) ≤ N := by
  have h : Nat.sqrt (2 * N) < N + 1 := by
    rw [Nat.sqrt_lt']
    nlinarith [Nat.zero_le N]
  omega

theorem recipSumIoc_double_le (N : ℕ) :
    recipSumIoc P N (2 * N) ≤ recipSumIoc P (Nat.sqrt (2 * N)) (2 * N) :=
  recipSumIoc_mono_left P (sqrt_two_mul_le N)

/-- `j * 4^{-j} ≤ 2^{-j}`. -/
theorem nat_mul_quarter_pow_le (j : ℕ) : (j : ℝ) * (1 / 4 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ j := by
  have hj : (j : ℝ) ≤ (2 : ℝ) ^ j := by
    have h := Nat.lt_two_pow_self (n := j)
    have h2 : (j : ℝ) < (2 : ℝ) ^ j := by exact_mod_cast h
    exact h2.le
  have hsplit : (1 / 4 : ℝ) ^ j = (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j := by
    rw [← mul_pow]; norm_num
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have hcancel : (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j = 1 := by
    rw [← mul_pow]; norm_num
  calc (j : ℝ) * (1 / 4 : ℝ) ^ j
      = ((j : ℝ) * (1 / 2 : ℝ) ^ j) * (1 / 2 : ℝ) ^ j := by rw [hsplit]; ring
    _ ≤ ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j) * (1 / 2 : ℝ) ^ j := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hj hpos.le) hpos.le
    _ = (1 / 2 : ℝ) ^ j := by rw [hcancel]; ring

theorem sum_half_pow_Icc_le (J : ℕ) : ∑ j ∈ Finset.Icc 1 J, (1 / 2 : ℝ) ^ j ≤ 2 := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => by positivity))
    (sum_geometric_two_le (J + 1))
  intro j hj
  simp only [Finset.mem_Icc] at hj
  simp only [Finset.mem_range]
  omega

/-- **The quantitative form.**  `F_N ≤ 2(3 + 2 log₂ u_N)/u_N² + 2 S_P(⌊√(2N)⌋, 2N)`. -/
theorem geomFreshMass_le (hS : SqrtFreshMassZero P) : ∀ᶠ N : ℕ in atTop,
    geomFreshMass P N
      ≤ 2 * (3 + 2 * Real.log ((uG P N : ℕ) : ℝ) / Real.log 2) / ((uG P N : ℕ) : ℝ) ^ 2
        + 2 * recipSumIoc P (Nat.sqrt (2 * N)) (2 * N) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [recipSumIoc_yG_le P hS,
    (uG_tendsto P hS yBotG_tendsto).eventually_ge_atTop 1] with N hchain hu1
  set u : ℝ := ((uG P N : ℕ) : ℝ) with hudef
  have hu1r : (1 : ℝ) ≤ u := by rw [hudef]; exact_mod_cast hu1
  have hupos : (0 : ℝ) < u := by linarith
  set L : ℝ := Real.log u / Real.log 2 with hLdef
  have hLnn : 0 ≤ L := by
    rw [hLdef]
    exact div_nonneg (Real.log_nonneg hu1r) hlog2.le
  set δ : ℝ := recipSumIoc P (Nat.sqrt (2 * N)) (2 * N) with hδdef
  have hδnn : 0 ≤ δ := recipSumIoc_nonneg P _ _
  -- pointwise bound on each summand
  have hterm : ∀ j ∈ Finset.Icc 1 (JG P N),
      (1 / 4 : ℝ) ^ j * recipSumIoc P (yG P N j) (2 * N)
        ≤ (1 / 2 : ℝ) ^ j * ((3 + 2 * L) / u ^ 2 + δ) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hjJ1 : j ≤ J1 N := le_trans hj.2 (JG_le_J1 P N)
    have hsplit : recipSumIoc P (yG P N j) (2 * N)
        ≤ recipSumIoc P (yG P N j) N + recipSumIoc P N (2 * N) :=
      recipSumIoc_split_le P _ _ _
    have h1 : recipSumIoc P (yG P N j) N ≤ ((j : ℝ) + 2 + 2 * L) / u ^ 2 := by
      have := hchain j hjJ1
      simpa [hudef, hLdef, mul_div_assoc] using this
    have h2 : recipSumIoc P N (2 * N) ≤ δ := recipSumIoc_double_le P N
    have hS2 : recipSumIoc P (yG P N j) (2 * N) ≤ ((j : ℝ) + 2 + 2 * L) / u ^ 2 + δ := by
      linarith
    have hq : (0 : ℝ) < (1 / 4 : ℝ) ^ j := by positivity
    calc (1 / 4 : ℝ) ^ j * recipSumIoc P (yG P N j) (2 * N)
        ≤ (1 / 4 : ℝ) ^ j * (((j : ℝ) + 2 + 2 * L) / u ^ 2 + δ) :=
          mul_le_mul_of_nonneg_left hS2 hq.le
      _ = ((j : ℝ) * (1 / 4 : ℝ) ^ j) / u ^ 2
            + (1 / 4 : ℝ) ^ j * ((2 + 2 * L) / u ^ 2 + δ) := by ring
      _ ≤ ((1 / 2 : ℝ) ^ j) / u ^ 2
            + (1 / 2 : ℝ) ^ j * ((2 + 2 * L) / u ^ 2 + δ) := by
          have hA : ((j : ℝ) * (1 / 4 : ℝ) ^ j) / u ^ 2 ≤ ((1 / 2 : ℝ) ^ j) / u ^ 2 := by
            have h := nat_mul_quarter_pow_le j
            gcongr
          have hB : (1 / 4 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ j :=
            pow_le_pow_left₀ (by norm_num) (by norm_num) j
          have hBn : (0 : ℝ) ≤ (2 + 2 * L) / u ^ 2 + δ := by positivity
          have := mul_le_mul_of_nonneg_right hB hBn
          linarith
      _ = (1 / 2 : ℝ) ^ j * ((3 + 2 * L) / u ^ 2 + δ) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  have hnn : (0 : ℝ) ≤ (3 + 2 * L) / u ^ 2 + δ := by positivity
  have := mul_le_mul_of_nonneg_right (sum_half_pow_Icc_le (JG P N)) hnn
  calc (∑ j ∈ Finset.Icc 1 (JG P N), (1 / 2 : ℝ) ^ j) * ((3 + 2 * L) / u ^ 2 + δ)
      ≤ 2 * ((3 + 2 * L) / u ^ 2 + δ) := this
    _ = 2 * (3 + 2 * L) / u ^ 2 + 2 * δ := by ring
    _ = 2 * (3 + 2 * Real.log u / Real.log 2) / u ^ 2 + 2 * δ := by rw [hLdef]; ring
  
/-- The right-hand side of `geomFreshMass_le`, first summand, is `O(1/u_N)`. -/
theorem geomBound_le (u : ℝ) (hu : 1 ≤ u) :
    2 * (3 + 2 * Real.log u / Real.log 2) / u ^ 2 ≤ (6 + 4 / Real.log 2) / u := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hupos : (0 : ℝ) < u := by linarith
  have hlogu : Real.log u ≤ u := le_trans (Real.log_le_sub_one_of_pos hupos) (by linarith)
  have hlognn : 0 ≤ Real.log u := Real.log_nonneg hu
  have h1 : 2 * (3 + 2 * Real.log u / Real.log 2) ≤ (6 + 4 / Real.log 2) * u := by
    have hA : 4 * Real.log u / Real.log 2 ≤ 4 * u / Real.log 2 := by
      gcongr
    have hu6 : (6 : ℝ) ≤ 6 * u := by nlinarith
    have hfin : (6 + 4 / Real.log 2) * u = 6 * u + 4 * u / Real.log 2 := by
      field_simp
    rw [hfin]
    have : 2 * (3 + 2 * Real.log u / Real.log 2) = 6 + 4 * Real.log u / Real.log 2 := by ring
    rw [this]
    linarith
  calc 2 * (3 + 2 * Real.log u / Real.log 2) / u ^ 2
      ≤ ((6 + 4 / Real.log 2) * u) / u ^ 2 := by
        gcongr
    _ = (6 + 4 / Real.log 2) / u := by
        rw [pow_two, ← div_div, mul_div_assoc, div_self (ne_of_gt hupos), mul_one]

/-- **Theorem C′ implies Astra (10.1)** on the graded schedule. -/
theorem geomFreshMass_tendsto (hS : SqrtFreshMassZero P) :
    Tendsto (geomFreshMass P) atTop (𝓝 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdouble : Tendsto (fun N : ℕ => recipSumIoc P (Nat.sqrt (2 * N)) (2 * N)) atTop (𝓝 0) := by
    refine hS.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
  have hu : Tendsto (fun N : ℕ => ((uG P N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (uG_tendsto P hS yBotG_tendsto)
  have hinv : Tendsto (fun N : ℕ => (6 + 4 / Real.log 2) / ((uG P N : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa using (Filter.Tendsto.const_div_atTop hu (6 + 4 / Real.log 2))
  have hsum : Tendsto
      (fun N : ℕ => (6 + 4 / Real.log 2) / ((uG P N : ℕ) : ℝ)
        + 2 * recipSumIoc P (Nat.sqrt (2 * N)) (2 * N)) atTop (𝓝 0) := by
    simpa using hinv.add (hdouble.const_mul 2)
  refine squeeze_zero' (Eventually.of_forall fun N => geomFreshMass_nonneg P N) ?_ hsum
  filter_upwards [geomFreshMass_le P hS,
    (uG_tendsto P hS yBotG_tendsto).eventually_ge_atTop 1] with N hb hu1
  have hu1r : (1 : ℝ) ≤ ((uG P N : ℕ) : ℝ) := by exact_mod_cast hu1
  have := geomBound_le ((uG P N : ℕ) : ℝ) hu1r
  linarith

end NormalNumbers.PrimeModel.FamilyGraded
