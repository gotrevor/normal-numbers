/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4ScheduleWitness
import NormalNumbers.G4ScheduleB
import NormalNumbers.G4ScheduleBig
import NormalNumbers.G4ScheduleBudget
import NormalNumbers.G4ScheduleFar

/-!
# G4 disjunctivity, §5 assembly: the schedule witness, and the headline

For every omitted base-four cylinder `[w/4^ℓ, (w+1)/4^ℓ)` with `ℓ ≥ 1` we build one
`ScheduleWitness ℓ w` from the explicit schedule in `K`:

    k₄ = 8464·ℓ²·16^ℓ,  K = 4k₄,  M = 4232·ℓ·16^ℓ   (so 2ℓM = k₄ and 8ℓM = K)
    G = gridOf K (N K),  X = Sched.X K,  η = 2^{−k₄},  ε = 1/K,  D = Dj K k₄
    R = Sched.R K, Y = Sched.Y K, Mc = Sched.Mc K, lam' = e, lam = 13/2, δ's = 1/8.

The five inequalities are `gridParams_hB`, `Sched.hbig_holds`, `Sched.hfar_holds`,
`Sched.hbudget_holds` and `log_det_one_add_tensorGram_le'`; everything else is bookkeeping.
The empty word `ℓ = 0` is the cylinder `[0,1)`, which every orbit point hits, so no witness
is needed there.

The result is the unconditional headline `isDisjunctive_four` and its binary corollary
`isDisjunctive_two`.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

open PrimeLambert GridParams Sched

namespace Sched

/-- `k₄ = 8464·ℓ²·16^ℓ`. -/
def k₄ℓ (ℓ : ℕ) : ℕ := 8464 * ℓ ^ 2 * 16 ^ ℓ
/-- `K = 4k₄`. -/
def Kℓ (ℓ : ℕ) : ℕ := 4 * k₄ℓ ℓ
/-- `M = 4232·ℓ·16^ℓ`, so that `2ℓM = k₄`. -/
def Mℓ (ℓ : ℕ) : ℕ := 4232 * ℓ * 16 ^ ℓ

lemma two_mul_Mℓ (ℓ : ℕ) : 2 * ℓ * Mℓ ℓ = k₄ℓ ℓ := by unfold Mℓ k₄ℓ; ring

lemma Kℓ_eq (ℓ : ℕ) : Kℓ ℓ = 4 * k₄ℓ ℓ := rfl

lemma Kℓ_ge (ℓ : ℕ) : 33856 * ℓ ^ 2 * 16 ^ ℓ ≤ Kℓ ℓ := by
  unfold Kℓ k₄ℓ; nlinarith

lemma Kℓ_ge_100 {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 100 ≤ Kℓ ℓ := by
  have h := Kℓ_ge ℓ
  have h16 : 16 ≤ 16 ^ ℓ := by
    calc 16 = 16 ^ 1 := by norm_num
      _ ≤ 16 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  nlinarith

lemma R_le_Y (K : ℕ) : R K ≤ Y K :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (m₁_le_m K))

/-- `2^K · D ≤ 4^{N−1}`, the `hN` side condition. -/
lemma two_pow_mul_Dj_le {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) :
    2 ^ K * Dj K k₄ ≤ 4 ^ (N K - 1) := by
  have hk : 25 ≤ k₄ := by omega
  have h1 := two_Dj_add_one_le hK4 hk
  have h2 : 2 ^ K * Dj K k₄ ≤ 4 ^ K * 4 ^ K := by
    have : 2 ^ K ≤ 4 ^ K := Nat.pow_le_pow_left (by norm_num) K
    exact Nat.mul_le_mul this (by omega)
  rw [← pow_add] at h2
  refine h2.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold N
  have : K + K ≤ K * K := by nlinarith
  have : K * K ≤ 100 * K ^ 2 - 1 := by
    have : 100 * K ^ 2 = 100 * (K * K) := by ring
    omega
  omega

end Sched

/-- **The schedule witness** for every omitted cylinder of depth `ℓ ≥ 1`. -/
noncomputable def scheduleWitness (ℓ w : ℕ) (hℓ : 1 ≤ ℓ) : ScheduleWitness ℓ w :=
  let k₄ := k₄ℓ ℓ
  let K := Kℓ ℓ
  have hK4 : K = 4 * k₄ := rfl
  have hK100 : 100 ≤ K := Kℓ_ge_100 hℓ
  have hK1 : 1 ≤ K := by omega
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK100
  have hk₄K : k₄ ≤ K := by omega
  { G := gridOf K (N K) hK1
    hK := by show 0 < K; omega
    hr := Nat.one_le_pow _ _ (by show 0 < K ^ 2; positivity)
    X := X K
    hne := sample_nonempty hK100
    η := (1 / 2 : ℝ) ^ k₄
    hη := by positivity
    ε := 1 / (K : ℝ)
    hε := by positivity
    hε1 := by rw [div_lt_one (by linarith)]; linarith
    M := Mℓ ℓ
    hM := by
      have h : ((4 : ℝ) ^ ℓ) ^ Mℓ ℓ = 2 ^ k₄ := by
        rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        congr 1
        show 2 * (ℓ * Mℓ ℓ) = k₄ℓ ℓ
        rw [← two_mul_Mℓ ℓ]; ring
      rw [h, one_div_pow]
    Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)
    hlog := by
      have h := log_det_one_add_tensorGram_le' hK1
      push_cast
      exact h
    δ₁ := 1 / 8
    hδ₁ := by norm_num
    hB := by
      refine gridParams_hB (G := gridOf K (N K) hK1) (ℓ := ℓ) (M := Mℓ ℓ) rfl hℓ (Kℓ_ge ℓ)
        ?_ ?_ (by positivity) ?_ le_rfl
      · show K ≤ 8 * ℓ * Mℓ ℓ
        have := two_mul_Mℓ ℓ
        rw [hK4]; nlinarith
      · show 8 * ℓ * Mℓ ℓ ≤ K + 8 * ℓ
        have := two_mul_Mℓ ℓ
        rw [hK4]; nlinarith
      · show ((1 / 2 : ℝ) ^ k₄) ^ 4 ≤ (1 / 2 : ℝ) ^ K
        rw [← pow_mul, hK4, mul_comm]
    R := R K
    hR := R_ge_two K
    Y := Y K
    hRY := R_le_Y K
    D := Dj K k₄
    hN := by
      show 1 + Nat.clog 4 (2 ^ K * Dj K k₄) ≤ N K
      have h := (Nat.clog_le_iff_le_pow (by norm_num)).2 (two_pow_mul_Dj_le hK4 hK100)
      have hN : 1 ≤ N K := N_pos hK1
      omega
    Mc := Mc K
    hMc := Mc_pos hK1
    lam' := Real.exp 1
    hlam' := Real.one_le_exp zero_le_one
    lam := 13 / 2
    hlam := by norm_num
    Mx := ((X K + J K * gridDm K (N K) : ℕ) : ℝ)
    hMx1 := by
      have : 1 ≤ X K := Nat.one_le_two_pow
      exact_mod_cast le_add_right this
    hMx := fun n hn i => by exact_mod_cast gridOf.add_shiftAL_le hK1 hn i
    Dm := gridDm K (N K)
    hDm := gridOf.d_le hK1
    δbig := 1 / 8
    δfar := 1 / 8
    hbig := hbig_holds hK4 hK100
    hfar := by
      refine (hfar_holds hK100).trans ?_
      have : (1 / 2 : ℝ) ^ K ≤ (1 / 2 : ℝ) ^ k₄ :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hk₄K
      have hKpos : (0 : ℝ) < K := by linarith
      gcongr
    hbudget := by
      have h := hbudget_holds hK4 hK100
      have hc : Fintype.card (gridOf K (N K) hK1).Idx = T K := gridOf.card_Idx hK1
      rw [← hc] at h
      exact h }

/-- **The headline: `G₄ = ∑_p 1/(4^p − 1) = ∑_n ω(n)/4^n` is disjunctive in base four.** -/
theorem isDisjunctive_four : IsDisjunctive 4 primeLambertFour := by
  refine isDisjunctive_four_of_witness fun ℓ w hw homit => ?_
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · -- the empty word: the cylinder is `[0,1)`, which every orbit point hits
    exfalso
    subst hℓ
    have hw0 : w = 0 := by simpa using hw
    subst hw0
    have := homit 0
    simp only [Nat.cast_zero, pow_zero, zero_add, div_one] at this
    exact this (orbit_mem_Ico 4 primeLambertFour 0)
  · exact ⟨scheduleWitness ℓ w hℓ⟩

/-- **The binary corollary: `G₄` is disjunctive in base two.** -/
theorem isDisjunctive_two : IsDisjunctive 2 primeLambertFour :=
  isDisjunctive_two_of_four isDisjunctive_four

/-- The campaign's named headline Prop. -/
theorem G4DisjunctiveFour_holds : G4DisjunctiveFour := isDisjunctive_four

/-- The campaign's named binary Prop. -/
theorem G4DisjunctiveTwo_holds : G4DisjunctiveTwo := isDisjunctive_two

/-- **Every finite binary word occurs in the binary expansion of `G₄`.** -/
theorem every_binary_word_occurs (w : List ℕ) (hw : ∀ d ∈ w, d < 2) :
    ∃ n, OccursAt 2 primeLambertFour w n :=
  (isDisjunctive_iff_forall_occursAt 2 le_rfl primeLambertFour).1 isDisjunctive_two w hw

/-- **Every finite base-four word occurs in the base-four expansion of `G₄`.** -/
theorem every_quaternary_word_occurs (w : List ℕ) (hw : ∀ d ∈ w, d < 4) :
    ∃ n, OccursAt 4 primeLambertFour w n :=
  (isDisjunctive_iff_forall_occursAt 4 (by norm_num) primeLambertFour).1 isDisjunctive_four w hw

end NormalNumbers.G4
