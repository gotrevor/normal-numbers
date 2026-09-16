/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SchedWeight
import NormalNumbers.G4SchedOmegaAssembly

/-!
# The general weight headline: `∑_n w_c(n)/bⁿ` is disjunctive for every bounded `c`

`w_c = ω + excess c` with `c_p ≤ C`.  The schedule pays for `C` in one place — the outer
dimension must satisfy `100000·C·k₄³ ≤ 2^{k₄}`, which is arranged by taking `k₄ = j + C` with
`j ≥ max(50, 2C, k₄bℓ b ℓ)` (`exists_good_k₄`).  At `C = 1` this is the `Ω` schedule.
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

namespace SchedB

open Sched (N J logP₀Nat)

/-- `100000·2^m·(j+m)³ ≤ 2^{j+m}` for `j ≥ 50` and `2m ≤ j`. -/
lemma cube_le_two_pow_shift {m j : ℕ} (hj : 50 ≤ j) (hm : 2 * m ≤ j) :
    100000 * 2 ^ m * (j + m) ^ 3 ≤ 2 ^ (j + m) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 3 := ⟨j - 3, by omega⟩
  have hcube : 100000 * i ^ 3 ≤ 2 ^ i := cube_le_two_pow (by omega)
  have h2 : i + 3 + m ≤ 2 * i := by omega
  have hjm : (i + 3 + m) ^ 3 ≤ 8 * i ^ 3 := by
    calc (i + 3 + m) ^ 3 ≤ (2 * i) ^ 3 := Nat.pow_le_pow_left h2 3
      _ = 8 * i ^ 3 := by ring
  have hstep : 100000 * (i + 3 + m) ^ 3 ≤ 2 ^ (i + 3) := by
    calc 100000 * (i + 3 + m) ^ 3 ≤ 100000 * (8 * i ^ 3) := Nat.mul_le_mul_left _ hjm
      _ = 8 * (100000 * i ^ 3) := by ring
      _ ≤ 8 * 2 ^ i := Nat.mul_le_mul_left _ hcube
      _ = 2 ^ (i + 3) := by rw [pow_add]; ring
  calc 100000 * 2 ^ m * (i + 3 + m) ^ 3 = 2 ^ m * (100000 * (i + 3 + m) ^ 3) := by ring
    _ ≤ 2 ^ m * 2 ^ (i + 3) := Nat.mul_le_mul_left _ hstep
    _ = 2 ^ (i + 3 + m) := by rw [← pow_add]; ring_nf

/-- A `k₄` large enough for both the `(b,ℓ)` demand and the coefficient bound. -/
lemma exists_good_k₄ (b ℓ C : ℕ) :
    ∃ k₄, k₄bℓ b ℓ ≤ k₄ ∧ 40 ≤ k₄ ∧ 100000 * C * k₄ ^ 3 ≤ 2 ^ k₄ := by
  set j : ℕ := max (max 50 (2 * C)) (k₄bℓ b ℓ) with hj
  refine ⟨j + C, ?_, ?_, ?_⟩
  · exact le_trans (le_max_right _ _) (Nat.le_add_right _ _)
  · have : 50 ≤ j := le_trans (le_max_left _ _) (le_max_left _ _)
    omega
  · have h50 : 50 ≤ j := le_trans (le_max_left _ _) (le_max_left _ _)
    have h2C : 2 * C ≤ j := le_trans (le_max_right _ _) (le_max_left _ _)
    have hC2 : C ≤ 2 ^ C := Nat.lt_two_pow_self.le
    have := cube_le_two_pow_shift (m := C) h50 h2C
    calc 100000 * C * (j + C) ^ 3 ≤ 100000 * 2 ^ C * (j + C) ^ 3 := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hC2)
      _ ≤ 2 ^ (j + C) := this

noncomputable def scheduleWitnessCE (c : ℕ → ℕ) (C : ℕ) (hC : ∀ p, c p ≤ C)
    (b ℓ w e k₄ : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ)
    (hk : k₄bℓ b ℓ ≤ k₄) (hk40 : 40 ≤ k₄) (hCk : 100000 * C * k₄ ^ 3 ≤ 2 ^ k₄)
    (hE : HypE b (4 * k₄) e) :
    ScheduleWitnessC C b ℓ w :=
  let K := 4 * k₄
  have hK4 : K = 4 * k₄ := rfl
  have h : Hyp b K := hE.base
  have hK100 : 100 ≤ K := h.hK
  have hK1 : 1 ≤ K := h.hK1
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK100
  { G := gridOf K (N K) hK1
    hK := by show 0 < K; omega
    hr := Nat.one_le_pow _ _ (by show 0 < K ^ 2; positivity)
    hP₀ := (gridOf K (N K) hK1).P₀_pos
    X := XE K e
    hne := sample_nonemptyE hE
    η := (1 / 2 : ℝ) ^ k₄
    hη := by positivity
    ε := 1 / (K : ℝ)
    hε := by positivity
    hε1 := by rw [div_lt_one (by linarith)]; linarith
    M := MG b ℓ K
    hM := hM_holdsG hb hℓ hK4
    Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)
    hlog := by
      have h := log_det_one_add_tensorGram_le' hK1
      push_cast
      exact h
    δ₁ := 1 / 8
    hδ₁ := by norm_num
    hB := by
      intro g hglo hghi
      have hr : (gridOf K (N K) hK1).rDim = (K ^ 2) ^ K := rfl
      have hH : (gridOf K (N K) hK1).hDim = (K ^ 2 + 1) ^ K := rfl
      rw [hr] at hglo hghi
      rw [hr, hH]
      have hη : ((1 / 2 : ℝ) ^ k₄) ^ 4 ≤ (1 / 2 : ℝ) ^ K := by
        rw [← pow_mul, hK4, mul_comm]
      exact gridB_bound (bb := b) (by omega) hℓ (KG_ge hk) (MG_lo hb hℓ) (MG_hi hb hℓ)
        (by positivity) hη le_rfl hglo hghi
    R := RE e
    hR := RE_ge_two e
    Y := YE K e
    hRY := RE_le_YE K e
    D := Sched.Dj K k₄
    hN := hN_holds (by omega) hK4 hK100
    Mc := McE K e
    hMc := McE_pos hE
    lam' := Real.exp 1
    hlam' := Real.one_le_exp zero_le_one
    lam := 13 / 2
    hlam := by norm_num
    Mx := ((XE K e + J K * gridDm K (N K) : ℕ) : ℝ)
    hMx1 := by
      have : 1 ≤ XE K e := Nat.one_le_two_pow
      exact_mod_cast le_add_right this
    hMx := fun n hn i => by exact_mod_cast gridOf.add_shiftAL_le hK1 hn i
    Dm := gridDm K (N K)
    hDm := gridOf.d_le hK1
    ρmax := J K * gridDm K (N K)
    hρm := fun i => gridOf.shiftAL_le hK1 i
    δbig := 1 / 8
    δjunk := 1 / 8
    δfar := 11 / 64
    hbig := hbig_holdsE hK4 hE
    hjunk := hjunk_holdsCE hK4 hk40 hCk hE
    hfar := hfarC_holdsE (κ := max C 1) hK4 (by
      have h1 : C ≤ 2 ^ k₄ := by
        have hk3 : 1 ≤ k₄ ^ 3 := Nat.one_le_pow _ _ (by omega)
        nlinarith [hCk, Nat.zero_le C]
      have h2 : 1 ≤ 2 ^ k₄ := Nat.one_le_two_pow
      omega) hE
    hbudget := by
      have hbud := hbudget_holdsΩE (k₄ := k₄) hK4 hE
      have hc : Fintype.card (gridOf K (N K) hK1).Idx = Sched.T K := gridOf.card_Idx hK1
      rw [← hc] at hbud
      exact hbud }


/-- A schedule witness for `w_c` at every base `b ≥ 3`, depth `ℓ ≥ 1` and word `w`. -/
theorem exists_scheduleWitnessC (c : ℕ → ℕ) (C : ℕ) (hC : ∀ p, c p ≤ C)
    (b ℓ w : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) : Nonempty (ScheduleWitnessC C b ℓ w) := by
  classical
  obtain ⟨k₄, hk, hk40, hCk⟩ := exists_good_k₄ b ℓ C
  set K : ℕ := 4 * k₄ with hKdef
  have h : Hyp b K := hyp_KG hb hℓ hk
  have hK100 : 100 ≤ K := h.hK
  have hhi : McE K (m₁ b K) ≤ 2 ^ Sched.m₂ K :=
    MertensAP.moment_cap_subset hb h.hbK hK100 (D := 1) (Nat.one_le_two_pow) (by omega)
  have hE : HypE b K (m₁ b K) := ⟨h, le_rfl, hhi⟩
  exact ⟨scheduleWitnessCE c C hC b ℓ w (m₁ b K) k₄ hb hℓ hk hk40 hCk hE⟩

/-- **The general weight headline.**  For every bounded coefficient vector `c ≤ C`,
`∑_n w_c(n)/bⁿ = ∑_n (ω(n) + ∑_{p∣n} c_p (v_p(n) − 1))/bⁿ` is disjunctive in every base
`b ≥ 3`. -/
theorem isDisjunctive_weight (c : ℕ → ℕ) (C : ℕ) (hC : ∀ p, c p ≤ C) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (PrimeLambert.weightLambert b c) := by
  have hmain : IsDisjunctive b ((TWeight.weight c C hC).lambert b) := by
    refine isDisjunctive_weightC_of_witness c C hC b hb fun ℓ w hw homit => ?_
    rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
    · exfalso
      subst hℓ
      have hw0 : w = 0 := by simpa using hw
      subst hw0
      have := homit 0
      simp only [Nat.cast_zero, pow_zero, zero_add, div_one] at this
      exact this (orbit_mem_Ico b _ 0)
    · exact exists_scheduleWitnessC c C hC b ℓ w hb hℓ
  rwa [TWeight.lambert_weight (b := b) c C hC] at hmain

end SchedB

end NormalNumbers.G4
