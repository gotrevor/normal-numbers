/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SchedOmega

/-!
# The `Ω` schedule witness at a free cutoff

`scheduleWitnessΩE` is `SchedB.scheduleWitnessSE` with the two `Ω`-specific §4D fields
(`hjunk`, `hfar`) supplied by `G4SchedOmega` and the four-delta budget `hbudget_holdsΩE`.
No Mertens input is needed: `Ω` is not restricted to a subset of primes, so the small primes
are the schedule's own `smallPrimes (RE e) P₀`.  The extra demand over the `ω` schedule is
`40 ≤ k₄` (from `hjunk_holdsE`).
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

namespace SchedB

open Sched (N J logP₀Nat)

/-- **The `Ω` schedule witness in base `b ≥ 3`** at any cutoff exponent `e` admissible for the
schedule (`HypE`), with `k₄ ≥ 40`. -/
noncomputable def scheduleWitnessΩE (b ℓ w e k₄ : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ)
    (hk : k₄bℓ b ℓ ≤ k₄) (hk40 : 40 ≤ k₄) (hE : HypE b (4 * k₄) e) :
    ScheduleWitnessΩ b ℓ w :=
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
    hjunk := hjunk_holdsE hK4 hk40 hE
    hfar := hfarΩ_holdsE hK4 hE
    hbudget := by
      have hbud := hbudget_holdsΩE (k₄ := k₄) hK4 hE
      have hc : Fintype.card (gridOf K (N K) hK1).Idx = Sched.T K := gridOf.card_Idx hK1
      rw [← hc] at hbud
      exact hbud }

/-! ### The `Ω` headline

No Mertens input is needed, so the cutoff may be taken at its minimum `e = m₁ b K`; the only
extra demand over the `ω` schedule is `k₄ ≥ 40`. -/

/-- A schedule witness for `Ω` at every base `b ≥ 3`, depth `ℓ ≥ 1` and word `w`. -/
theorem exists_scheduleWitnessΩ (b ℓ w : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) :
    Nonempty (ScheduleWitnessΩ b ℓ w) := by
  classical
  set k₄ : ℕ := max (k₄bℓ b ℓ) 40 with hk₄
  have hk : k₄bℓ b ℓ ≤ k₄ := le_max_left _ _
  have hk40 : 40 ≤ k₄ := le_max_right _ _
  set K : ℕ := 4 * k₄ with hKdef
  have h : Hyp b K := hyp_KG hb hℓ hk
  have hK100 : 100 ≤ K := h.hK
  have hhi : McE K (m₁ b K) ≤ 2 ^ Sched.m₂ K :=
    MertensAP.moment_cap_subset hb h.hbK hK100 (D := 1) (Nat.one_le_two_pow) (by omega)
  have hE : HypE b K (m₁ b K) := ⟨h, le_rfl, hhi⟩
  exact ⟨scheduleWitnessΩE b ℓ w (m₁ b K) k₄ hb hℓ hk hk40 hE⟩

/-- **The `Ω` headline.**  `∑_n Ω(n)/bⁿ` is disjunctive in every base `b ≥ 3`. -/
theorem isDisjunctive_Omega {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (TWeight.cardFactors.lambert b) := by
  refine isDisjunctive_cardFactorsLambert_of_witness b hb fun ℓ w hw homit => ?_
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · exfalso
    subst hℓ
    have hw0 : w = 0 := by simpa using hw
    subst hw0
    have := homit 0
    simp only [Nat.cast_zero, pow_zero, zero_add, div_one] at this
    exact this (orbit_mem_Ico b _ 0)
  · exact exists_scheduleWitnessΩ b ℓ w hb hℓ


end SchedB

end NormalNumbers.G4
