/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4LogLogPow
import NormalNumbers.G4PolySched
import NormalNumbers.G4SubsetCAssembly

/-!
# Campaign B: the headline for the growth class `c_p ≤ A₀(1 + log₂log₂ p)^s`

Both places the coefficient size enters survive the widening:

* `cMax ≤ A₀(1 + V)^s` with `V = 23K²` — still polynomial in `K`, now of degree `2s`;
* tameness at `A = 5A₀(s+1)^s + 1` (`tame_of_logLog_pow`).

So `exists_good_k₄_polyGen` at degree `d = 2s + 2` closes the circularity exactly as
`exists_good_k₄_poly` did at `s = 1`, and the two headlines (the plain weight and the merged
`w_{c,S}`) go through with the same witnesses.
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

open PrimeLambert GridParams

/-- **`cMax` for the growth class.** -/
theorem cMax_le_of_logLog_pow (G : GridParams) {c : ℕ → ℕ} {A₀ s : ℕ}
    (hc : ∀ x, c x ≤ A₀ * (1 + Nat.log 2 (Nat.log 2 x)) ^ s) {Dm ρmax V : ℕ}
    (hDm : ∀ α, G.d α ≤ Dm) (hρ : ∀ i : G.Idx, G.ρ i ≤ ρmax)
    (hM : max (max Dm (2 * Fintype.card G.Idx)) ρmax ≤ 2 ^ 2 ^ V) :
    cMax c G.P₀ ≤ ((A₀ * (1 + V) ^ s : ℕ) : ℝ) := by
  refine cMax_le (fun p hp => ?_)
  have hple : p ≤ 2 ^ 2 ^ V :=
    le_trans (prime_le_of_dvd_P₀ G (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp) hDm hρ) hM
  have hlog : Nat.log 2 (Nat.log 2 p) ≤ V := by
    calc Nat.log 2 (Nat.log 2 p) ≤ Nat.log 2 (Nat.log 2 (2 ^ 2 ^ V)) :=
          Nat.log_mono_right (Nat.log_mono_right hple)
      _ = V := by rw [Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)]
  exact le_trans (hc p) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) s))

/-- **`effC` for the growth class**, in the schedule's two quantities. -/
theorem effC_le_of_logLog_pow (G : GridParams) {c : ℕ → ℕ} {A₀ s : ℕ}
    (hc : ∀ x, c x ≤ A₀ * (1 + Nat.log 2 (Nat.log 2 x)) ^ s) {A : ℝ} (hA : 1 ≤ A)
    {Dm ρmax V : ℕ}
    (hDm : ∀ α, G.d α ≤ Dm) (hρ : ∀ i : G.Idx, G.ρ i ≤ ρmax)
    (hM : max (max Dm (2 * Fintype.card G.Idx)) ρmax ≤ 2 ^ 2 ^ V) {L : ℝ}
    (hL : Real.log (G.P₀.primeFactors.card) ≤ L) (hL0 : 0 ≤ L) :
    effC c G.P₀ A ≤ A + ((A₀ * (1 + V) ^ s : ℕ) : ℝ) * (1 + L) := by
  refine (effC_le_closed (c := c) hA G.P₀).trans ?_
  have h1 := cMax_le_of_logLog_pow G hc hDm hρ hM
  have hc0 := cMax_nonneg c G.P₀
  have hlog0 : (0 : ℝ) ≤ Real.log (G.P₀.primeFactors.card) := Real.log_natCast_nonneg _
  nlinarith

namespace SchedB

open Sched (N J)

/-- The arithmetic of the widening: at `K = 4k₄` the `effC` numerator is a polynomial in `k₄`
of degree `2s + 2`, with the explicit coefficient `γ = 256·A₀·384^s`. -/
lemma effC_numerator_le (A₀ s k₄ : ℕ) (hk : 1 ≤ k₄) :
    A₀ * (1 + 23 * (4 * k₄) ^ 2) ^ s * (1 + 15 * (4 * k₄) ^ 2)
      ≤ (256 * A₀ * 384 ^ s) * k₄ ^ (2 * s + 2) := by
  have hk2 : 1 ≤ k₄ ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h1 : 1 + 23 * (4 * k₄) ^ 2 ≤ 384 * k₄ ^ 2 := by nlinarith
  have h2 : 1 + 15 * (4 * k₄) ^ 2 ≤ 256 * k₄ ^ 2 := by nlinarith
  have h3 : (1 + 23 * (4 * k₄) ^ 2) ^ s ≤ (384 * k₄ ^ 2) ^ s := Nat.pow_le_pow_left h1 s
  have h4 : (384 * k₄ ^ 2 : ℕ) ^ s = 384 ^ s * k₄ ^ (2 * s) := by
    rw [mul_pow, ← pow_mul]
  calc A₀ * (1 + 23 * (4 * k₄) ^ 2) ^ s * (1 + 15 * (4 * k₄) ^ 2)
      ≤ A₀ * (384 ^ s * k₄ ^ (2 * s)) * (256 * k₄ ^ 2) := by
        refine Nat.mul_le_mul (Nat.mul_le_mul_left _ ?_) h2
        rw [← h4]; exact h3
    _ = (256 * A₀ * 384 ^ s) * k₄ ^ (2 * s + 2) := by
        rw [pow_add]; ring

/-- **The schedule witness for the growth class.** -/
theorem exists_scheduleWitnessU_pow (c : ℕ → ℕ) {A₀ s : ℕ}
    (hc : ∀ x, c x ≤ A₀ * (1 + Nat.log 2 (Nat.log 2 x)) ^ s)
    {A : ℝ} (hA : 1 ≤ A) (b ℓ w : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) :
    Nonempty (ScheduleWitnessU c A b ℓ w) := by
  classical
  obtain ⟨k₄, hk, hk40, ha, hCk⟩ :=
    exists_good_k₄_polyGen b ℓ ⌈A⌉₊ (256 * A₀ * 384 ^ s) (d := 2 * s + 2) (by omega)
  set K : ℕ := 4 * k₄ with hKdef
  set C : ℕ := ⌈A⌉₊ + (256 * A₀ * 384 ^ s) * k₄ ^ (2 * s + 2) with hC
  have h : Hyp b K := hyp_KG hb hℓ hk
  have hK100 : 100 ≤ K := h.hK
  have hK1 : 1 ≤ K := h.hK1
  have hhi : McE K (m₁ b K) ≤ 2 ^ Sched.m₂ K :=
    MertensAP.moment_cap_subset hb h.hbK hK100 (D := 1) (Nat.one_le_two_pow) (by omega)
  have hE : HypE b K (m₁ b K) := ⟨h, le_rfl, hhi⟩
  have hEff : effC c (gridOf K (N K) hK1).P₀ A ≤ (C : ℝ) := by
    have hbound := effC_le_of_logLog_pow (gridOf K (N K) hK1) hc hA
      (Dm := gridDm K (N K)) (ρmax := J K * gridDm K (N K)) (V := 23 * K ^ 2)
      (gridOf.d_le hK1) (fun i => gridOf.shiftAL_le hK1 i)
      (Sched.sched_prime_size hK100 hK1)
      (L := 15 * (K : ℝ) ^ 2) (log_card_primeFactors_P₀_leE hE) (by positivity)
    refine hbound.trans ?_
    have hAc : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    have hnat : A₀ * (1 + 23 * K ^ 2) ^ s * (1 + 15 * K ^ 2)
        ≤ (256 * A₀ * 384 ^ s) * k₄ ^ (2 * s + 2) := by
      rw [hKdef]
      exact effC_numerator_le A₀ s k₄ (by omega)
    have hcast : ((A₀ * (1 + 23 * K ^ 2) ^ s : ℕ) : ℝ) * (1 + 15 * (K : ℝ) ^ 2)
        ≤ (((256 * A₀ * 384 ^ s) * k₄ ^ (2 * s + 2) : ℕ) : ℝ) := by
      have : ((A₀ * (1 + 23 * K ^ 2) ^ s * (1 + 15 * K ^ 2) : ℕ) : ℝ)
          ≤ (((256 * A₀ * 384 ^ s) * k₄ ^ (2 * s + 2) : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at this ⊢
      linarith
    have hCr : (C : ℝ) = (⌈A⌉₊ : ℝ) + (((256 * A₀ * 384 ^ s) * k₄ ^ (2 * s + 2) : ℕ) : ℝ) := by
      rw [hC]; push_cast; ring
    rw [hCr]
    linarith [hAc, hcast]
  exact ⟨scheduleWitnessUE c C b ℓ w (m₁ b K) k₄ hb hℓ hk hk40 hCk hE hEff⟩

/-- **The widened headline.**  Every coefficient vector with `c_p ≤ A₀(1 + log₂log₂ p)^s` — a
growth class containing arbitrarily fast-growing polylog vectors — gives a disjunctive
constant `∑_n (ω(n) + ∑_{p∣n} c_p(v_p(n) − 1))/bⁿ` in every base `b ≥ 3`. -/
theorem isDisjunctive_weight_logLogPow (c : ℕ → ℕ) {A₀ s : ℕ}
    (hc : ∀ x, c x ≤ A₀ * (1 + Nat.log 2 (Nat.log 2 x)) ^ s) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (PrimeLambert.weightLambert b c) := by
  have hT : PrimeLambert.Tame c ((5 * (A₀ * (s + 1) ^ s) + 1 : ℕ) : ℝ) :=
    tame_of_logLog_pow A₀ s hc
  have hA : (1 : ℝ) ≤ ((5 * (A₀ * (s + 1) ^ s) + 1 : ℕ) : ℝ) := by
    have : 1 ≤ 5 * (A₀ * (s + 1) ^ s) + 1 := by omega
    exact_mod_cast this
  have hmain : IsDisjunctive b ((TWeight.weightU c hT).lambert b) := by
    refine isDisjunctive_weightU_of_witness c hT b hb fun ℓ w hw homit => ?_
    rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
    · exfalso
      subst hℓ
      have hw0 : w = 0 := by simpa using hw
      subst hw0
      have := homit 0
      simp only [Nat.cast_zero, pow_zero, zero_add, div_one] at this
      exact this (orbit_mem_Ico b _ 0)
    · exact exists_scheduleWitnessU_pow c hc hA b ℓ w hb hℓ
  rwa [TWeight.lambert_weightU (b := b) c hT] at hmain

/-! ### The merged headline at the growth class -/

variable (S : ℕ → Prop) [DecidablePred S]

/-- **The merged schedule witness at the growth class.** -/
theorem exists_scheduleWitnessSU_pow (c : ℕ → ℕ) {A₀ s : ℕ}
    (hc : ∀ x, c x ≤ A₀ * (1 + Nat.log 2 (Nat.log 2 x)) ^ s)
    {A : ℝ} (hA : 1 ≤ A) {cm Cm : ℝ} (hmert : MertensAP.MertensRate S cm Cm)
    (b ℓ w : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) :
    Nonempty (ScheduleWitnessSU S c A b ℓ w) := by
  classical
  obtain ⟨hcm, -⟩ := id hmert
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  set Xr : ℝ := (24 + max Cm 0 + cm) / (cm * Real.log 2) with hXr
  have hXr0 : 0 < Xr := by
    rw [hXr]; have : (0:ℝ) ≤ max Cm 0 := le_max_right _ _; positivity
  set Dc : ℕ := ⌈Xr + 1⌉₊ with hDc
  have hDcge : Xr + 1 ≤ (Dc : ℝ) := Nat.le_ceil _
  have hDc1 : 1 ≤ Dc := by
    have : (1 : ℝ) ≤ (Dc : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨k₄, hk, hk40, ha, hCk⟩ :=
    exists_good_k₄_polyGen b ℓ (max ⌈A⌉₊ Dc) (256 * A₀ * 384 ^ s) (d := 2 * s + 2) (by omega)
  have hDck : Dc ≤ k₄ := le_trans (le_max_right _ _) ha
  set K : ℕ := 4 * k₄ with hKdef
  set C : ℕ := max ⌈A⌉₊ Dc + (256 * A₀ * 384 ^ s) * k₄ ^ (2 * s + 2) with hC
  have h : Hyp b K := hyp_KG hb hℓ hk
  have hK100 : 100 ≤ K := h.hK
  have hK1 : 1 ≤ K := h.hK1
  obtain ⟨e₀, hsum₀, hbnd₀⟩ := MertensAP.exists_cutoff_subset hmert hK100 (m₁ b K)
  set e : ℕ := max e₀ (m₁ b K) with hedef
  have hlo : m₁ b K ≤ e := le_max_right _ _
  have he₀e : e₀ ≤ e := le_max_left _ _
  have hDle : Dc ≤ 2 ^ K := by
    calc Dc ≤ k₄ := hDck
      _ ≤ 2 ^ k₄ := (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  set Aq : ℕ := m₁ b K + K ^ 2 + 1 with hAq
  have hA1 : (1 : ℝ) ≤ (Aq : ℝ) := by
    have : 1 ≤ Aq := by omega
    exact_mod_cast this
  have hA0 : (0 : ℝ) < (Aq : ℝ) := by linarith
  have hm₁A : (m₁ b K : ℝ) ≤ (Aq : ℝ) := by
    have : m₁ b K ≤ Aq := by omega
    exact_mod_cast this
  have hKA : ((K : ℝ)) ^ 2 ≤ (Aq : ℝ) := by
    have : K ^ 2 ≤ Aq := by omega
    have h' : ((K ^ 2 : ℕ) : ℝ) ≤ (Aq : ℝ) := by exact_mod_cast this
    push_cast at h'; linarith
  have hm₁0 : (0 : ℝ) ≤ (m₁ b K : ℝ) := by positivity
  have hCmax : Cm ≤ max Cm 0 := le_max_left _ _
  have hCmax0 : (0 : ℝ) ≤ max Cm 0 := le_max_right _ _
  have hQ : ((m₁ b K : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 2 + Cm + cm)
      ≤ (Aq : ℝ) * (24 + max Cm 0 + cm) := by
    have h1 : (m₁ b K : ℝ) * Real.log 2 ≤ (Aq : ℝ) := by nlinarith
    have h2 : 21 * (K : ℝ) ^ 2 ≤ 21 * (Aq : ℝ) := by linarith
    have h3 : (2 : ℝ) ≤ 2 * (Aq : ℝ) := by linarith
    have h4 : Cm ≤ max Cm 0 * (Aq : ℝ) := by nlinarith
    have h5 : cm ≤ cm * (Aq : ℝ) := by nlinarith
    nlinarith
  have hbnd : (e₀ : ℝ) ≤ (Dc : ℝ) * (Aq : ℝ) := by
    have hdiv : ((m₁ b K : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 2 + Cm + cm)
        / (cm * Real.log 2) ≤ (Aq : ℝ) * Xr := by
      rw [hXr, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_right hQ (by positivity)
    have hmax : max 0 (((m₁ b K : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 2 + Cm + cm)
        / (cm * Real.log 2)) ≤ (Aq : ℝ) * Xr := by
      refine max_le ?_ hdiv
      positivity
    have : (e₀ : ℝ) ≤ (Aq : ℝ) * Xr + 1 := by linarith
    nlinarith
  have hele : e ≤ Dc * Aq := by
    have h1 : e₀ ≤ Dc * Aq := by
      have : (e₀ : ℝ) ≤ ((Dc * Aq : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have h2 : m₁ b K ≤ Dc * Aq := by
      calc m₁ b K ≤ Aq := by omega
        _ ≤ Dc * Aq := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hhi : McE K e ≤ 2 ^ Sched.m₂ K :=
    MertensAP.moment_cap_subset hb h.hbK hK100 hDle hele
  have hE : HypE b K e := ⟨h, hlo, hhi⟩
  have hlow : (m₁ b K : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ (smallPrimes (RE e) (gridOf K (N K) hE.hK1).P₀).filter S, (p : ℝ)⁻¹ := by
    refine hsum₀.trans ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨smallPrimes_mono (Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) he₀e)) hp.1, hp.2⟩
  have hEff : effC c (gridOf K (N K) hK1).P₀ A ≤ (C : ℝ) := by
    have hbound := effC_le_of_logLog_pow (gridOf K (N K) hK1) hc hA
      (Dm := gridDm K (N K)) (ρmax := J K * gridDm K (N K)) (V := 23 * K ^ 2)
      (gridOf.d_le hK1) (fun i => gridOf.shiftAL_le hK1 i)
      (Sched.sched_prime_size hK100 hK1)
      (L := 15 * (K : ℝ) ^ 2) (log_card_primeFactors_P₀_leE hE) (by positivity)
    refine hbound.trans ?_
    have hAc : A ≤ ((max ⌈A⌉₊ Dc : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil A) (by exact_mod_cast le_max_left ⌈A⌉₊ Dc)
    have hnat : A₀ * (1 + 23 * K ^ 2) ^ s * (1 + 15 * K ^ 2)
        ≤ (256 * A₀ * 384 ^ s) * k₄ ^ (2 * s + 2) := by
      rw [hKdef]
      exact effC_numerator_le A₀ s k₄ (by omega)
    have hcast : ((A₀ * (1 + 23 * K ^ 2) ^ s : ℕ) : ℝ) * (1 + 15 * (K : ℝ) ^ 2)
        ≤ (((256 * A₀ * 384 ^ s) * k₄ ^ (2 * s + 2) : ℕ) : ℝ) := by
      have : ((A₀ * (1 + 23 * K ^ 2) ^ s * (1 + 15 * K ^ 2) : ℕ) : ℝ)
          ≤ (((256 * A₀ * 384 ^ s) * k₄ ^ (2 * s + 2) : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at this ⊢
      linarith
    have hCr : (C : ℝ)
        = ((max ⌈A⌉₊ Dc : ℕ) : ℝ) + (((256 * A₀ * 384 ^ s) * k₄ ^ (2 * s + 2) : ℕ) : ℝ) := by
      rw [hC]; push_cast; ring
    rw [hCr]
    linarith [hAc, hcast]
  exact ⟨scheduleWitnessSUE S c C b ℓ w e k₄ hb hℓ hk hk40 hCk hE hEff hlow⟩

/-- **The merged headline at the growth class**: a divergent prime subset *and* a polylog
coefficient vector. -/
theorem isDisjunctive_subsetWeight_logLogPow (c : ℕ → ℕ) {A₀ s : ℕ}
    (hc : ∀ x, c x ≤ A₀ * (1 + Nat.log 2 (Nat.log 2 x)) ^ s) {cm Cm : ℝ}
    (hmert : MertensAP.MertensRate S cm Cm) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (subsetWeightLambert S c b) := by
  have hT : PrimeLambert.Tame c ((5 * (A₀ * (s + 1) ^ s) + 1 : ℕ) : ℝ) :=
    tame_of_logLog_pow A₀ s hc
  have hA : (1 : ℝ) ≤ ((5 * (A₀ * (s + 1) ^ s) + 1 : ℕ) : ℝ) := by
    have : 1 ≤ 5 * (A₀ * (s + 1) ^ s) + 1 := by omega
    exact_mod_cast this
  have hmain : IsDisjunctive b ((TWeight.weightSU S c hT).lambert b) := by
    refine isDisjunctive_weightSU_of_witness S c hT b hb fun ℓ w hw homit => ?_
    rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
    · exfalso
      subst hℓ
      have hw0 : w = 0 := by simpa using hw
      subst hw0
      have := homit 0
      simp only [Nat.cast_zero, pow_zero, zero_add, div_one] at this
      exact this (orbit_mem_Ico b _ 0)
    · exact exists_scheduleWitnessSU_pow S c hc hA hmert b ℓ w hb hℓ
  rwa [TWeight.lambert_weightSU (b := b) S c hT] at hmain

end SchedB

/-- **The residue-class instance at the growth class.** -/
theorem isDisjunctive_residueClass_weight_logLogPow {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) (c : ℕ → ℕ) {A₀ s : ℕ}
    (hc : ∀ x, c x ≤ A₀ * (1 + Nat.log 2 (Nat.log 2 x)) ^ s) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (subsetWeightLambert (fun p => (p : ZMod q) = a) c b) := by
  obtain ⟨cm, Cm, hmert⟩ := MertensAP.mertensRate_residueClass ha
  exact SchedB.isDisjunctive_subsetWeight_logLogPow _ c hc hmert hb

end NormalNumbers.G4
