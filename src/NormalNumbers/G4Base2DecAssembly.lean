/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2DecSched

/-!
# The base-2 witness for every divergent prime set

On the decoupled frame (`HypE2`, moment order at `s`; far tail through `farCS`) the cutoff
exponent `e` has no upper cap.  So for a divergent `S` take `e` the **first** exponent past the
floor `e_min` at which `F_S(e) := Σ_{p ∈ S, p ≤ 2^{2^e}} 1/p` reaches `m₁·log 2`.  One tower step
adds at most `4(1 + log 2) < 7` (`sumInvPrimes_tower_step`, from `sum_inv_primes_Ioc_le`), so
`F_S(e) ≤ 3·e_min + 5` (`exists_first_crossing`), and the moment parameter `s = e_min` meets the
cap.  The far tail sees `F_S(2^x + Dm) ≤ F_S(e) + 7·(m₂ + 7)`.

`exists_scheduleWitnessSCS_two_of_divergent` needs only divergence: no rate at all.
-/

open Finset Real Filter
open scoped BigOperators Nat

namespace NormalNumbers.G4

open PrimeLambert GridParams

/-! ### Tower increments of the `S`-reciprocal sum -/

section Tower

variable (S : ℕ → Prop) [DecidablePred S]

/-- `F(e) := F_S(2^{2^e} + 1)`, the `S`-reciprocal sum over primes `≤ 2^{2^e}`. -/
noncomputable def towerF (e : ℕ) : ℝ := MertensAP.sumInvPrimesIn S (2 ^ 2 ^ e + 1)

lemma sum_inv_Ioc_le_four (R Y : ℕ) (hR : 2 ≤ R) (hRY : R ≤ Y) :
    ∑ p ∈ ((Y + 1).primesBelow.filter S).filter (fun p => R < p), (p : ℝ)⁻¹
      ≤ 4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R)) := by
  refine le_trans ?_ (sum_inv_primes_Ioc_le hR hRY)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1.1, hp.2⟩

lemma towerF_split (R Y : ℕ) :
    MertensAP.sumInvPrimesIn S (Y + 1)
      ≤ MertensAP.sumInvPrimesIn S (R + 1)
        + ∑ p ∈ ((Y + 1).primesBelow.filter S).filter (fun p => R < p), (p : ℝ)⁻¹ := by
  unfold MertensAP.sumInvPrimesIn
  rw [← Finset.sum_filter_add_sum_filter_not ((Y + 1).primesBelow.filter S) (fun p => R < p)]
  rw [add_comm]
  gcongr
  intro p hp
  simp only [Finset.mem_filter, Nat.mem_primesBelow] at hp ⊢
  exact ⟨⟨by omega, hp.1.1.2⟩, hp.1.2⟩

/-- **One tower step adds at most 7.** -/
lemma towerF_succ_le (a : ℕ) : towerF S (a + 1) ≤ towerF S a + 7 := by
  have hR : 2 ≤ 2 ^ 2 ^ a := Sched.two_le_two_pow_two_pow a
  have hRY : 2 ^ 2 ^ a ≤ 2 ^ 2 ^ (a + 1) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h1 := towerF_split S (2 ^ 2 ^ a) (2 ^ 2 ^ (a + 1))
  have h2 := sum_inv_Ioc_le_four S _ _ hR hRY
  rw [Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)] at h2
  push_cast at h2
  rw [Real.log_pow, Real.log_pow] at h2
  push_cast at h2
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  unfold towerF
  linarith

lemma towerF_add_le (a j : ℕ) : towerF S (a + j) ≤ towerF S a + 7 * j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have := towerF_succ_le S (a + j)
    rw [← add_assoc]
    push_cast
    linarith

/-- `F_S(2^{2^e} + 1) ≤ 3e + 5` (all-primes Mertens, dyadic constant 4). -/
lemma towerF_le (e : ℕ) : towerF S e ≤ 3 * (e : ℝ) + 5 := by
  have hR : (2 : ℕ) ≤ 2 ^ 2 ^ e := Sched.two_le_two_pow_two_pow e
  have h1 := towerF_split S 2 (2 ^ 2 ^ e)
  have h2 := sum_inv_Ioc_le_four S 2 _ le_rfl hR
  rw [Nat.log_pow (by norm_num)] at h2
  have hlog2 : Nat.log 2 2 = 1 := by simpa using Nat.log_pow (by norm_num : 1 < 2) 1
  rw [hlog2] at h2
  push_cast at h2
  rw [Real.log_pow, Real.log_one] at h2
  have h3 : MertensAP.sumInvPrimesIn S (2 + 1) ≤ 1 / 2 := by
    unfold MertensAP.sumInvPrimesIn
    have hsub : (3 : ℕ).primesBelow.filter S ⊆ {2} := by
      intro p hp
      simp only [Finset.mem_filter, Nat.mem_primesBelow] at hp
      have := hp.1.2.two_le
      rw [Finset.mem_singleton]; omega
    calc ∑ p ∈ (3 : ℕ).primesBelow.filter S, (p : ℝ)⁻¹ ≤ ∑ p ∈ ({2} : Finset ℕ), (p : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 / 2 := by simp
  have hl2 : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have he0 : (0 : ℝ) ≤ e := by positivity
  unfold towerF
  nlinarith

/-- **The first crossing.**  If `F` is unbounded, then past any floor `e₀ ≥ 1` there is an
exponent at which `F` has reached `D ≤ e₀` while still `F ≤ 3e₀ + 5`. -/
lemma exists_first_crossing (hdiv : ∀ B : ℝ, ∃ e, B ≤ towerF S e) {e₀ : ℕ} (he₀ : 1 ≤ e₀)
    {D : ℝ} (hD : D ≤ e₀) :
    ∃ e, e₀ ≤ e ∧ D ≤ towerF S e ∧ towerF S e ≤ 3 * (e₀ : ℝ) + 5 := by
  classical
  have hex : ∃ e, e₀ ≤ e ∧ D ≤ towerF S e := by
    obtain ⟨e, he⟩ := hdiv D
    by_cases h : e₀ ≤ e
    · exact ⟨e, h, he⟩
    · refine ⟨e₀, le_rfl, he.trans ?_⟩
      have := towerF_add_le S e (e₀ - e)
      have hmono : towerF S e ≤ towerF S e₀ := by
        unfold towerF
        exact MertensAP.sumInvPrimesIn_mono (Nat.succ_le_succ
          (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))))
      exact hmono
  let e := Nat.find hex
  have hspec : e₀ ≤ e ∧ D ≤ towerF S e := Nat.find_spec hex
  refine ⟨e, hspec.1, hspec.2, ?_⟩
  rcases Nat.eq_or_lt_of_le hspec.1 with heq | hlt
  · rw [← heq]; exact towerF_le S e₀
  · have hprev : ¬ (e₀ ≤ e - 1 ∧ D ≤ towerF S (e - 1)) := Nat.find_min hex (by omega)
    have hlt' : towerF S (e - 1) < D := by
      by_contra hc; exact hprev ⟨by omega, not_lt.1 hc⟩
    have hstep := towerF_succ_le S (e - 1)
    rw [show e - 1 + 1 = e by omega] at hstep
    have he₀r : (1 : ℝ) ≤ e₀ := by exact_mod_cast he₀
    linarith

end Tower

namespace SchedB

namespace Dec

open Sched (N J T logP₀Nat m₂ Dj)

lemma HypE2.s_le {b K e s : ℕ} (h : HypE2 b K e s) : s ≤ 2 ^ (8 * K ^ 2) := by
  have hT1 : 1 ≤ T K := Sched.T_pos h.hK1
  have := h.hi
  unfold McE at this
  have : s ≤ 100000 * T K * s := Nat.le_mul_of_pos_left _ (by positivity)
  show s ≤ 2 ^ m₂ K
  omega

lemma far_mass_num {K : ℕ} (hK : 100 ≤ K) {E F : ℝ} (hE : E ≤ (2 : ℝ) ^ (8 * K ^ 2))
    (hF : F ≤ 3 * E + 5 + 7 * (8 * (K : ℝ) ^ 2 + 7)) : F ≤ (2 : ℝ) ^ (39 * K ^ 2) := by
  have hK2 : 8 * K ^ 2 + 7 < 2 ^ (8 * K ^ 2 + 7) := Nat.lt_two_pow_self
  have hK2r : (8 : ℝ) * (K : ℝ) ^ 2 + 7 ≤ (2 : ℝ) ^ (8 * K ^ 2 + 7) := by
    have := hK2.le; exact_mod_cast this
  have hpow : (2 : ℝ) ^ (8 * K ^ 2 + 7) = 128 * (2 : ℝ) ^ (8 * K ^ 2) := by
    rw [pow_add]; norm_num; ring
  have hbig : (2 : ℝ) ^ (8 * K ^ 2) * 2 ^ 10 ≤ (2 : ℝ) ^ (39 * K ^ 2) := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (8 * K ^ 2) := one_le_pow₀ (by norm_num)
  nlinarith

variable (S : ℕ → Prop) [DecidablePred S]

/-- **N7 for every divergent `S`.**  The effective covariance supply plus divergence of
`Σ_{p∈S} 1/p` gives the base-2 schedule witness (with the `S`-restricted far tail). -/
theorem exists_scheduleWitnessSCS_two_of_divergent (hsup : VeryLargeCovSupplyEff S)
    (hdiv : ∀ B : ℝ, ∃ e, B ≤ towerF S e) (ℓ w : ℕ) (hℓ : 1 ≤ ℓ) :
    Nonempty (ScheduleWitnessSCS S 2 ℓ w) := by
  classical
  obtain ⟨A, hA⟩ := hsup
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  set k₄ : ℕ := max (k₄bℓ 3 ℓ) (A + 25) with hk₄
  have hk : k₄bℓ 3 ℓ ≤ k₄ := le_max_left _ _
  have hAk : A + 25 ≤ k₄ := le_max_right _ _
  set K : ℕ := 4 * k₄ with hKdef
  have h : Hyp 3 K := hyp_KG (by norm_num) hℓ hk
  have hK100 : 100 ≤ K := h.hK
  set w₂ : ℕ := 4 * logP₀Nat K + 2 * (K + N K) + K with hw₂
  -- the floor `e_min` and its cap
  have hele := e_bound_two (k₄ := k₄) (A := A) (Dc := 0) (e₀ := 0) (by omega) (by omega)
    (by omega) h (by omega)
  have hcap₁ : McE K (max (max 0 (m₁ 3 K)) (A + A * w₂)) ≤ 2 ^ m₂ K :=
    moment_cap_two (by omega) hele
  set e₀ : ℕ := max (max 0 (m₁ 3 K)) (A + A * w₂) with he₀def
  have hm₁e₀ : m₁ 3 K ≤ e₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hAe₀ : A + A * w₂ ≤ e₀ := le_max_right _ _
  have hm₁pos : 1 ≤ m₁ 3 K := by
    have := m₁_ge_cube (b := 3) (K := K) (by norm_num) (by omega)
    have : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have he₀1 : 1 ≤ e₀ := hm₁pos.trans hm₁e₀
  -- the first crossing of `m₁·log 2`
  have hD : (m₁ 3 K : ℝ) * Real.log 2 ≤ e₀ := by
    have : ((m₁ 3 K : ℕ) : ℝ) ≤ e₀ := by exact_mod_cast hm₁e₀
    have h0 : (0 : ℝ) ≤ (m₁ 3 K : ℕ) := Nat.cast_nonneg _
    nlinarith
  obtain ⟨e, hee₀, hFlo, hFhi⟩ := exists_first_crossing S hdiv he₀1 hD
  have hE : HypE2 3 K e e₀ := ⟨h, hm₁e₀.trans hee₀, hm₁e₀, hcap₁⟩
  -- the small-prime sum, both ways
  have hsmall_le : ∑ p ∈ (smallPrimes (RE e) (gridOf K (N K) hE.hK1).P₀).filter S, (p : ℝ)⁻¹
      ≤ towerF S e := by
    unfold towerF MertensAP.sumInvPrimesIn
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro p hp
    simp only [Finset.mem_filter, smallPrimes, RE] at hp ⊢
    exact ⟨hp.1.1, hp.2⟩
  have hlow : (m₁ 3 K : ℝ) * Real.log 2 - 21 * ((K : ℕ) : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ (smallPrimes (RE e) (gridOf K (N K) hE.hK1).P₀).filter S, (p : ℝ)⁻¹ := by
    have := MertensAP.sum_inv_smallPrimes_subset_ge (S := S) hK100 (RE e)
    have e1 : towerF S e = MertensAP.sumInvPrimesIn S (RE e + 1) := rfl
    have e2 : ∑ p ∈ {p ∈ smallPrimes (RE e) (gridOf K (Sched.N K) (by omega)).P₀ | S p}, (p : ℝ)⁻¹
        = ∑ p ∈ (smallPrimes (RE e) (gridOf K (N K) hE.hK1).P₀).filter S, (p : ℝ)⁻¹ := rfl
    rw [e2, ← e1] at this
    linarith
  have hsum : ∑ p ∈ (smallPrimes (RE e) (gridOf K (N K) hE.hK1).P₀).filter S, (p : ℝ)⁻¹
      ≤ 3 * (e₀ : ℝ) + 5 := hsmall_le.trans hFhi
  -- the covariance supply at `e`
  have hZ := sizeZ_le hK100
  have hthr : A * ((gridOf K (N K) hE.hK1).P₀ * ((K + N K) * gridDm K (N K) + 1) * 2 ^ K) ^ A
      ≤ 2 ^ e := by
    calc A * ((gridOf K (N K) hE.hK1).P₀ * ((K + N K) * gridDm K (N K) + 1) * 2 ^ K) ^ A
        ≤ 2 ^ A * (2 ^ w₂) ^ A :=
          Nat.mul_le_mul (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left hZ _)
      _ = 2 ^ (A + A * w₂) := by rw [← pow_mul, ← pow_add, mul_comm w₂]
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (hAe₀.trans hee₀)
  obtain ⟨x, hx1, hx2, hcov⟩ := hA K (N K) hE.hK1 ((1 / 2 : ℝ) ^ K) K le_rfl e hthr
  -- the far-tail `S`-mass
  have hFS : MertensAP.sumInvPrimesIn S (2 ^ x + gridDm K (N K)) ≤ (2 : ℝ) ^ (39 * K ^ 2) := by
    have hDm : gridDm K (N K) ≤ 2 ^ x :=
      (gridDm_le_XE hE).trans (Nat.pow_le_pow_right (by norm_num) hx1)
    have hxle : x + 1 ≤ 2 ^ (e + (m₂ K + 7)) := by
      have : 2 ^ (e + (m₂ K + 7)) = 128 * 2 ^ mE K e := by
        unfold mE; rw [show e + (m₂ K + 7) = (e + m₂ K) + 7 by ring, pow_add]; ring
      rw [this]
      have : 1 ≤ 2 ^ mE K e := Nat.one_le_two_pow
      omega
    have hbound : 2 ^ x + gridDm K (N K) ≤ 2 ^ 2 ^ (e + (m₂ K + 7)) + 1 := by
      have : 2 ^ x + gridDm K (N K) ≤ 2 ^ (x + 1) := by rw [pow_succ]; omega
      have := this.trans (Nat.pow_le_pow_right (by norm_num) hxle)
      omega
    have h1 := MertensAP.sumInvPrimesIn_mono (S := S) hbound
    have h2 := towerF_add_le S e (m₂ K + 7)
    have he₀r : (e₀ : ℝ) ≤ (2 : ℝ) ^ (8 * K ^ 2) := by exact_mod_cast hE.s_le
    have hm2r : ((m₂ K + 7 : ℕ) : ℝ) = 8 * (K : ℝ) ^ 2 + 7 := by
      show ((8 * K ^ 2 + 7 : ℕ) : ℝ) = _; push_cast; ring
    unfold towerF at h2
    rw [hm2r] at h2
    refine far_mass_num hK100 he₀r (h1.trans ?_)
    have := hFhi; unfold towerF at this; linarith
  exact ⟨scheduleWitnessSCS2 S ℓ w e e₀ k₄ x hℓ hk hE hlow hsum hFS hx1 hx2 hcov⟩

end Dec

end SchedB

end NormalNumbers.G4
