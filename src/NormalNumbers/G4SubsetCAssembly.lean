/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SubsetCWitness
import NormalNumbers.G4SubsetAssembly
import NormalNumbers.G4UnboundedSched

/-!
# Campaign B, the merge: `w_{c,S}` is disjunctive

The two campaigns' parameter choices combine with no interference:

* the **subset** side (campaign A) inflates the cutoff exponent `e` by the Mertens rate's
  `Dc ≈ 1/(c log 2)`, and needs `Dc ≤ k₄`;
* the **unbounded** side (campaign B) needs `k₄ = 2^t` so that the junk budget
  `100000·C(k₄)·k₄³ ≤ 2^{k₄}` survives the `effC`-polynomial `C(k₄)`.

`exists_good_k₄_poly` already takes an arbitrary `a ≤ k₄`, so passing `a = max ⌈A⌉₊ Dc` buys
both at once.  The budget field is the `Ω`-shaped one over the `S`-filtered small primes
(`hbudget_holdsΩE_gen`).
-/

open Finset Real
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

open PrimeLambert GridParams

namespace SchedB

open Sched (N J)

/-- **`hbudget` for the `Ω`-shaped witness over an arbitrary sub-family of small primes.**
`hbudget_holdsΩE` with the family generalized exactly as `hbudget_holdsE_gen` generalizes
`hbudget_holdsE`. -/
theorem hbudget_holdsΩE_gen {b K k₄ e : ℕ} (hK4 : K = 4 * k₄) (h : HypE b K e)
    {sm : Finset ℕ} (hsub : sm ⊆ smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀)
    (hlow : (m₁ b K : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4 ≤ ∑ p ∈ sm, (p : ℝ)⁻¹) :
    (1 / 8 : ℝ) + ((1 / 8 : ℝ) + (1 / 8 : ℝ) + (11 / 64 : ℝ))
      + 2 * (1 / ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * Real.sqrt ((Sched.Dj K k₄ : ℕ) + 1)))
      + (((2 * Sched.Dj K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
        * smallPrimeBound sm (Sched.T K) (RE e) (McE K e)
            (apSample (XE K e) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card
            (Real.exp 1) (13 / 2) (freqSeed b K) < 1 := by
  have hK := h.base.hK
  have hk : 25 ≤ k₄ := by omega
  have hJ := Sched.jackson_term_le (K := K) (k₄ := k₄) (by omega)
  have hΛ := Sched.Lambda_le hK4 hk
  have hsmcard : sm.card ≤ RE e + 1 :=
    (Finset.card_le_card hsub).trans (Sched.card_smallPrimes_le _ _)
  have hsum : ∑ p ∈ sm, (p : ℝ)⁻¹ ≤ 3 * (e : ℝ) + 5 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans
      (sum_inv_smallPrimes_leE h)
  unfold smallPrimeBound
  exact budget_assemblyΩ hΛ (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (main_term_leE_gen h hlow) (term_a_leE_gen h hsmcard)
    (term_b_leE_gen h hsum) (term_c_leE_gen h hsum) (term_d_leE_gen h hsmcard) hJ

variable (S : ℕ → Prop) [DecidablePred S]

/-- **The merged schedule witness.**  `scheduleWitnessUE` with the `S`-filtered budget. -/
noncomputable def scheduleWitnessSUE (c : ℕ → ℕ) {A : ℝ} (C : ℕ)
    (b ℓ w e k₄ : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ)
    (hk : k₄bℓ b ℓ ≤ k₄) (hk40 : 40 ≤ k₄) (hCk : 100000 * C * k₄ ^ 3 ≤ 2 ^ k₄)
    (hE : HypE b (4 * k₄) e)
    (hEff : effC c (gridOf (4 * k₄) (Sched.N (4 * k₄)) hE.base.hK1).P₀ A ≤ (C : ℝ))
    (hlow : (m₁ b (4 * k₄) : ℝ) * Real.log 2 - 21 * ((4 * k₄ : ℕ) : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ (smallPrimes (RE e)
          (gridOf (4 * k₄) (Sched.N (4 * k₄)) hE.hK1).P₀).filter S, (p : ℝ)⁻¹) :
    ScheduleWitnessSU S c A b ℓ w :=
  let K := 4 * k₄
  have hK4 : K = 4 * k₄ := rfl
  have h : Hyp b K := hE.base
  have hK100 : 100 ≤ K := h.hK
  have hK1 : 1 ≤ K := h.hK1
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK100
  let U := scheduleWitnessUE c C b ℓ w e k₄ hb hℓ hk hk40 hCk hE hEff
  { G := U.G
    hK := U.hK
    hr := U.hr
    hP₀ := U.hP₀
    hΩ := U.hΩ
    X := U.X
    hne := U.hne
    η := U.η
    hη := U.hη
    ε := U.ε
    hε := U.hε
    hε1 := U.hε1
    M := U.M
    hM := U.hM
    Lg := U.Lg
    hlog := U.hlog
    δ₁ := U.δ₁
    hδ₁ := U.hδ₁
    hB := U.hB
    R := U.R
    hR := U.hR
    Y := U.Y
    hRY := U.hRY
    D := U.D
    hN := U.hN
    Mc := U.Mc
    hMc := U.hMc
    lam' := U.lam'
    hlam' := U.hlam'
    lam := U.lam
    hlam := U.hlam
    Mx := U.Mx
    hMx1 := U.hMx1
    hMx := U.hMx
    Dm := U.Dm
    hDm := U.hDm
    ρmax := U.ρmax
    hρm := U.hρm
    δbig := U.δbig
    δjunk := U.δjunk
    δfar := U.δfar
    hbig := U.hbig
    hjunk := U.hjunk
    hfar := U.hfar
    hbudget := by
      have hsub : (smallPrimes (RE e) (gridOf K (N K) hK1).P₀).filter S
          ⊆ smallPrimes (RE e) (gridOf K (N K) hK1).P₀ := Finset.filter_subset _ _
      have hbud := hbudget_holdsΩE_gen (k₄ := k₄) hK4 hE hsub hlow
      have hc : Fintype.card (gridOf K (N K) hK1).Idx = Sched.T K := gridOf.card_Idx hK1
      rw [← hc] at hbud
      exact hbud }

/-- **The merged existence statement.**  A Mertens rate for `S` and the `log₂log₂` coefficient
bound together produce a schedule witness at every base `b ≥ 3`, depth `ℓ ≥ 1`, word `w`. -/
theorem exists_scheduleWitnessSU (c : ℕ → ℕ) {A : ℝ} (hA : 1 ≤ A)
    (hc : ∀ x, c x ≤ Nat.log 2 (Nat.log 2 x)) {cm Cm : ℝ}
    (hmert : MertensAP.MertensRate S cm Cm)
    (b ℓ w : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) :
    Nonempty (ScheduleWitnessSU S c A b ℓ w) := by
  classical
  obtain ⟨hcm, -⟩ := id hmert
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  -- the Mertens inflation factor
  set Xr : ℝ := (24 + max Cm 0 + cm) / (cm * Real.log 2) with hXr
  have hXr0 : 0 < Xr := by
    rw [hXr]; have : (0:ℝ) ≤ max Cm 0 := le_max_right _ _; positivity
  set Dc : ℕ := ⌈Xr + 1⌉₊ with hDc
  have hDcge : Xr + 1 ≤ (Dc : ℝ) := Nat.le_ceil _
  have hDc1 : 1 ≤ Dc := by
    have : (1 : ℝ) ≤ (Dc : ℝ) := by linarith
    exact_mod_cast this
  -- a `k₄` large enough for BOTH the Mertens inflation and the junk budget
  obtain ⟨k₄, hk, hk40, ha, hCk⟩ := exists_good_k₄_poly b ℓ (max ⌈A⌉₊ Dc)
  have hDck : Dc ≤ k₄ := le_trans (le_max_right _ _) ha
  set K : ℕ := 4 * k₄ with hKdef
  set C : ℕ := max ⌈A⌉₊ Dc + 368 * k₄ ^ 2 + 88320 * k₄ ^ 4 with hC
  have h : Hyp b K := hyp_KG hb hℓ hk
  have hK100 : 100 ≤ K := h.hK
  have hK1 : 1 ≤ K := h.hK1
  -- the cutoff exponent supplied by the rate
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
  -- the Mertens supply at the enlarged cutoff
  have hlow : (m₁ b K : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ (smallPrimes (RE e) (gridOf K (N K) hE.hK1).P₀).filter S, (p : ℝ)⁻¹ := by
    refine hsum₀.trans ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨smallPrimes_mono (Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) he₀e)) hp.1, hp.2⟩
  -- the effective constant at this grid
  have hEff : effC c (gridOf K (N K) hK1).P₀ A ≤ (C : ℝ) := by
    have hbound := effC_le_of_logLog (gridOf K (N K) hK1) hc hA
      (Dm := gridDm K (N K)) (ρmax := J K * gridDm K (N K)) (V := 23 * K ^ 2)
      (gridOf.d_le hK1) (fun i => gridOf.shiftAL_le hK1 i)
      (Sched.sched_prime_size hK100 hK1)
      (L := 15 * (K : ℝ) ^ 2) (log_card_primeFactors_P₀_leE hE) (by positivity)
    refine hbound.trans ?_
    have hAc : A ≤ ((max ⌈A⌉₊ Dc : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil A) (by exact_mod_cast le_max_left ⌈A⌉₊ Dc)
    have hCr : (C : ℝ) = ((max ⌈A⌉₊ Dc : ℕ) : ℝ) + 368 * (k₄ : ℝ) ^ 2 + 88320 * (k₄ : ℝ) ^ 4 := by
      rw [hC]; push_cast; ring
    have hKr : (K : ℝ) = 4 * (k₄ : ℝ) := by rw [hKdef]; push_cast; ring
    have hcast : ((23 * K ^ 2 : ℕ) : ℝ) = 23 * (K : ℝ) ^ 2 := by push_cast; ring
    have hEq : ((23 * K ^ 2 : ℕ) : ℝ) * (1 + 15 * (K : ℝ) ^ 2)
        = 368 * (k₄ : ℝ) ^ 2 + 88320 * (k₄ : ℝ) ^ 4 := by
      rw [hcast, hKr]; ring
    rw [hCr, hEq]
    linarith [hAc]
  exact ⟨scheduleWitnessSUE S c C b ℓ w e k₄ hb hℓ hk hk40 hCk hE hEff hlow⟩

/-! ### The merged headline -/

/-- **The merged headline.**  For a prime set `S` with a Mertens rate and any coefficient vector
with `c_p ≤ ⌊log₂ log₂ p⌋`, the constant
`∑_n (ω_S(n) + ∑_{p ∣ n, p ∈ S} c_p (v_p(n) − 1))/bⁿ` is disjunctive in every base `b ≥ 3`. -/
theorem isDisjunctive_subsetWeight_logLog (c : ℕ → ℕ)
    (hc : ∀ x, c x ≤ Nat.log 2 (Nat.log 2 x)) {cm Cm : ℝ}
    (hmert : MertensAP.MertensRate S cm Cm) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (subsetWeightLambert S c b) := by
  have hlog : ∀ p, c p ≤ Nat.log 2 p := fun p =>
    (hc p).trans (Nat.log_mono_right (Nat.log_le_self 2 p))
  have hT : PrimeLambert.Tame c 4 := tame_of_natLog_le hlog
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
    · exact exists_scheduleWitnessSU S c (by norm_num : (1:ℝ) ≤ 4) hc hmert b ℓ w hb hℓ
  rwa [TWeight.lambert_weightSU (b := b) S c hT] at hmain

end SchedB

/-- **The residue-class instance.**  For `a` a unit mod `q`, the constant
`∑_n (ω_{a mod q}(n) + ∑_{p ∣ n, p ≡ a} c_p (v_p(n) − 1))/bⁿ` is disjunctive for `b ≥ 3`,
for every `c_p ≤ ⌊log₂ log₂ p⌋`. -/
theorem isDisjunctive_residueClass_weight_logLog {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) (c : ℕ → ℕ) (hc : ∀ x, c x ≤ Nat.log 2 (Nat.log 2 x))
    {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (subsetWeightLambert (fun p => (p : ZMod q) = a) c b) := by
  obtain ⟨cm, Cm, hmert⟩ := MertensAP.mertensRate_residueClass ha
  exact SchedB.isDisjunctive_subsetWeight_logLog _ c hc hmert hb

end NormalNumbers.G4
