/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2Sched

/-!
# The base-2 schedule under a stretched Mertens rate

`SchedB.exists_scheduleWitnessSC_two_of_supplyEff` consumes a Mertens rate
`F_S(e) ≥ c·e − C` (with `F_S(e) = sumInvPrimesIn S (2^{2^e})`).  Here the rate is relaxed to
`F_S(e) ≥ e^ε − C` for some `ε > 0`.

The cutoff exponent becomes `e₀ = n^q` with `q = ⌈1/ε⌉` and `n ≈ M(K) = exp(O(K log K))`, so
`log₂ e₀ = O(q·K log K)`, and the moment cap `10⁵·T K·e₀ ≤ 2^{8K²}` holds once `K = 2^{j+2}`
with `j ≥ q + 1` (`moment_cap_weak`): `(q+1)(j+3) ≤ j(j+3) ≤ 2^{j+3} = 2K`.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

open PrimeLambert GridParams

namespace MertensAP

variable {S : ℕ → Prop} [DecidablePred S]

/-- `(n^q)^ε ≥ n` once `q·ε ≥ 1`. -/
lemma le_rpow_pow {n q : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hq : 1 ≤ (q : ℝ) * ε) :
    (n : ℝ) ≤ (((n ^ q : ℕ) : ℝ)) ^ ε := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (n : ℝ) ^ ((q : ℝ) * ε) := Real.rpow_le_rpow_of_exponent_le hn' hq

/-- **The weak-rate cutoff.**  Under `F_S(e) ≥ e^ε − C` with `q·ε ≥ 1`, the schedule's
`S`-restricted small-prime demand is met at the exponent `n^q`, with
`n ≤ m·log 2 + 21K² + 4 + max C 0`. -/
theorem exists_cutoff_subset_weak {ε C : ℝ}
    (hw : ∀ e : ℕ, (e : ℝ) ^ ε - C ≤ sumInvPrimesIn S (2 ^ 2 ^ e))
    {q : ℕ} (hq : 1 ≤ (q : ℝ) * ε) {K : ℕ} (hK : 100 ≤ K) (m : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧
      (n : ℝ) ≤ (m : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 4 + max C 0 ∧
      ((m : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4
        ≤ ∑ p ∈ {p ∈ smallPrimes (2 ^ 2 ^ (n ^ q)) (gridOf K (Sched.N K) (by omega)).P₀ | S p},
            (p : ℝ)⁻¹) := by
  set M : ℝ := (m : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 2 with hM
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hM0 : 0 ≤ M + max C 0 := by
    have : (0 : ℝ) ≤ max C 0 := le_max_right _ _
    rw [hM]; positivity
  refine ⟨⌈M + max C 0⌉₊ + 1, by omega, ?_, ?_⟩
  · have := Nat.ceil_lt_add_one hM0
    push_cast
    rw [hM] at this
    linarith
  · have hn : (((⌈M + max C 0⌉₊ + 1 : ℕ)) : ℝ) ≤ (((⌈M + max C 0⌉₊ + 1) ^ q : ℕ) : ℝ) ^ ε :=
      le_rpow_pow (by omega) hq
    have h1 := hw ((⌈M + max C 0⌉₊ + 1) ^ q)
    have hc : M + max C 0 ≤ (⌈M + max C 0⌉₊ : ℝ) := Nat.le_ceil _
    have hCm : C ≤ max C 0 := le_max_left _ _
    have hsum : M ≤ sumInvPrimesIn S (2 ^ 2 ^ ((⌈M + max C 0⌉₊ + 1) ^ q)) := by
      push_cast at hn h1
      linarith
    have hmono := sumInvPrimesIn_mono (S := S)
      (Nat.le_succ (2 ^ 2 ^ ((⌈M + max C 0⌉₊ + 1) ^ q)))
    have hsched := sum_inv_smallPrimes_subset_ge (S := S) hK
      (2 ^ 2 ^ ((⌈M + max C 0⌉₊ + 1) ^ q))
    rw [hM] at hsum
    linarith [sq_nonneg (K : ℝ)]

end MertensAP

namespace SchedB

open Sched (N J T logP₀Nat m₂ Dj)

lemma mul_add_three_le_two_pow (j : ℕ) : j * (j + 3) ≤ 2 ^ (j + 3) := by
  induction j with
  | zero => norm_num
  | succ i ih =>
    have h := Nat.lt_two_pow_self (n := i + 2)
    have h2 : 2 ^ (i + 3) = 2 * 2 ^ (i + 2) := by ring
    calc (i + 1) * (i + 1 + 3) = i * (i + 3) + (2 * i + 4) := by ring
      _ ≤ 2 ^ (i + 3) + 2 ^ (i + 3) := by omega
      _ = 2 ^ (i + 1 + 3) := by ring

/-- **The moment cap at the stretched cutoff.**  With `K = 2^{j+2}`, `j ≥ q + 1`, the cutoff
`n^q` with `n ≤ Dc·Am`, `Dc ≤ 2^K`, `Am ≤ K^{3K+4}` stays under `2^{8K²}`. -/
lemma moment_cap_weak {j q K Dc Am n : ℕ} (hKdef : K = 2 ^ (j + 2)) (hj : q + 1 ≤ j)
    (hK : 100 ≤ K) (hDc : Dc ≤ 2 ^ K) (hAm : Am ≤ K ^ (3 * K + 4))
    (hn : n ≤ Dc * Am) :
    100000 * T K * n ^ q ≤ 2 ^ m₂ K := by
  have hT := Sched.T_le hK
  have hKpow : ∀ a, K ^ a = 2 ^ ((j + 2) * a) := fun a => by rw [hKdef, ← pow_mul]
  set E := (j + 3) * (3 * K + 4) with hE
  have hn' : n ≤ 2 ^ E := by
    calc n ≤ Dc * Am := hn
      _ ≤ 2 ^ K * 2 ^ ((j + 2) * (3 * K + 4)) := Nat.mul_le_mul hDc (by rw [← hKpow]; exact hAm)
      _ = 2 ^ (K + (j + 2) * (3 * K + 4)) := by rw [← pow_add]
      _ ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by rw [hE]; nlinarith)
  have hTE : T K ≤ 2 ^ E :=
    hT.trans (by rw [hKpow]; exact Nat.pow_le_pow_right (by norm_num) (by rw [hE]; nlinarith))
  have hjj : (q + 1) * (j + 3) ≤ 2 * K := by
    have := mul_add_three_le_two_pow j
    have h2 : 2 ^ (j + 3) = 2 * K := by rw [hKdef, pow_succ]; ring
    nlinarith
  calc 100000 * T K * n ^ q ≤ 2 ^ 17 * 2 ^ E * (2 ^ E) ^ q := by
        gcongr
        · norm_num
    _ = 2 ^ (17 + (q + 1) * E) := by rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
    _ ≤ 2 ^ m₂ K := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        show 17 + (q + 1) * E ≤ 8 * K ^ 2
        have : (q + 1) * E = (q + 1) * (j + 3) * (3 * K + 4) := by rw [hE]; ring
        rw [this]
        have := Nat.mul_le_mul_right (3 * K + 4) hjj
        nlinarith

lemma Am_le {K M1 : ℕ} (hK : 3 ≤ K) (hm : M1 ≤ K ^ (3 * K + 3)) :
    M1 + K ^ 2 + 1 ≤ K ^ (3 * K + 4) := by
  have hp : K ^ 2 ≤ K ^ (3 * K + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have : K ^ (3 * K + 4) = K * K ^ (3 * K + 3) := by rw [pow_succ]; ring
  rw [this]
  have hp1 : 1 ≤ K ^ (3 * K + 3) := Nat.one_le_pow _ _ (by omega)
  have h3 : 3 * K ^ (3 * K + 3) ≤ K * K ^ (3 * K + 3) := Nat.mul_le_mul_right _ (by omega)
  omega

lemma n_le_Dc_mul {n M1 K Dc : ℕ} {C : ℝ}
    (hn : (n : ℝ) ≤ (M1 : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 4 + max C 0)
    (hDc : 25 + max C 0 ≤ (Dc : ℝ)) : n ≤ Dc * (M1 + K ^ 2 + 1) := by
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hCm0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hm0 : (0 : ℝ) ≤ M1 := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ (K : ℝ) ^ 2 := by positivity
  have h1 : (M1 : ℝ) * Real.log 2 ≤ M1 := mul_le_of_le_one_right hm0 hl2'
  set Am : ℝ := (M1 : ℝ) + (K : ℝ) ^ 2 + 1 with hAm
  have hA1 : 1 ≤ Am := by rw [hAm]; linarith
  have h4 : max C 0 ≤ max C 0 * Am := le_mul_of_one_le_right hCm0 hA1
  have h5 : Am * (25 + max C 0) ≤ (Dc : ℝ) * Am := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hDc (by linarith)
  have : (n : ℝ) ≤ ((Dc * (M1 + K ^ 2 + 1) : ℕ) : ℝ) := by
    push_cast
    rw [← hAm]
    nlinarith
  exact_mod_cast this

variable (S : ℕ → Prop) [DecidablePred S]

/-- **N7 from the effective supply, under the stretched rate.** -/
theorem exists_scheduleWitnessSC_two_of_supplyEff_weak (hsup : VeryLargeCovSupplyEff S)
    {ε C : ℝ} (hε : 0 < ε)
    (hw : ∀ e : ℕ, (e : ℝ) ^ ε - C ≤ MertensAP.sumInvPrimesIn S (2 ^ 2 ^ e))
    (ℓ w : ℕ) (hℓ : 1 ≤ ℓ) :
    Nonempty (ScheduleWitnessSC S 2 ℓ w) := by
  classical
  obtain ⟨A, hA⟩ := hsup
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  set q : ℕ := ⌈1 / ε⌉₊ with hqdef
  have hq : 1 ≤ (q : ℝ) * ε := by
    have : 1 / ε ≤ (q : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hε] at this
    linarith
  set Dc : ℕ := ⌈25 + max C 0⌉₊ with hDc
  have hDcge : 25 + max C 0 ≤ (Dc : ℝ) := Nat.le_ceil _
  set B : ℕ := max (max (k₄bℓ 3 ℓ) Dc) (A + 25) with hB
  set j : ℕ := max (q + 1) B with hjdef
  set k₄ : ℕ := 2 ^ j with hk₄
  have hjk : j ≤ k₄ := (Nat.lt_two_pow_self).le
  have hBk : B ≤ k₄ := le_trans (le_max_right _ _) hjk
  have hk : k₄bℓ 3 ℓ ≤ k₄ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hBk
  have hDck : Dc ≤ k₄ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hBk
  have hAk : A + 25 ≤ k₄ := le_trans (le_max_right _ _) hBk
  set K : ℕ := 4 * k₄ with hKdef
  have hKj : K = 2 ^ (j + 2) := by rw [hKdef, hk₄, pow_add]; ring
  have h : Hyp 3 K := hyp_KG (by norm_num) hℓ hk
  have hK100 : 100 ≤ K := h.hK
  obtain ⟨n, hn1, hnle, hsum₀⟩ :=
    MertensAP.exists_cutoff_subset_weak (S := S) hw hq hK100 (m₁ 3 K)
  obtain ⟨M1, hM1⟩ : ∃ M1, m₁ 3 K = M1 := ⟨_, rfl⟩
  rw [hM1] at hsum₀ hnle
  have hm₁ : M1 ≤ K ^ (3 * K + 3) := hM1 ▸ m₁_le h
  set e₀ : ℕ := n ^ q with he₀def
  have hcap₀ : McE K e₀ ≤ 2 ^ m₂ K := by
    have hDc2 : Dc ≤ 2 ^ K := by have := Nat.lt_two_pow_self (n := K); omega
    exact moment_cap_weak hKj (le_max_left _ _) hK100 hDc2 (Am_le (by omega) hm₁)
      (n_le_Dc_mul hnle hDcge)
  -- the cap for the other two floors
  set w₂ : ℕ := 4 * logP₀Nat K + 2 * (K + N K) + K with hw₂
  have hele := e_bound_two (k₄ := k₄) (A := A) (Dc := 0) (e₀ := 0) (by omega) (by omega)
    (by omega) h (by omega)
  have hcap₁ : McE K (max (max 0 (m₁ 3 K)) (A + A * w₂)) ≤ 2 ^ m₂ K :=
    moment_cap_two (by omega) hele
  set e : ℕ := max (max e₀ (m₁ 3 K)) (A + A * w₂) with hedef
  have hhi : McE K e ≤ 2 ^ m₂ K := by
    have hsplit : e ≤ e₀ ∨ e ≤ max (max 0 (m₁ 3 K)) (A + A * w₂) := by
      rw [hedef]; omega
    unfold McE at hcap₀ hcap₁ ⊢
    rcases hsplit with hs | hs
    · exact le_trans (Nat.mul_le_mul_left _ hs) hcap₀
    · exact le_trans (Nat.mul_le_mul_left _ hs) hcap₁
  have hlo : m₁ 3 K ≤ e := le_trans (le_max_right _ _) (le_max_left _ _)
  have he₀e : e₀ ≤ e := le_trans (le_max_left _ _) (le_max_left _ _)
  have hE : HypE 3 K e := ⟨h, hlo, hhi⟩
  have hlow : (m₁ 3 K : ℝ) * Real.log 2 - 21 * ((K : ℕ) : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ (smallPrimes (RE e) (gridOf K (N K) hE.hK1).P₀).filter S, (p : ℝ)⁻¹ := by
    rw [hM1]
    refine hsum₀.trans ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨smallPrimes_mono (Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) he₀e)) hp.1, hp.2⟩
  have hZ := sizeZ_le hK100
  have hthr : A * ((gridOf K (N K) hE.hK1).P₀ * ((K + N K) * gridDm K (N K) + 1) * 2 ^ K) ^ A
      ≤ 2 ^ e := by
    calc A * ((gridOf K (N K) hE.hK1).P₀ * ((K + N K) * gridDm K (N K) + 1) * 2 ^ K) ^ A
        ≤ 2 ^ A * (2 ^ w₂) ^ A :=
          Nat.mul_le_mul (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left hZ _)
      _ = 2 ^ (A + A * w₂) := by rw [← pow_mul, ← pow_add, mul_comm w₂]
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  obtain ⟨x, hx1, hx2, hcov⟩ := hA K (N K) hE.hK1 ((1 / 2 : ℝ) ^ K) K le_rfl e hthr
  exact ⟨scheduleWitnessSC2 S ℓ w e k₄ x hℓ hk hE hlow hx1 hx2 hcov⟩

end SchedB

end NormalNumbers.G4
