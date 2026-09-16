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
  sorry

end SchedB

end NormalNumbers.G4
