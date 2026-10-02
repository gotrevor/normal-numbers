/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2TTHyp
import NormalNumbers.G4Base2Cov
import NormalNumbers.G4SchedBE
import NormalNumbers.LiteratureTTEquidistributedDefect

/-!
# N3–N6: the very-large covariance supply, decomposed

* `exists_bins` (N3): greedy partition of a prime set into bins of harmonic mass `≤ 2θ`.
* `binErr_le_pairs`: `c − 1[c > 0] ≤ C(c, 2)`, so the bin error is a pair count.
* `avg_binErr_le` (N4 average): sample mean of the bin error `≤ Σ_ℓ mass_ℓ² + C₆·P₀/log Y`.
* `abs_one_sub_binDelta_le`: `|1 − δ_I(N)| ≤ 2·mass(I)` for `mass(I) ≤ 1`.
* `sum_inv_vlPrimes_le`: the very-large primes up to `Y^{102}` have mass `≤ 5`.
* `omegaVLS_le`: `ω_{S,>Y}(m) ≤ 101` for `m < Y^{102}`.
* `binPair_cov` (N6 core): from TT (dyadic), a power-of-two `X` at which all bin-pair cross
  moments of the centred indicators are `≤ ε₂`.
-/

open Finset

namespace NormalNumbers.G4.Base2

/-- Harmonic mass of a finset. -/
noncomputable def mass (I : Finset ℕ) : ℝ := ∑ p ∈ I, (p : ℝ)⁻¹

/-- The dyadic base of `n`: `2^k` for `n ∈ (2^k, 2^{k+1}]`. -/
noncomputable def dyBase (n : ℕ) : ℝ := (2 : ℝ) ^ Nat.log 2 (n - 1)

/-- **N3.** -/
theorem exists_bins (Q : Finset ℕ) {θ : ℝ} (hθ : 0 < θ) (hQ : ∀ p ∈ Q, (p : ℝ)⁻¹ ≤ θ) :
    ∃ B : ℕ, ∃ bins : Fin B → Finset ℕ,
      (∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (bins ℓ) (bins ℓ')) ∧ univ.biUnion bins = Q ∧
      (∀ ℓ, mass (bins ℓ) ≤ 2 * θ) ∧ (B : ℝ) ≤ mass Q / θ + 1 := by
  sorry

theorem binErr_le_pairs (c : ℕ) : (c : ℝ) - (if c = 0 then 0 else 1) ≤ (c.choose 2 : ℝ) := by
  rcases c with _ | c
  · simp
  · rw [if_neg (Nat.succ_ne_zero c), Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    have : (0 : ℝ) ≤ (c.choose 2 : ℝ) := by positivity
    linarith

theorem abs_one_sub_binDelta_le (I : Finset ℕ) (hI : ∀ p ∈ I, p.Prime) (hm : mass I ≤ 1)
    (N : ℝ) : |1 - binDelta I N| ≤ 2 * mass I := by
  sorry

variable (S : ℕ → Prop) [DecidablePred S]

theorem sum_inv_vlPrimes_le : ∃ Y₀ : ℕ, ∀ Y P₀ M : ℕ, Y₀ ≤ Y → M ≤ Y ^ 102 →
    mass (vlPrimes S Y P₀ M) ≤ 5 := by
  sorry

theorem omegaVLS_le {Y P₀ m : ℕ} (hY : 2 ≤ Y) (hm : m < Y ^ 102) : omegaVLS S Y P₀ m ≤ 101 := by
  by_contra hc
  push Not at hc
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp [omegaVLS] at hc
  set F := m.primeFactors.filter (fun p => S p ∧ ¬ p ∣ P₀ ∧ Y < p) with hF
  have hdvd : ∏ p ∈ F, p ∣ m := by
    refine (Finset.prod_dvd_prod_of_subset _ _ id (filter_subset _ _)).trans ?_
    exact Nat.prod_primeFactors_dvd m
  have hle : Y ^ F.card ≤ ∏ p ∈ F, p := by
    rw [← prod_const]
    exact prod_le_prod' fun p hp => ((mem_filter.1 hp).2.2.2).le
  have h1 : Y ^ 102 ≤ Y ^ F.card :=
    Nat.pow_le_pow_right (by omega) (by unfold omegaVLS at hc; exact hc)
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
  omega

/-- **N4, average.** -/
theorem avg_binErr_le : ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (X Y P₀ b₀ ρ : ℕ) (B : ℕ) (bins : Fin B → Finset ℕ),
    0 < P₀ → b₀ < P₀ → P₀ < Y → Y ≤ X → ρ ≤ X → 2 * P₀ ≤ X →
    (∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (bins ℓ) (bins ℓ')) →
    (∀ ℓ, ∀ p ∈ bins ℓ, p.Prime ∧ Y < p) →
    ((apSample X P₀ b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X P₀ b₀, ∑ ℓ,
        ((binCount (bins ℓ) (n + ρ) : ℝ) - (if binCount (bins ℓ) (n + ρ) = 0 then 0 else 1))
      ≤ ∑ ℓ, mass (bins ℓ) ^ 2 + C₆ * P₀ / Real.log Y := by
  sorry

/-- **N6 core.**  From TT 3.1(i) (dyadic) and N5 (`binInd_ap_mean`).  75%. -/
theorem binPair_cov (htt : CastingOut.TTEquidistributedDyadic) (K N : ℕ) (hK : 1 ≤ K)
    {ε₂ : ℝ} (hε : 0 < ε₂) (Bmax : ℕ) : ∃ e₀ : ℕ, ∀ e, e₀ ≤ e → ∀ B ≤ Bmax,
      ∀ bins : Fin B → Finset ℕ, (∀ ℓ, ∀ p ∈ bins ℓ, p.Prime ∧ SchedB.YE K e < p) →
      ∃ x : ℕ, 100 * 2 ^ SchedB.mE K e ≤ x ∧ x ≤ 101 * 2 ^ SchedB.mE K e ∧
        ∀ ℓ ℓ' : Fin B, ∀ i j : (gridOf K N hK).Idx, i ≠ j →
          |((apSample (2 ^ x) (gridOf K N hK).P₀ (gridOf K N hK).b₀).card : ℝ)⁻¹ *
            ∑ n ∈ apSample (2 ^ x) (gridOf K N hK).P₀ (gridOf K N hK).b₀,
              ((binInd (bins ℓ) (n + shiftAL (gridOf K N hK).B (gridOf K N hK).Q
                  (gridOf K N hK).D₀ i)).re - binDelta (bins ℓ) (dyBase n))
              * ((binInd (bins ℓ') (n + shiftAL (gridOf K N hK).B (gridOf K N hK).Q
                  (gridOf K N hK).D₀ j)).re - binDelta (bins ℓ') (dyBase n))| ≤ ε₂ := by
  sorry

end NormalNumbers.G4.Base2
