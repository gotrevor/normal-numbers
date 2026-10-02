/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2Supply
import NormalNumbers.G4Base2Pair

/-!
# N6 core: bin-pair cross moments from TT 3.1(i) (dyadic)

TT applied once per bin pair at `X_T = 2^{101·2^{mE}} = Y^{101}`, `L = log X_T / C₅`; the union of
the exceptional scales is avoided by `exists_good_x`; each good block is `block_bound` +
`shifted_mean_le` (N5); the sample average is `abs_avg_le_blocks`.
-/

open Finset

namespace NormalNumbers.G4.Base2

lemma dyBase_of_mem {k n : ℕ} (hn : n ∈ Ioc (2 ^ k) (2 ^ (k + 1))) : dyBase n = 2 ^ k := by
  rw [mem_Ioc] at hn
  unfold dyBase
  congr 1
  rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by omega⟩)]
  constructor <;> omega

lemma abs_re_binInd_le (I : Finset ℕ) (n : ℕ) : |(binInd I n).re| ≤ 1 := by
  unfold binInd; split_ifs <;> simp

/-- **One good block.**  TT's bound `T` and the N5 error `E` at `N = 2^k` give the centred
bin-pair block bound. -/
theorem good_block_bound (I I' : Finset ℕ) (P₀ b₀ k h₁ h₂ : ℕ) (hP₀ : 0 < P₀) (hb : b₀ < P₀)
    (hh : h₁ ≤ 2 ^ k) {T E : ℝ} (hE : 0 ≤ E)
    (hδ : |binDelta I (2 ^ k)| ≤ 3) (hδ' : |binDelta I' (2 ^ k)| ≤ 3)
    (hTT : ‖(((P₀ : ℝ) / ((2 ^ k : ℕ) : ℝ) : ℝ) : ℝ) •
        ∑ n ∈ (Ioc (2 ^ k) (2 * 2 ^ k)).filter (fun n => n % P₀ = b₀ % P₀),
          (binInd I (n + h₁) - ((binDelta I ((2 ^ k : ℕ) : ℝ) : ℝ) : ℂ)) * binInd I' (n + h₂)‖ ≤ T)
    (hN5 : ‖(∑ n ∈ (Ioc (2 ^ k) (2 * 2 ^ k)).filter (fun n => n % P₀ = (b₀ + h₁) % P₀),
          binInd I n) - (((((2 ^ k : ℕ) : ℝ) / P₀) * binDelta I ((2 ^ k : ℕ) : ℝ) : ℝ) : ℂ)‖ ≤ E) :
    |(P₀ : ℝ) / 2 ^ k * blockSum2 (fun n =>
        ((binInd I (n + h₁)).re - binDelta I (dyBase n))
        * ((binInd I' (n + h₂)).re - binDelta I' (dyBase n))) P₀ b₀ k|
      ≤ T + 3 * ((P₀ : ℝ) / 2 ^ k * (E + 2 * h₁ + 6)) := by
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  rw [hcast] at hTT hN5
  have hbmod : b₀ % P₀ = b₀ := Nat.mod_eq_of_lt hb
  set s := (Ioc (2 ^ k) (2 * 2 ^ k)).filter (fun n => n % P₀ = b₀ % P₀) with hs
  have hblk : blockSum2 (fun n =>
        ((binInd I (n + h₁)).re - binDelta I (dyBase n))
        * ((binInd I' (n + h₂)).re - binDelta I' (dyBase n))) P₀ b₀ k
      = ∑ n ∈ s, ((binInd I (n + h₁)).re - binDelta I (2 ^ k))
          * ((binInd I' (n + h₂)).re - binDelta I' (2 ^ k)) := by
    unfold blockSum2
    rw [hs, hbmod, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]
    refine sum_congr rfl fun n hn => ?_
    dsimp only
    rw [dyBase_of_mem (mem_filter.1 hn).1]
  rw [hblk]
  refine block_bound s (fun n => (binInd I n).re) (fun n => (binInd I' n).re) h₁ h₂ ?_ ?_ hδ'
    (by positivity)
  · have h := norm_TT_eq s (binInd I) (binInd I') (binInd_im I) (binInd_im I')
      (binDelta I (2 ^ k)) ((P₀ : ℝ) / 2 ^ k) h₁ h₂
    rw [h] at hTT
    exact hTT
  · have hsm := shifted_mean_le (fun n => (binInd I n).re) (abs_re_binInd_le I) (2 ^ k) P₀ b₀ h₁
      hP₀ (by positivity) hh (D := 3) hδ (E := E) ?_
    · push_cast at hsm; rw [hs]; norm_num at hsm ⊢; exact hsm
    · have hre : (∑ m ∈ (Ioc (2 ^ k) (2 * 2 ^ k)).filter (fun m => m % P₀ = (b₀ + h₁) % P₀),
          (binInd I m).re) - ((2 ^ k : ℕ) : ℝ) / P₀ * binDelta I (2 ^ k)
          = ((∑ n ∈ (Ioc (2 ^ k) (2 * 2 ^ k)).filter (fun n => n % P₀ = (b₀ + h₁) % P₀),
            binInd I n) - ((((2 : ℝ) ^ k / P₀) * binDelta I (2 ^ k) : ℝ) : ℂ)).re := by
        rw [Complex.sub_re, Complex.re_sum, Complex.ofReal_re]; push_cast; ring
      have him : ((∑ n ∈ (Ioc (2 ^ k) (2 * 2 ^ k)).filter (fun n => n % P₀ = (b₀ + h₁) % P₀),
            binInd I n) - ((((2 : ℝ) ^ k / P₀) * binDelta I (2 ^ k) : ℝ) : ℂ)).im = 0 := by
        rw [Complex.sub_im, Complex.im_sum, Complex.ofReal_im]; simp [binInd_im]
      rw [hre]
      exact (Complex.abs_re_eq_norm.2 him).trans_le hN5

/-- **N6 core.**  From TT 3.1(i) (dyadic) and N5 (`binInd_ap_mean`).  75%. -/
theorem binPair_cov (htt : CastingOut.TTEquidistributedDyadic) (K N : ℕ) (hK : 1 ≤ K)
    {ε₂ : ℝ} (hε : 0 < ε₂) (Bmax : ℕ) : ∃ e₀ : ℕ, ∀ e, e₀ ≤ e → ∀ B ≤ Bmax,
      ∀ bins : Fin B → Finset ℕ, (∀ ℓ, ∀ p ∈ bins ℓ, p.Prime ∧ SchedB.YE K e < p) → (∀ ℓ, mass (bins ℓ) ≤ 1) →
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
