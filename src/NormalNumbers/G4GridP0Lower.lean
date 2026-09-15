/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4ScheduleParams

/-!
# A *lower* bound on the progression modulus, and the level-to-level growth

Every estimate in the `E0` cone wants `P₀` **small**, so the repo carries only upper bounds
(`gridOf.P₀_le`, `P₀_le_two_pow`).  The head of a band needs the opposite: the head of band
`i+1` consumes `≈ 16·wFloor_{i+1}·|Atom_{i+1}|/P₀_{i+1}` windows against a history of
`≈ wTop_i·kk_i/(2·P₀_i)` digits, and `wFloor_{i+1} = 4·Dm_{i+1}·wTop_i`, so the head is a
vanishing fraction of the history exactly when

> `P₀ (K+4)  ≥  256·(K+4)²·Dm(K+4)·H(K+4) · P₀ K`      (`P₀_growth`)

This module proves that.  The mechanism:

* **`gridQ_le_dist`** — two distinct atoms **in the same layer** have shifts that differ by a
  multiple of `Q`: `ρ_{α,j} = j + Q(j·D₀ + proj B j α)` (`shiftG_eq`), so the difference is
  `Q·(proj α − proj β)`, nonzero by `ρ_injective`.  Hence `dist ≥ Q`.
* **`distProd_ge`** — the shift-difference product of `freezeQ` therefore has at least
  `T·(H−1)` factors of size `≥ Q`: `freezeQ ≥ Q^{T(H−1)}` (`P₀_ge_pow`).
* **`P₀_le_pow_gridQ`** — in the other direction every factor of `gridP₀Bound` is a power of
  `Q`, so `P₀ K ≤ Q^{6T²}`.
* The exponents then settle it: `H(K+4) ≥ K⁸·H K` while `T² = H²N²`, so
  `T'(H'−1) ≥ 6T² + 3` with room to spare, and `Q` is monotone in `(K, N)`.
-/

open Finset
open scoped BigOperators Nat

namespace NormalNumbers.G4

open NormalNumbers.G4.Sched (N)

lemma gridQ_pos (K N : ℕ) : 0 < gridQ K N := Nat.factorial_pos _

lemma le_dist_of_dvd {a b q : ℕ} (hq : 0 < q) (hab : a ≠ b) (h : (q:ℤ) ∣ ((a:ℤ) - b)) :
    q ≤ Nat.dist a b := by
  have hd : q ∣ Nat.dist a b := by
    rcases le_total a b with hle | hle
    · rw [Nat.dist_eq_sub_of_le hle]
      have hc : ((b - a : ℕ) : ℤ) = -((a:ℤ) - b) := by
        rw [Nat.cast_sub hle]; ring
      have : (q:ℤ) ∣ ((b - a : ℕ) : ℤ) := by rw [hc]; exact dvd_neg.mpr h
      exact_mod_cast this
    · rw [Nat.dist_eq_sub_of_le_right hle]
      have hc : ((a - b : ℕ) : ℤ) = ((a:ℤ) - b) := by
        rw [Nat.cast_sub hle]
      have : (q:ℤ) ∣ ((a - b : ℕ) : ℤ) := by rw [hc]; exact h
      exact_mod_cast this
  exact Nat.le_of_dvd (Nat.dist_pos_of_ne hab) hd

theorem gridQ_le_dist {K NN : ℕ} (hK : 1 ≤ K) {α β : (gridOf K NN hK).Atom} (hab : α ≠ β)
    (jj : Fin NN) :
    gridQ K NN ≤ Nat.dist ((gridOf K NN hK).ρ (α, jj)) ((gridOf K NN hK).ρ (β, jj)) := by
  have hj : 1 ≤ layer K jj := by unfold layer; omega
  have hne : (gridOf K NN hK).ρ (α, jj) ≠ (gridOf K NN hK).ρ (β, jj) := by
    intro h
    exact hab (congrArg Prod.fst ((gridOf K NN hK).ρ_injective h))
  have hρα : (((gridOf K NN hK).ρ (α, jj) : ℕ) : ℤ)
      = (layer K jj : ℤ) + ((gridOf K NN hK).Q : ℤ) * ((layer K jj : ℤ) * (gridOf K NN hK).D₀ + proj (gridOf K NN hK).B (layer K jj) α) := by
    show ((shiftG (gridOf K NN hK).B (gridOf K NN hK).Q (gridOf K NN hK).D₀ α (layer K jj) : ℕ) : ℤ) = _
    rw [shiftG_eq (gridOf K NN hK).B (gridOf K NN hK).Q (gridOf K NN hK).D₀ α ((gridOf K NN hK).hD α) hj]
  have hρβ : (((gridOf K NN hK).ρ (β, jj) : ℕ) : ℤ)
      = (layer K jj : ℤ) + ((gridOf K NN hK).Q : ℤ) * ((layer K jj : ℤ) * (gridOf K NN hK).D₀
          + proj (gridOf K NN hK).B (layer K jj) β) := by
    show ((shiftG (gridOf K NN hK).B (gridOf K NN hK).Q (gridOf K NN hK).D₀ β (layer K jj) : ℕ) : ℤ) = _
    rw [shiftG_eq (gridOf K NN hK).B (gridOf K NN hK).Q (gridOf K NN hK).D₀ β ((gridOf K NN hK).hD β) hj]
  have hdvd : ((gridQ K NN : ℕ) : ℤ)
      ∣ ((((gridOf K NN hK).ρ (α, jj) : ℕ) : ℤ) - (((gridOf K NN hK).ρ (β, jj) : ℕ) : ℤ)) := by
    refine ⟨proj (gridOf K NN hK).B (layer K jj) α - proj (gridOf K NN hK).B (layer K jj) β, ?_⟩
    rw [hρα, hρβ]
    show _ = ((gridOf K NN hK).Q : ℤ) * _
    ring
  exact le_dist_of_dvd (gridQ_pos K NN) hne hdvd



theorem distProd_ge {K NN : ℕ} (hK : 1 ≤ K) :
    gridQ K NN ^ (gridT K NN * (gridH K - 1))
      ≤ ∏ i : (gridOf K NN hK).Idx, ∏ i' : (gridOf K NN hK).Idx,
          (if i = i' then 1 else Nat.dist ((gridOf K NN hK).ρ i) ((gridOf K NN hK).ρ i')) := by
  classical
  have hcardA : Fintype.card (gridOf K NN hK).Atom = gridH K := by
    rw [(gridOf K NN hK).card_atom, gridOf.hDim_eq]; rfl
  have hstep : ∀ i : (gridOf K NN hK).Idx,
      gridQ K NN ^ (gridH K - 1)
        ≤ ∏ i' : (gridOf K NN hK).Idx,
            (if i = i' then 1 else Nat.dist ((gridOf K NN hK).ρ i) ((gridOf K NN hK).ρ i')) := by
    intro i
    have hle : ∀ i' ∈ (Finset.univ : Finset (gridOf K NN hK).Idx),
        (if i'.2 = i.2 ∧ i'.1 ≠ i.1 then gridQ K NN else 1)
          ≤ (if i = i' then 1 else Nat.dist ((gridOf K NN hK).ρ i) ((gridOf K NN hK).ρ i')) := by
      intro i' _
      by_cases hc : i'.2 = i.2 ∧ i'.1 ≠ i.1
      · rw [if_pos hc]
        have hne : i ≠ i' := by
          intro h; exact hc.2 (by rw [h])
        rw [if_neg hne]
        have : i' = (i'.1, i.2) := by
          rw [← hc.1]
        have hd := gridQ_le_dist hK (Ne.symm hc.2) i.2
        calc gridQ K NN ≤ Nat.dist ((gridOf K NN hK).ρ (i.1, i.2)) ((gridOf K NN hK).ρ (i'.1, i.2)) := hd
          _ = Nat.dist ((gridOf K NN hK).ρ i) ((gridOf K NN hK).ρ i') := by
              rw [← this]
      · rw [if_neg hc]
        by_cases hii : i = i'
        · rw [if_pos hii]
        · rw [if_neg hii]
          exact Nat.one_le_iff_ne_zero.2 (fun h => hii
            ((gridOf K NN hK).ρ_injective (Nat.eq_of_dist_eq_zero h)))
    refine le_trans (le_of_eq ?_) (Finset.prod_le_prod' hle)
    rw [Finset.prod_ite]
    have hfil : (Finset.univ : Finset (gridOf K NN hK).Idx).filter
        (fun i' => i'.2 = i.2 ∧ i'.1 ≠ i.1)
        = ((Finset.univ : Finset (gridOf K NN hK).Atom).erase i.1) ×ˢ {i.2} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        Finset.mem_erase, Finset.mem_singleton]
      tauto
    rw [Finset.prod_const, Finset.prod_const_one, mul_one, hfil, Finset.card_product,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_singleton, Finset.card_univ,
      hcardA, mul_one]
  calc gridQ K NN ^ (gridT K NN * (gridH K - 1))
      = ∏ _i : (gridOf K NN hK).Idx, gridQ K NN ^ (gridH K - 1) := by
        rw [Finset.prod_const, Finset.card_univ, gridOf.card_Idx, ← pow_mul]
        congr 1
        rw [gridT, gridH]; ring
    _ ≤ _ := Finset.prod_le_prod' fun i _ => hstep i


/-- **`P₀ ≥ Q^{T(H−1)}`.** -/
theorem P₀_ge_pow {K NN : ℕ} (hK : 1 ≤ K) :
    gridQ K NN ^ (gridT K NN * (gridH K - 1)) ≤ (gridOf K NN hK).P₀ := by
  classical
  have hprim : 0 < ∏ p ∈ (2 * Fintype.card (gridOf K NN hK).Idx + 1).primesBelow, p :=
    Finset.prod_pos fun p hp => (Nat.mem_primesBelow.1 hp).2.pos
  have hMp : 0 < (gridOf K NN hK).Mprod := (gridOf K NN hK).Mprod_pos
  have hchain : (∏ i : (gridOf K NN hK).Idx, ∏ i' : (gridOf K NN hK).Idx,
      (if i = i' then 1 else Nat.dist ((gridOf K NN hK).ρ i) ((gridOf K NN hK).ρ i')))
      ≤ (gridOf K NN hK).P₀ := by
    show _ ≤ (gridOf K NN hK).Mprod * (gridOf K NN hK).freezeQ
    refine le_trans ?_ (Nat.le_mul_of_pos_left _ hMp)
    show _ ≤ (∏ p ∈ (2 * Fintype.card (gridOf K NN hK).Idx + 1).primesBelow, p) * _
    exact Nat.le_mul_of_pos_left _ hprim
  exact le_trans (distProd_ge hK) hchain

/-! ### The upper side: every factor of `gridP₀Bound` is a power of `Q` -/

lemma mul_self_pred_le_factorial (n : ℕ) : n * (n - 1) ≤ n ! := by
  cases n with
  | zero => simp
  | succ m =>
      rw [Nat.factorial_succ]
      simpa using Nat.mul_le_mul_left (m + 1) (Nat.self_le_factorial m)

lemma gridSum_ge_pow {K B : ℕ} (hK : 1 ≤ K) : B ^ K ≤ gridSum K B := by
  have hmem : (⟨K - 1, by omega⟩ : Fin K) ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ _
  have := Finset.single_le_sum (f := fun i : Fin K => B ^ ((i : ℕ) + 1))
    (fun i _ => Nat.zero_le _) hmem
  simpa [gridSum, Nat.sub_add_cancel hK] using this

lemma gridH_le_gridUmax {K N : ℕ} (hK : 1 ≤ K) : gridH K ≤ gridUmax K N := by
  have hB : K ^ 2 + 1 ≤ gridB K N := by
    unfold gridB
    have : K ^ 2 * 1 ≤ K ^ 2 * (K + N) := Nat.mul_le_mul_left _ (by omega)
    omega
  have h1 : gridH K ≤ gridB K N ^ K := by
    unfold gridH
    exact Nat.pow_le_pow_left hB K
  have h2 : gridB K N ^ K ≤ gridSum K (gridB K N) := gridSum_ge_pow hK
  have h3 : gridSum K (gridB K N) ≤ K ^ 2 * gridSum K (gridB K N) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  unfold gridUmax
  omega

lemma one_le_gridUmax {K N : ℕ} (hK : 1 ≤ K) : 1 ≤ gridUmax K N := by
  have h := gridH_le_gridUmax (K := K) (N := N) hK
  have : 1 ≤ gridH K := Nat.one_le_iff_ne_zero.2 (by unfold gridH; positivity)
  omega

lemma gridDm_le_gridQ_sq {K N : ℕ} (hK : 1 ≤ K) : gridDm K N ≤ gridQ K N ^ 2 := by
  set U := gridUmax K N with hU
  set W := U + K + N + 2 with hW
  have hUpos : 1 ≤ U := one_le_gridUmax (N := N) hK
  have hfac : W * (W - 1) ≤ gridQ K N := by
    have := mul_self_pred_le_factorial W
    simpa [gridQ, hW, hU] using this
  have hkey : (K + 1) * U + 1 ≤ gridQ K N := by
    have h1 : (K + 2) * U ≤ W * (W - 1) := by
      have hW1 : K + 2 ≤ W := by omega
      have hW2 : U ≤ W - 1 := by omega
      exact Nat.mul_le_mul hW1 hW2
    have : (K + 1) * U + 1 ≤ (K + 2) * U := by nlinarith
    omega
  have hQpos : 1 ≤ gridQ K N := gridQ_pos K N
  have hDm : gridDm K N = 1 + gridQ K N * ((K + 1) * U) := by
    unfold gridDm gridD₀
    rw [← hU]; ring_nf
  rw [hDm, pow_two]
  calc 1 + gridQ K N * ((K + 1) * U) ≤ gridQ K N * (1 + (K + 1) * U) := by nlinarith
    _ ≤ gridQ K N * gridQ K N := Nat.mul_le_mul_left _ (by omega)

lemma two_gridT_succ_le_gridQ {K N : ℕ} (hK : 1 ≤ K) : 2 * gridT K N + 1 ≤ gridQ K N := by
  set U := gridUmax K N with hU
  set W := U + K + N + 2 with hW
  have hHU : gridH K ≤ U := gridH_le_gridUmax (N := N) hK
  have hfac : W * (W - 1) ≤ gridQ K N := by
    have := mul_self_pred_le_factorial W
    simpa [gridQ, hW, hU] using this
  have h1 : 2 * (gridH K * N) + 1 ≤ W * (W - 1) := by
    have hW1 : gridH K + N + 2 ≤ W := by omega
    have hW2 : gridH K + N + 1 ≤ W - 1 := by omega
    have := Nat.mul_le_mul hW1 hW2
    nlinarith [Nat.zero_le (gridH K), Nat.zero_le N]
  rw [gridT]
  omega

theorem P₀_le_pow_gridQ {K N : ℕ} (hK : 1 ≤ K) (hN : 1 ≤ N) :
    (gridOf K N hK).P₀ ≤ gridQ K N ^ (7 * gridT K N ^ 2) := by
  have hQ1 : 1 ≤ gridQ K N := gridQ_pos K N
  have hDm := gridDm_le_gridQ_sq (K := K) (N := N) hK
  have hT : 2 * gridT K N + 1 ≤ gridQ K N := two_gridT_succ_le_gridQ (N := N) hK
  have hKN : K + N ≤ gridQ K N := by have := gridQ_gt K N; omega
  have hH2 : 2 ≤ gridH K := by
    unfold gridH
    calc 2 ≤ K ^ 2 + 1 := by nlinarith
      _ = (K ^ 2 + 1) ^ 1 := (pow_one _).symm
      _ ≤ (K ^ 2 + 1) ^ K := Nat.pow_le_pow_right (by omega) hK
  have hHT : gridH K ≤ gridT K N := by
    rw [gridT]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hT2 : 2 ≤ gridT K N := le_trans hH2 hHT
  have e1 : gridDm K N ^ (2 * gridH K) ≤ gridQ K N ^ (4 * gridH K) := by
    calc gridDm K N ^ (2 * gridH K) ≤ (gridQ K N ^ 2) ^ (2 * gridH K) :=
          Nat.pow_le_pow_left hDm _
      _ = gridQ K N ^ (4 * gridH K) := by rw [← pow_mul]; ring_nf
  have e2 : (2 * gridT K N + 1) ^ (2 * gridT K N + 1) ≤ gridQ K N ^ (2 * gridT K N + 1) :=
    Nat.pow_le_pow_left hT _
  have e3 : ((K + N) * gridDm K N) ^ (gridT K N ^ 2) ≤ gridQ K N ^ (3 * gridT K N ^ 2) := by
    calc ((K + N) * gridDm K N) ^ (gridT K N ^ 2)
        ≤ (gridQ K N * gridQ K N ^ 2) ^ (gridT K N ^ 2) :=
          Nat.pow_le_pow_left (Nat.mul_le_mul hKN hDm) _
      _ = gridQ K N ^ (3 * gridT K N ^ 2) := by
          rw [← pow_succ', ← pow_mul]
  have hexp : 4 * gridH K + (2 * gridT K N + 1) + 3 * gridT K N ^ 2 ≤ 7 * gridT K N ^ 2 := by
    nlinarith [hHT, hT2]
  calc (gridOf K N hK).P₀ ≤ gridP₀Bound K N := gridOf.P₀_le hK
    _ ≤ gridQ K N ^ (4 * gridH K) * gridQ K N ^ (2 * gridT K N + 1)
        * gridQ K N ^ (3 * gridT K N ^ 2) := by
        unfold gridP₀Bound
        exact Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3
    _ = gridQ K N ^ (4 * gridH K + (2 * gridT K N + 1) + 3 * gridT K N ^ 2) := by
        rw [← pow_add, ← pow_add]
    _ ≤ gridQ K N ^ (7 * gridT K N ^ 2) := Nat.pow_le_pow_right hQ1 hexp

/-! ### Monotonicity -/

lemma gridSum_mono {K K' B B' : ℕ} (hK : K ≤ K') (hB : B ≤ B') :
    gridSum K B ≤ gridSum K' B' := by
  have h1 : gridSum K B = ∑ i ∈ Finset.range K, B ^ (i + 1) := by
    rw [gridSum]; exact Fin.sum_univ_eq_sum_range (fun i => B ^ (i + 1)) K
  have h2 : gridSum K' B' = ∑ i ∈ Finset.range K', B' ^ (i + 1) := by
    rw [gridSum]; exact Fin.sum_univ_eq_sum_range (fun i => B' ^ (i + 1)) K'
  rw [h1, h2]
  calc ∑ i ∈ Finset.range K, B ^ (i + 1) ≤ ∑ i ∈ Finset.range K, B' ^ (i + 1) :=
        Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left hB _
    _ ≤ ∑ i ∈ Finset.range K', B' ^ (i + 1) :=
        Finset.sum_le_sum_of_subset (by intro x hx; simp only [Finset.mem_range] at *; omega)

lemma gridB_mono {K K' N N' : ℕ} (hK : K ≤ K') (hN : N ≤ N') : gridB K N ≤ gridB K' N' := by
  unfold gridB
  have : K ^ 2 * (K + N) ≤ K' ^ 2 * (K' + N') :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hK 2) (by omega)
  omega

lemma gridUmax_mono {K K' N N' : ℕ} (hK : K ≤ K') (hN : N ≤ N') :
    gridUmax K N ≤ gridUmax K' N' := by
  unfold gridUmax
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hK 2) (gridSum_mono hK (gridB_mono hK hN))

lemma gridQ_mono {K K' N N' : ℕ} (hK : K ≤ K') (hN : N ≤ N') : gridQ K N ≤ gridQ K' N' := by
  unfold gridQ
  exact Nat.factorial_le (by have := gridUmax_mono hK hN; omega)

/-! ### The growth -/

lemma small_le_pow_gridQ {A : ℕ} (hA : 1 ≤ A) :
    256 * A ^ 2 * gridDm A (N A) * gridH A ≤ gridQ A (N A) ^ 3 := by
  set U := gridUmax A (N A) with hU
  set H := gridH A with hH
  set W := U + A + N A + 2 with hW
  have hHU : H ≤ U := gridH_le_gridUmax (N := N A) hA
  have hNA : N A = 100 * A ^ 2 := rfl
  have hfac : W * (W - 1) ≤ gridQ A (N A) := by
    have := mul_self_pred_le_factorial W
    simpa [gridQ, hW, hU] using this
  have hkey : 256 * A ^ 2 * H ≤ gridQ A (N A) := by
    have hW1 : H + 100 * A ^ 2 ≤ W := by omega
    have hW2 : H + 100 * A ^ 2 ≤ W - 1 := by omega
    have hmul := Nat.mul_le_mul hW1 hW2
    have hZ : (256 : ℤ) * (A : ℤ) ^ 2 * (H : ℤ)
        ≤ ((H : ℤ) + 100 * (A : ℤ) ^ 2) * ((H : ℤ) + 100 * (A : ℤ) ^ 2) := by
      nlinarith [sq_nonneg ((H : ℤ) - 100 * (A : ℤ) ^ 2), sq_nonneg ((A : ℤ)),
        Int.natCast_nonneg H, Int.natCast_nonneg A]
    have : 256 * A ^ 2 * H ≤ (H + 100 * A ^ 2) * (H + 100 * A ^ 2) := by exact_mod_cast hZ
    omega
  have hDm := gridDm_le_gridQ_sq (K := A) (N := N A) hA
  calc 256 * A ^ 2 * gridDm A (N A) * H = (256 * A ^ 2 * H) * gridDm A (N A) := by ring
    _ ≤ gridQ A (N A) * gridQ A (N A) ^ 2 := Nat.mul_le_mul hkey hDm
    _ = gridQ A (N A) ^ 3 := by ring

lemma exponent_growth {K : ℕ} (hK : 2 ≤ K) :
    7 * gridT K (N K) ^ 2 + 3
      ≤ gridT (K + 4) (N (K + 4)) * (gridH (K + 4) - 1) := by
  set H := gridH K with hH
  set H' := gridH (K + 4) with hH'
  set c := (K ^ 2 + 1) ^ 4 with hc
  have hHc : H * c ≤ H' := by
    rw [hH, hH', hc, gridH, gridH, ← pow_add]
    exact Nat.pow_le_pow_left (by nlinarith) _
  have hH2 : 2 ≤ H' := by
    rw [hH', gridH]
    calc 2 ≤ (K + 4) ^ 2 + 1 := by nlinarith
      _ = ((K + 4) ^ 2 + 1) ^ 1 := (pow_one _).symm
      _ ≤ ((K + 4) ^ 2 + 1) ^ (K + 4) := Nat.pow_le_pow_right (by omega) (by omega)
  have hHpos : 1 ≤ H := by
    rw [hH, gridH]; exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hN : N K = 100 * K ^ 2 := rfl
  have hN' : N (K + 4) = 100 * (K + 4) ^ 2 := rfl
  have hNle : N K ≤ N (K + 4) := by rw [hN, hN']; nlinarith
  -- `2·T'(H'−1) ≥ H'²N'`
  have hstep1 : H' ^ 2 * N (K + 4) ≤ 2 * (gridT (K + 4) (N (K + 4)) * (H' - 1)) := by
    rw [gridT, ← hH']
    have h2 : H' ≤ 2 * (H' - 1) := by omega
    calc H' ^ 2 * N (K + 4) = H' * N (K + 4) * H' := by ring
      _ ≤ H' * N (K + 4) * (2 * (H' - 1)) := Nat.mul_le_mul_left _ h2
      _ = 2 * (H' * N (K + 4) * (H' - 1)) := by ring
  -- `H'²N' ≥ H²c²·N`
  have hstep2 : H ^ 2 * c ^ 2 * N K ≤ H' ^ 2 * N (K + 4) := by
    have h1 : (H * c) ^ 2 ≤ H' ^ 2 := Nat.pow_le_pow_left hHc 2
    calc H ^ 2 * c ^ 2 * N K = (H * c) ^ 2 * N K := by ring
      _ ≤ H' ^ 2 * N K := Nat.mul_le_mul_right _ h1
      _ ≤ H' ^ 2 * N (K + 4) := Nat.mul_le_mul_left _ hNle
  -- `c² ≥ 14·N + 6`
  have hcN : 14 * N K + 6 ≤ c ^ 2 := by
    have hKpow : (2 : ℕ) ^ 14 ≤ K ^ 14 := Nat.pow_le_pow_left hK 14
    have hc16 : K ^ 16 ≤ c ^ 2 := by
      rw [hc, ← pow_mul]
      calc K ^ 16 = (K ^ 2) ^ 8 := by rw [← pow_mul]
        _ ≤ (K ^ 2 + 1) ^ 8 := Nat.pow_le_pow_left (by omega) 8
    have hK2 : 4 ≤ K ^ 2 := by nlinarith
    have h16 : K ^ 16 = K ^ 2 * K ^ 14 := by rw [← pow_add]
    rw [hN]
    nlinarith [hKpow, hc16, hK2, h16]
  -- assemble
  have hfinal : 14 * (H * N K) ^ 2 + 6 ≤ H ^ 2 * c ^ 2 * N K := by
    have h1 : H ^ 2 * N K * (14 * N K + 6) ≤ H ^ 2 * N K * c ^ 2 :=
      Nat.mul_le_mul_left _ hcN
    have h2 : 1 ≤ H ^ 2 * N K := by
      have : 1 ≤ N K := by rw [hN]; nlinarith
      exact Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith [h1, h2]
  have : 14 * gridT K (N K) ^ 2 + 6 ≤ 2 * (gridT (K + 4) (N (K + 4)) * (H' - 1)) := by
    rw [gridT, ← hH]
    omega
  omega

/-- **THE GROWTH LEMMA.**  The modulus of level `K+4` dwarfs level `K`'s by more than the
band head's whole junk factor `256·(K+4)²·Dm(K+4)·|Atom(K+4)|`. -/
theorem P₀_growth {K : ℕ} (hK : 2 ≤ K) :
    256 * (K + 4) ^ 2 * gridDm (K + 4) (N (K + 4)) * gridH (K + 4)
        * (gridOf K (N K) (by omega : 1 ≤ K)).P₀
      ≤ (gridOf (K + 4) (N (K + 4)) (by omega : 1 ≤ K + 4)).P₀ := by
  have hQ' : 1 ≤ gridQ (K + 4) (N (K + 4)) := gridQ_pos _ _
  have hN1 : 1 ≤ N K := by show 1 ≤ 100 * K ^ 2; nlinarith
  have hmono : gridQ K (N K) ≤ gridQ (K + 4) (N (K + 4)) := by
    refine gridQ_mono (by omega) ?_
    show 100 * K ^ 2 ≤ 100 * (K + 4) ^ 2
    nlinarith
  calc 256 * (K + 4) ^ 2 * gridDm (K + 4) (N (K + 4)) * gridH (K + 4)
        * (gridOf K (N K) (by omega : 1 ≤ K)).P₀
      ≤ gridQ (K + 4) (N (K + 4)) ^ 3 * gridQ K (N K) ^ (7 * gridT K (N K) ^ 2) :=
        Nat.mul_le_mul (small_le_pow_gridQ (by omega)) (P₀_le_pow_gridQ (by omega) hN1)
    _ ≤ gridQ (K + 4) (N (K + 4)) ^ 3
          * gridQ (K + 4) (N (K + 4)) ^ (7 * gridT K (N K) ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmono _)
    _ = gridQ (K + 4) (N (K + 4)) ^ (3 + 7 * gridT K (N K) ^ 2) := by rw [← pow_add]
    _ ≤ gridQ (K + 4) (N (K + 4))
          ^ (gridT (K + 4) (N (K + 4)) * (gridH (K + 4) - 1)) := by
        refine Nat.pow_le_pow_right hQ' ?_
        have := exponent_growth hK
        omega
    _ ≤ _ := P₀_ge_pow (by omega)

end NormalNumbers.G4
