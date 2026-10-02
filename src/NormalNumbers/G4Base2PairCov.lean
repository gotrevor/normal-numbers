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

open Filter Topology in
lemma ev_L {c : ℝ} (hc : 0 < c) (A η : ℝ) (hη : 0 < η) {C₅ : ℝ} (hC₅ : 1 ≤ C₅) (X₀ : ℝ) :
    ∀ᶠ L in atTop, 1 ≤ L ∧ A ≤ L ^ c ∧ A * L ^ (-c) < η ∧ A / L < η ∧
      (C₅ * L) ^ ((1 : ℝ) / 10) ≤ C₅ * L / 101 ∧ X₀ ≤ Real.exp (C₅ * L) := by
  have h1 : ∀ᶠ L : ℝ in atTop, 1 ≤ L := eventually_ge_atTop 1
  have h2 : ∀ᶠ L : ℝ in atTop, A ≤ L ^ c := (tendsto_rpow_atTop hc).eventually_ge_atTop A
  have h3 : ∀ᶠ L : ℝ in atTop, A * L ^ (-c) < η := by
    have t : Tendsto (fun L : ℝ => A * L ^ (-c)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hc).const_mul A
    exact t.eventually (gt_mem_nhds hη)
  have h4 : ∀ᶠ L : ℝ in atTop, A / L < η := by
    have t : Tendsto (fun L : ℝ => A / L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    exact t.eventually (gt_mem_nhds hη)
  have hu : Tendsto (fun L : ℝ => C₅ * L) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith)
  have h5 : ∀ᶠ L : ℝ in atTop, (C₅ * L) ^ ((1 : ℝ) / 10) ≤ C₅ * L / 101 := by
    have t := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp hu).eventually_ge_atTop 101
    filter_upwards [t, hu.eventually_gt_atTop 0] with L hL hpos
    simp only [Function.comp] at hL
    have hsplit : C₅ * L = (C₅ * L) ^ ((1 : ℝ) / 10) * (C₅ * L) ^ ((9 : ℝ) / 10) := by
      rw [← Real.rpow_add hpos]; norm_num
    have hp : 0 ≤ (C₅ * L) ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hpos.le _
    rw [le_div_iff₀ (by norm_num)]
    calc (C₅ * L) ^ ((1 : ℝ) / 10) * 101 ≤ (C₅ * L) ^ ((1 : ℝ) / 10) * (C₅ * L) ^ ((9 : ℝ) / 10) :=
          mul_le_mul_of_nonneg_left hL hp
      _ = C₅ * L := hsplit.symm
  have h6 : ∀ᶠ L : ℝ in atTop, X₀ ≤ Real.exp (C₅ * L) :=
    (Real.tendsto_exp_atTop.comp hu).eventually_ge_atTop X₀
  filter_upwards [h1, h2, h3, h4, h5, h6] with L a b c d e f
  exact ⟨a, b, c, d, e, f⟩

lemma log_two_pow (a : ℕ) : Real.log ((2 : ℝ) ^ a) = a * Real.log 2 := by
  rw [Real.log_pow]

lemma two_pow_rpow_div (m : ℕ) :
    ((2 : ℝ) ^ (101 * 2 ^ m)) ^ ((1 : ℝ) / 101) = (2 : ℝ) ^ (2 ^ m) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
  congr 1; push_cast; ring

lemma two_pow_rpow_le {a j : ℕ} {t : ℝ} (ht : 0 ≤ t) (h : t * a ≤ j) :
    ((2 : ℝ) ^ a) ^ t ≤ (2 : ℝ) ^ j := by
  rw [← Real.rpow_natCast 2 a, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast 2 j]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

lemma mem_dyadicScales_two_pow {a j : ℕ} (h1 : a ≤ 2 * j) (h2 : j + 1 ≤ a) :
    j ∈ CastingOut.dyadicScales ((2 : ℝ) ^ a) := by
  unfold CastingOut.dyadicScales
  rw [mem_filter, mem_range]
  have hlog : Real.logb 2 ((2 : ℝ) ^ a) = a := by
    rw [← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hlog, Nat.ceil_natCast]; omega
  · rw [Real.sqrt_le_left (by positivity)]
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · exact pow_le_pow_right₀ (by norm_num) h2

lemma card_dyadicScales_two_pow (a : ℕ) :
    (CastingOut.dyadicScales ((2 : ℝ) ^ a)).card ≤ a + 1 := by
  unfold CastingOut.dyadicScales
  have hlog : Real.logb 2 ((2 : ℝ) ^ a) = a := by
    rw [← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num)]
  refine (card_filter_le _ _).trans ?_
  rw [card_range, hlog, Nat.ceil_natCast]

lemma aux_blk {C Lc P L r H t s η : ℝ} (hP : 0 ≤ P) (hL : 0 < L) (hs : 0 < s) (hst : s ≤ t)
    (hr : r ≤ H) (hr0 : 0 ≤ r) (hC : 0 ≤ C) (hLc : 0 ≤ Lc) (hη : 0 < η)
    (h1 : (C + 3 * P) * Lc < η / 4) (h2 : (C + 3 * P) / L < η / 4)
    (h3 : 12 * P * (2 * H + 6) / η ≤ s) :
    C * Lc + 3 * (P / t * (t / L + 2 * r + 6)) ≤ η := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have e : P / t * (t / L + 2 * r + 6) = P / L + P * (2 * r + 6) / t := by
    field_simp; ring
  rw [e]
  have a1 : C * Lc ≤ (C + 3 * P) * Lc := by nlinarith
  have a2 : 3 * (P / L) ≤ (C + 3 * P) / L := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hL]; linarith
  have a3 : 3 * (P * (2 * r + 6) / t) ≤ η / 4 := by
    rw [div_le_iff₀ hη] at h3
    rw [mul_div_assoc', div_le_iff₀ ht]
    have : P * (2 * r + 6) ≤ P * (2 * H + 6) := by nlinarith
    nlinarith
  linarith

lemma aux_Px {P ε t s : ℝ} (hP : 0 ≤ P) (hε : 0 < ε) (hs : 0 < s) (h1 : 288 * P / ε ≤ t)
    (h2 : t ≤ s) : 6 * 16 * P / s ≤ ε / 3 := by
  rw [div_le_iff₀ hs]
  rw [div_le_iff₀ hε] at h1
  nlinarith

/-- The good-`L` conditions used per threshold in `binPair_cov`. -/
def GoodL (c C₅ X₀ A η L : ℝ) : Prop :=
  1 ≤ L ∧ A ≤ L ^ c ∧ A * L ^ (-c) < η ∧ A / L < η ∧
    (C₅ * L) ^ ((1 : ℝ) / 10) ≤ C₅ * L / 101 ∧ X₀ ≤ Real.exp (C₅ * L)

/-- **N6 core at a given cutoff.**  TT's constants `c, Cst`, N5's `C₅' ≤ C₅, X₀`, the three
good-`L` conditions at `L = 101·2^{mE}·log 2 / C₅`, and `Z ≤ 2^{mE}`. -/
theorem binPair_cov_core {c Cst : ℝ} (hc : 0 < c) (hCst : 0 < Cst)
    (hTT : ∀ g₁ g₂ : ℕ → ℂ, CastingOut.IsCoprimeMultiplicativeNat g₁ →
      CastingOut.IsCoprimeMultiplicativeNat g₂ →
      (∀ n, ‖g₁ n‖ ≤ 1) → (∀ n, ‖g₂ n‖ ≤ 1) → (∀ n, (g₁ n).im = 0) →
      ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X → ∀ δ : ℝ → ℝ,
        (∀ N : ℝ, X ^ (0.4 : ℝ) ≤ N → N ≤ X → ∀ a q : ℕ, 1 ≤ q →
          ‖(∑ n ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q), g₁ n)
              - (((N / q) * δ N : ℝ) : ℂ)‖ ≤ N / L) →
        (∀ p : ℕ, p.Prime → Real.exp (Real.log X ^ ((1 : ℝ) / 11)) ≤ p →
          (p : ℝ) ≤ Real.exp (Real.log X ^ ((1 : ℝ) / 10)) → g₁ p = 1) →
        ∃ E : Finset ℕ, E ⊆ CastingOut.dyadicScales X ∧
          (E.card : ℝ) ≤ Cst * L ^ (-c) * ((CastingOut.dyadicScales X).card : ℝ) ∧
          ∀ j ∈ CastingOut.dyadicScales X, j ∉ E →
            ∀ N : ℕ, (2 : ℝ) ^ j ≤ (N : ℝ) → (N : ℝ) < 2 ^ (j + 1) →
              ∀ W b h₁ h₂ : ℕ, 0 < W → (W : ℝ) ≤ L ^ c →
                (h₁ : ℝ) ≤ L ^ c → (h₂ : ℝ) ≤ L ^ c → h₁ ≠ h₂ →
                ‖((W : ℝ) / (N : ℝ) : ℝ) •
                    ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % W = b % W),
                      (g₁ (n + h₁) - ((δ N : ℝ) : ℂ)) * g₂ (n + h₂)‖
                  ≤ Cst * L ^ (-c))
    {C₅' C₅ X₀ : ℝ} (hC₅' : 0 < C₅') (hC₅1 : 1 ≤ C₅) (hC₅C : C₅' ≤ C₅)
    (h5 : ∀ X : ℝ, X₀ ≤ X → ∀ Y : ℝ,
      X ^ ((1 : ℝ) / 101) ≤ Y → ∀ I : Finset ℕ, (∀ p ∈ I, p.Prime ∧ Y < p) →
      ∀ N : ℝ, X ^ (0.4 : ℝ) ≤ N → N ≤ X → ∀ a q : ℕ, 1 ≤ q →
        ‖(∑ n ∈ (Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q), binInd I n)
            - (((N / q) * binDelta I N : ℝ) : ℂ)‖ ≤ N / (Real.log X / C₅'))
    (K N : ℕ) (hK : 1 ≤ K) {ε₂ : ℝ} (hε : 0 < ε₂) (Bmax J₀ : ℕ)
    (hJ₀ : (1 / 2 : ℝ) ^ J₀ < ε₂ / 96) (e : ℕ)
    (hev : GoodL c C₅ X₀ (((gridOf K N hK).P₀ + (K + N) * gridDm K N : ℕ) : ℝ) (ε₂ / 6)
        (101 * 2 ^ SchedB.mE K e * Real.log 2 / C₅) ∧
      GoodL c C₅ X₀ (J₀ * Bmax ^ 2 * Cst * 102 + 1 : ℝ) 1
        (101 * 2 ^ SchedB.mE K e * Real.log 2 / C₅) ∧
      GoodL c C₅ X₀ (Cst + 3 * (gridOf K N hK).P₀ : ℝ) (ε₂ / 6 / 4)
        (101 * 2 ^ SchedB.mE K e * Real.log 2 / C₅))
    (hmZ : J₀ + (K + N) * gridDm K N + 2 * (gridOf K N hK).P₀
        + ⌈12 * ((gridOf K N hK).P₀ : ℝ) * (2 * (((K + N) * gridDm K N : ℕ) : ℝ) + 6) / (ε₂ / 6)⌉₊
        + ⌈288 * (gridOf K N hK).P₀ / ε₂⌉₊ + 1 ≤ 2 ^ SchedB.mE K e) :
    ∀ B ≤ Bmax,
      ∀ bins : Fin B → Finset ℕ, (∀ ℓ, ∀ p ∈ bins ℓ, p.Prime ∧ SchedB.YE K e < p) → (∀ ℓ, mass (bins ℓ) ≤ 1) →
      ∃ x : ℕ, 100 * 2 ^ SchedB.mE K e ≤ x ∧ x ≤ 101 * 2 ^ SchedB.mE K e ∧
        ∀ ℓ ℓ' : Fin B, ∀ i j : (gridOf K N hK).Idx, i ≠ j →
          |((apSample (2 ^ x) (gridOf K N hK).P₀ (gridOf K N hK).b₀).card : ℝ)⁻¹ *
            ∑ n ∈ apSample (2 ^ x) (gridOf K N hK).P₀ (gridOf K N hK).b₀,
              ((binInd (bins ℓ) (n + shiftAL (gridOf K N hK).B (gridOf K N hK).Q
                  (gridOf K N hK).D₀ i)).re - binDelta (bins ℓ) (dyBase n))
              * ((binInd (bins ℓ') (n + shiftAL (gridOf K N hK).B (gridOf K N hK).Q
                  (gridOf K N hK).D₀ j)).re - binDelta (bins ℓ') (dyBase n))| ≤ ε₂ := by
  classical
  intro B hB bins hbins hmass
  set G := gridOf K N hK with hG
  set P₀ : ℕ := G.P₀ with hP₀def
  have hP₀ : 0 < P₀ := G.P₀_pos
  have hb₀ : G.b₀ < P₀ := G.b₀_lt_P₀
  set Hs : ℕ := (K + N) * gridDm K N with hHs
  have hρle : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ Hs := fun i => gridOf.shiftAL_le hK i
  set η : ℝ := ε₂ / 6 with hη
  have hη0 : 0 < η := by positivity
  set m := SchedB.mE K e with hm
  have hme : e ≤ m := by rw [hm]; unfold SchedB.mE; omega
  have hm2 : m < 2 ^ m := Nat.lt_two_pow_self
  set Z : ℕ := J₀ + Hs + 2 * P₀ + ⌈12 * P₀ * (2 * Hs + 6) / η⌉₊ + ⌈288 * P₀ / ε₂⌉₊ + 1 with hZ
  have hmZ : Z ≤ 2 ^ m := hmZ
  obtain ⟨⟨hL1, hPL, -, hPL', hsm, hX₀⟩, ⟨-, -, hJL, -, -, -⟩, ⟨-, -, hCL, hCL', -, -⟩⟩ := hev
  set L : ℝ := 101 * 2 ^ m * Real.log 2 / C₅ with hL
  set a : ℕ := 101 * 2 ^ m with ha
  set XT : ℝ := (2 : ℝ) ^ a with hXT
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogXT : Real.log XT = C₅ * L := by
    rw [hXT, log_two_pow, hL, ha]; push_cast; field_simp
  have hLpos : 0 < L := by linarith
  have hYreal : ((SchedB.YE K e : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ m) := by
    unfold SchedB.YE; push_cast; rfl
  have hXT2 : (2 : ℝ) ≤ XT := by
    rw [hXT]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) (by rw [ha]; have := Nat.one_le_two_pow (n := m); omega)
  have hX₀XT : X₀ ≤ XT := by
    rw [← Real.exp_log (show 0 < XT by positivity), hlogXT]; exact hX₀
  have hXTY : XT ^ ((1 : ℝ) / 101) ≤ ((SchedB.YE K e : ℕ) : ℝ) := by
    rw [hYreal, hXT, ha, two_pow_rpow_div]
  have hbinsR : ∀ ℓ, ∀ p ∈ bins ℓ, p.Prime ∧ ((SchedB.YE K e : ℕ) : ℝ) < p := fun ℓ p hp =>
    ⟨(hbins ℓ p hp).1, by exact_mod_cast (hbins ℓ p hp).2⟩
  -- TT's hypothesis (3.1) for each bin, with `L`
  have h31 : ∀ ℓ, ∀ N' : ℝ, XT ^ (0.4 : ℝ) ≤ N' → N' ≤ XT → ∀ a' q : ℕ, 1 ≤ q →
      ‖(∑ n ∈ (Ioc ⌊N'⌋₊ ⌊2 * N'⌋₊).filter (fun n => n % q = a' % q), binInd (bins ℓ) n)
          - (((N' / q) * binDelta (bins ℓ) N' : ℝ) : ℂ)‖ ≤ N' / L := by
    intro ℓ N' hN1 hN2 a' q hq
    refine (h5 XT hX₀XT _ hXTY (bins ℓ) (hbinsR ℓ) N' hN1 hN2 a' q hq).trans ?_
    have hN0 : 0 ≤ N' := le_trans (Real.rpow_nonneg (by positivity) _) hN1
    rw [hlogXT]
    refine div_le_div_of_nonneg_left hN0 hLpos ?_
    rw [le_div_iff₀ hC₅']
    nlinarith
  -- small primes: `g_ℓ(p) = 1`
  have hsmall : ∀ ℓ, ∀ p : ℕ, p.Prime → Real.exp (Real.log XT ^ ((1 : ℝ) / 11)) ≤ p →
      (p : ℝ) ≤ Real.exp (Real.log XT ^ ((1 : ℝ) / 10)) → binInd (bins ℓ) p = 1 := by
    intro ℓ p hp _ hp2
    have hpY : (p : ℝ) ≤ ((SchedB.YE K e : ℕ) : ℝ) := by
      refine hp2.trans ?_
      rw [hlogXT, hYreal]
      have : C₅ * L / 101 = 2 ^ m * Real.log 2 := by rw [hL]; field_simp
      calc Real.exp ((C₅ * L) ^ ((1 : ℝ) / 10)) ≤ Real.exp (C₅ * L / 101) :=
            Real.exp_le_exp.2 hsm
        _ = (2 : ℝ) ^ (2 ^ m) := by
            rw [this]
            have h := log_two_pow (2 ^ m)
            push_cast at h
            rw [← h, Real.exp_log (by positivity)]
    unfold binInd
    rw [if_neg]
    rintro ⟨q, hq, hqp⟩
    have hq' := hbinsR ℓ q hq
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq'.1 hp).1 hqp
    subst this
    linarith [hq'.2]
  -- TT, once per bin pair
  have hE : ∀ pr : Fin B × Fin B, ∃ E : Finset ℕ, E ⊆ CastingOut.dyadicScales XT ∧
      (E.card : ℝ) ≤ Cst * L ^ (-c) * ((CastingOut.dyadicScales XT).card : ℝ) ∧
      ∀ j ∈ CastingOut.dyadicScales XT, j ∉ E →
        ∀ N' : ℕ, (2 : ℝ) ^ j ≤ (N' : ℝ) → (N' : ℝ) < 2 ^ (j + 1) →
          ∀ W b h₁ h₂ : ℕ, 0 < W → (W : ℝ) ≤ L ^ c →
            (h₁ : ℝ) ≤ L ^ c → (h₂ : ℝ) ≤ L ^ c → h₁ ≠ h₂ →
            ‖((W : ℝ) / (N' : ℝ) : ℝ) •
                ∑ n ∈ (Finset.Ioc N' (2 * N')).filter (fun n => n % W = b % W),
                  (binInd (bins pr.1) (n + h₁) - ((binDelta (bins pr.1) (N' : ℝ) : ℝ) : ℂ))
                    * binInd (bins pr.2) (n + h₂)‖
              ≤ Cst * L ^ (-c) := fun pr =>
    hTT (binInd (bins pr.1)) (binInd (bins pr.2))
      (binInd_isCoprimeMultiplicative _ fun p hp => (hbins pr.1 p hp).1)
      (binInd_isCoprimeMultiplicative _ fun p hp => (hbins pr.2 p hp).1)
      (norm_binInd_le _) (norm_binInd_le _) (binInd_im _) XT L hXT2 hL1
      (by rw [hlogXT]; nlinarith) (binDelta (bins pr.1)) (h31 pr.1) (hsmall pr.1)
  choose Ef hEsub hEcard hEgood using hE
  set U := univ.biUnion Ef with hU
  have hLc0 : 0 ≤ L ^ (-c) := Real.rpow_nonneg hLpos.le _
  have hscal : ((CastingOut.dyadicScales XT).card : ℝ) ≤ 102 * 2 ^ m := by
    have h := card_dyadicScales_two_pow a
    have h' : ((CastingOut.dyadicScales XT).card : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by
      rw [hXT]; exact_mod_cast h
    have h1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    rw [ha] at h'; push_cast at h'; linarith
  have hUcard : (U.card : ℝ) ≤ (B : ℝ) ^ 2 * (Cst * L ^ (-c) * (102 * 2 ^ m)) := by
    have h1 : (U.card : ℝ) ≤ ∑ pr : Fin B × Fin B, ((Ef pr).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    refine h1.trans ?_
    calc ∑ pr : Fin B × Fin B, ((Ef pr).card : ℝ)
        ≤ ∑ _pr : Fin B × Fin B, Cst * L ^ (-c) * (102 * 2 ^ m) :=
          sum_le_sum fun pr _ => (hEcard pr).trans (by gcongr)
      _ = (B : ℝ) ^ 2 * (Cst * L ^ (-c) * (102 * 2 ^ m)) := by
          rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hJU : J₀ * U.card < 2 ^ m + 1 := by
    have hBr : (B : ℝ) ≤ Bmax := by exact_mod_cast hB
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    have hm0 : (0 : ℝ) < 2 ^ m := by positivity
    have hJ0 : (0 : ℝ) ≤ J₀ := Nat.cast_nonneg _
    have key : (J₀ : ℝ) * U.card < 2 ^ m := by
      calc (J₀ : ℝ) * U.card ≤ J₀ * ((B : ℝ) ^ 2 * (Cst * L ^ (-c) * (102 * 2 ^ m))) :=
            mul_le_mul_of_nonneg_left hUcard hJ0
        _ ≤ J₀ * ((Bmax : ℝ) ^ 2 * (Cst * L ^ (-c) * (102 * 2 ^ m))) := by gcongr
        _ = (J₀ * Bmax ^ 2 * Cst * 102) * L ^ (-c) * 2 ^ m := by ring
        _ ≤ (J₀ * Bmax ^ 2 * Cst * 102 + 1) * L ^ (-c) * 2 ^ m := by gcongr; linarith
        _ < 1 * 2 ^ m := mul_lt_mul_of_pos_right hJL hm0
        _ = 2 ^ m := one_mul _
    have : ((J₀ * U.card : ℕ) : ℝ) < ((2 ^ m + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨x, hx1, hx2, hgood⟩ := exists_good_x U (100 * 2 ^ m) (2 ^ m + 1) J₀ hJU
  refine ⟨x, hx1, by omega, ?_⟩
  intro ℓ ℓ' i j hij
  have hδb : ∀ ℓ₁ : Fin B, ∀ N' : ℝ, |binDelta (bins ℓ₁) N'| ≤ 3 := by
    intro ℓ₁ N'
    exact abs_binDelta_le (bins ℓ₁) (fun p hp => (hbins ℓ₁ p hp).1) (hmass ℓ₁) N'
  set ρ := fun i : G.Idx => shiftAL G.B G.Q G.D₀ i with hρ
  have hF : ∀ n, |((binInd (bins ℓ) (n + ρ i)).re - binDelta (bins ℓ) (dyBase n))
      * ((binInd (bins ℓ') (n + ρ j)).re - binDelta (bins ℓ') (dyBase n))| ≤ 16 := by
    intro n
    have a1 := abs_re_binInd_le (bins ℓ) (n + ρ i)
    have a2 := abs_re_binInd_le (bins ℓ') (n + ρ j)
    have d1 := hδb ℓ (dyBase n)
    have d2 := hδb ℓ' (dyBase n)
    rw [abs_mul]
    have e1 : |(binInd (bins ℓ) (n + ρ i)).re - binDelta (bins ℓ) (dyBase n)| ≤ 4 :=
      (abs_sub _ _).trans (by linarith)
    have e2 : |(binInd (bins ℓ') (n + ρ j)).re - binDelta (bins ℓ') (dyBase n)| ≤ 4 :=
      (abs_sub _ _).trans (by linarith)
    exact (mul_le_mul e1 e2 (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hmx : m ≤ x - J₀ := by omega
  have hZη : 12 * P₀ * (2 * Hs + 6) / η ≤ (2 : ℝ) ^ m := by
    have h1 : 12 * P₀ * (2 * Hs + 6) / η ≤ (⌈12 * P₀ * (2 * Hs + 6) / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈12 * P₀ * (2 * Hs + 6) / η⌉₊ ≤ 2 ^ m := by omega
    have h3 : ((⌈12 * P₀ * (2 * Hs + 6) / η⌉₊ : ℕ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3; linarith
  have hZε : 288 * P₀ / ε₂ ≤ (2 : ℝ) ^ m := by
    have h1 : 288 * P₀ / ε₂ ≤ (⌈288 * P₀ / ε₂⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈288 * P₀ / ε₂⌉₊ ≤ 2 ^ m := by omega
    have h3 : ((⌈288 * P₀ / ε₂⌉₊ : ℕ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3; linarith
  have hblk : ∀ k, x - J₀ ≤ k → k < x → |(P₀ : ℝ) / 2 ^ k * blockSum2 (fun n =>
        ((binInd (bins ℓ) (n + ρ i)).re - binDelta (bins ℓ) (dyBase n))
        * ((binInd (bins ℓ') (n + ρ j)).re - binDelta (bins ℓ') (dyBase n))) P₀ G.b₀ k| ≤ η := by
    intro k hk1 hk2
    have hkU : k ∉ U := hgood k hk1 hk2
    have hkE : k ∉ Ef (ℓ, ℓ') := fun h => hkU (mem_biUnion.2 ⟨(ℓ, ℓ'), mem_univ _, h⟩)
    have hJm : J₀ ≤ 2 ^ m := by omega
    have hka1 : a ≤ 2 * k := by rw [ha]; omega
    have hka2 : k + 1 ≤ a := by rw [ha]; omega
    have hks : k ∈ CastingOut.dyadicScales XT := by
      rw [hXT]; exact mem_dyadicScales_two_pow hka1 hka2
    have hmk : m ≤ k := by omega
    have hρHs : ∀ i' : G.Idx, ρ i' ≤ Hs := hρle
    have hHsk : Hs ≤ 2 ^ k := by
      have : 2 ^ m ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hmk
      omega
    have hPHs : ((P₀ + Hs : ℕ) : ℝ) ≤ L ^ c := hPL
    have hP₀L : (P₀ : ℝ) ≤ L ^ c := le_trans (by exact_mod_cast Nat.le_add_right _ _) hPHs
    have hρL : ∀ i' : G.Idx, (ρ i' : ℝ) ≤ L ^ c := fun i' =>
      le_trans (by exact_mod_cast (hρHs i').trans (Nat.le_add_left _ _)) hPHs
    have hρne : ρ i ≠ ρ j := fun h => hij (G.ρ_injective h)
    have hTTk := hEgood (ℓ, ℓ') k hks hkE (2 ^ k) (by push_cast; exact le_rfl)
      (by push_cast; exact pow_lt_pow_right₀ (by norm_num) (by omega))
      P₀ G.b₀ (ρ i) (ρ j) hP₀ hP₀L (hρL i) (hρL j) hρne
    have h2k : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
    have hXT04 : XT ^ (0.4 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      rw [h2k]
      have h : (0.4 : ℝ) * (a : ℝ) ≤ (k : ℝ) := by
        have : (a : ℝ) ≤ 2 * k := by exact_mod_cast hka1
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        linarith
      exact two_pow_rpow_le (by norm_num) h
    have hkXT : ((2 ^ k : ℕ) : ℝ) ≤ XT := by
      rw [h2k]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hN5 := h31 ℓ ((2 ^ k : ℕ) : ℝ) hXT04 hkXT (G.b₀ + ρ i) P₀ hP₀
    have hfl1 : ⌊((2 ^ k : ℕ) : ℝ)⌋₊ = 2 ^ k := Nat.floor_natCast _
    have hfl2 : ⌊2 * ((2 ^ k : ℕ) : ℝ)⌋₊ = 2 * 2 ^ k := by
      rw [show (2 : ℝ) * ((2 ^ k : ℕ) : ℝ) = ((2 * 2 ^ k : ℕ) : ℝ) by push_cast; ring]
      exact Nat.floor_natCast _
    rw [hfl1, hfl2] at hN5
    have hgb := good_block_bound (bins ℓ) (bins ℓ') P₀ G.b₀ k (ρ i) (ρ j) hP₀ hb₀
      ((hρHs i).trans hHsk) (E := ((2 ^ k : ℕ) : ℝ) / L) (by positivity)
      (hδb ℓ _) (hδb ℓ' _) hTTk hN5
    refine hgb.trans ?_
    rw [h2k]
    have hs2 : (2 : ℝ) ^ m ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hmk
    have hρr : (ρ i : ℝ) ≤ Hs := by exact_mod_cast hρHs i
    have hC0 : (0 : ℝ) ≤ Cst := hCst.le
    exact aux_blk (Nat.cast_nonneg _) hLpos (by positivity) hs2 hρr (Nat.cast_nonneg _) hC0
      hLc0 hη0 hCL hCL' hZη
  have hfin := abs_avg_le_blocks _ hF hP₀ hb₀ (by omega)
    (show 2 * P₀ ≤ 2 ^ x by
      have : 2 ^ m ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega) hη0.le hblk
  refine hfin.trans ?_
  have hxm : (2 : ℝ) ^ m ≤ 2 ^ x := pow_le_pow_right₀ (by norm_num) (by omega)
  have hPx : 6 * 16 * (P₀ : ℝ) / 2 ^ x ≤ ε₂ / 3 :=
    aux_Px (Nat.cast_nonneg _) hε (by positivity) hZε hxm
  have hJ : 2 * 16 * (1 / 2 : ℝ) ^ J₀ ≤ ε₂ / 3 := by linarith
  linarith


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
  classical
  obtain ⟨c, Cst, hc, hCst, hTT⟩ := htt
  obtain ⟨C₅', X₀, hC₅', h5⟩ := binInd_ap_mean
  set C₅ : ℝ := max C₅' 1 with hC₅def
  have hC₅1 : 1 ≤ C₅ := le_max_right _ _
  have hC₅C : C₅' ≤ C₅ := le_max_left _ _
  set G := gridOf K N hK with hG
  set P₀ : ℕ := G.P₀ with hP₀def
  have hP₀ : 0 < P₀ := G.P₀_pos
  have hb₀ : G.b₀ < P₀ := G.b₀_lt_P₀
  set Hs : ℕ := (K + N) * gridDm K N with hHs
  have hρle : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ Hs := fun i => gridOf.shiftAL_le hK i
  set η : ℝ := ε₂ / 6 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨J₀, hJ₀⟩ := exists_pow_lt_of_lt_one (show 0 < ε₂ / 96 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  -- asymptotics in `L`
  have hevL : ∀ᶠ L : ℝ in Filter.atTop,
      (1 ≤ L ∧ ((P₀ + Hs : ℕ) : ℝ) ≤ L ^ c ∧ ((P₀ + Hs : ℕ) : ℝ) * L ^ (-c) < η ∧
        ((P₀ + Hs : ℕ) : ℝ) / L < η ∧ (C₅ * L) ^ ((1 : ℝ) / 10) ≤ C₅ * L / 101 ∧
        X₀ ≤ Real.exp (C₅ * L)) ∧
      (1 ≤ L ∧ (J₀ * Bmax ^ 2 * Cst * 102 + 1 : ℝ) ≤ L ^ c ∧
        (J₀ * Bmax ^ 2 * Cst * 102 + 1 : ℝ) * L ^ (-c) < 1 ∧
        (J₀ * Bmax ^ 2 * Cst * 102 + 1 : ℝ) / L < 1 ∧ (C₅ * L) ^ ((1 : ℝ) / 10) ≤ C₅ * L / 101 ∧
        X₀ ≤ Real.exp (C₅ * L)) ∧
      (1 ≤ L ∧ (Cst + 3 * P₀ : ℝ) ≤ L ^ c ∧ (Cst + 3 * P₀ : ℝ) * L ^ (-c) < η / 4 ∧
        (Cst + 3 * P₀ : ℝ) / L < η / 4 ∧ (C₅ * L) ^ ((1 : ℝ) / 10) ≤ C₅ * L / 101 ∧
        X₀ ≤ Real.exp (C₅ * L)) :=
    (ev_L hc _ η hη0 hC₅1 X₀).and ((ev_L hc _ 1 one_pos hC₅1 X₀).and
      (ev_L hc _ (η / 4) (by positivity) hC₅1 X₀))
  have hLm : Filter.Tendsto (fun m : ℕ => (101 * 2 ^ m * Real.log 2) / C₅) Filter.atTop
      Filter.atTop := by
    have h2 : Filter.Tendsto (fun m : ℕ => (2 : ℝ) ^ m) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hl : (0 : ℝ) < 101 * Real.log 2 / C₅ := by
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
    refine (h2.const_mul_atTop hl).congr fun m => ?_
    ring
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 (hLm.eventually hevL)
  set Z : ℕ := J₀ + Hs + 2 * P₀ + ⌈12 * P₀ * (2 * Hs + 6) / η⌉₊ + ⌈288 * P₀ / ε₂⌉₊ + 1 with hZ
  refine ⟨m₀ + Z, fun e he => ?_⟩
  set m := SchedB.mE K e with hm
  have hme : e ≤ m := by rw [hm]; unfold SchedB.mE; omega
  have hm2 : m < 2 ^ m := Nat.lt_two_pow_self
  exact binPair_cov_core hc hCst hTT hC₅' hC₅1 hC₅C h5 K N hK hε Bmax J₀ hJ₀ e
    (hm₀ m (by omega)) (show Z ≤ 2 ^ m by omega)

end NormalNumbers.G4.Base2
