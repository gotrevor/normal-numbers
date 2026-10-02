/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2PairCov

/-!
# N6, effective: explicit good-`L` threshold and `binPair_cov_eff`
-/
open Finset
namespace NormalNumbers.G4.Base2

lemma goodL_of_ge {c C₅ X₀ : ℝ} (hc : 0 < c) (hC₅ : 1 ≤ C₅) {k : ℕ} (hk : 1 ≤ (k : ℝ) * c)
    (hk1 : 1 ≤ k) {D : ℝ} (hD : (101 : ℝ) ^ 10 ≤ D) (hDX : X₀ ≤ D) {A η L : ℝ} (hA : 0 ≤ A)
    (hη : 0 < η) (hη1 : η ≤ 1) (hL : D * (2 * (A + 1) / η) ^ k ≤ L) : GoodL c C₅ X₀ A η L := by
  set u := 2 * (A + 1) / η with hu
  have hu2 : 2 * (A + 1) ≤ u := by
    rw [hu, le_div_iff₀ hη]; nlinarith
  have hu1 : 1 ≤ u := by linarith
  have hD1 : 1 ≤ D := le_trans (one_le_pow₀ (by norm_num)) hD
  have huk : u ≤ u ^ k := by
    calc u = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ k := pow_le_pow_right₀ hu1 hk1
  have hukL : u ^ k ≤ L := le_trans (le_mul_of_one_le_left (by positivity) hD1) hL
  have huL : u ≤ L := huk.trans hukL
  have hDL : D ≤ L := le_trans (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hu1)) hL
  have hL1 : 1 ≤ L := hD1.trans hDL
  have hL0 : 0 < L := by linarith
  have hLc : u ≤ L ^ c := by
    have e : (u ^ k) ^ c = u ^ ((k : ℝ) * c) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    calc u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
      _ ≤ u ^ ((k : ℝ) * c) := Real.rpow_le_rpow_of_exponent_le hu1 hk
      _ = (u ^ k) ^ c := e.symm
      _ ≤ L ^ c := Real.rpow_le_rpow (by positivity) hukL hc.le
  have hLcpos : 0 < L ^ c := Real.rpow_pos_of_pos hL0 c
  have huη : u * η = 2 * (A + 1) := by rw [hu]; field_simp
  refine ⟨hL1, by linarith, ?_, ?_, ?_, ?_⟩
  · rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, div_lt_iff₀ hLcpos]
    calc A < u * η := by rw [huη]; linarith
      _ ≤ η * L ^ c := by nlinarith
  · rw [div_lt_iff₀ hL0]
    have : u * η ≤ η * L := by nlinarith
    linarith
  · set y := C₅ * L with hy
    have hyD : (101 : ℝ) ^ 10 ≤ y := by
      have : L ≤ y := by rw [hy]; nlinarith
      linarith
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hyD
    have h101 : (101 : ℝ) ≤ y ^ ((1 : ℝ) / 10) := by
      have : ((101 : ℝ) ^ 10) ^ ((1 : ℝ) / 10) = 101 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [← this]
      exact Real.rpow_le_rpow (by positivity) hyD (by norm_num)
    have hy1 : 1 ≤ y := le_trans (one_le_pow₀ (by norm_num)) hyD
    have h9 : y ^ ((1 : ℝ) / 10) ≤ y ^ ((9 : ℝ) / 10) :=
      Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
    have hsplit : y = y ^ ((1 : ℝ) / 10) * y ^ ((9 : ℝ) / 10) := by
      rw [← Real.rpow_add hy0]; norm_num
    rw [le_div_iff₀ (by norm_num)]
    have hp : 0 ≤ y ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hy0.le _
    calc y ^ ((1 : ℝ) / 10) * 101 ≤ y ^ ((1 : ℝ) / 10) * y ^ ((9 : ℝ) / 10) :=
          mul_le_mul_of_nonneg_left (h101.trans h9) hp
      _ = y := hsplit.symm
  · have : L ≤ C₅ * L := by nlinarith
    have := Real.add_one_le_exp (C₅ * L)
    linarith

lemma ub_one {P H Q ε Cst : ℝ} (hP : 0 ≤ P) (hH : 0 ≤ H) (hPHQ : P + H + 1 ≤ Q)
    (hεQ : 1 / ε ≤ Q) (hε : 0 < ε) (hQ1 : 1 ≤ Q) (hCst : 0 < Cst) :
    2 * ((P + H) + 1) / (ε / 6) ≤ (1632 * Cst + 200) * Q ^ 3 := by
  have e1 : 2 * ((P + H) + 1) / (ε / 6) = 12 * (P + H + 1) * (1 / ε) := by field_simp; ring
  rw [e1]
  have hQ2 : Q ^ 2 ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hCQ : 0 ≤ Cst * Q ^ 3 := by positivity
  calc 12 * (P + H + 1) * (1 / ε) ≤ 12 * Q * Q := by gcongr
    _ = 12 * Q ^ 2 := by ring
    _ ≤ (1632 * Cst + 200) * Q ^ 3 := by nlinarith

lemma ub_two {J B Q Cst : ℝ} (hJ0 : 0 ≤ J) (hB0 : 0 ≤ B) (hJ : J ≤ 8 * Q) (hB : B ≤ Q)
    (hQ1 : 1 ≤ Q) (hCst : 0 < Cst) :
    2 * (J * B ^ 2 * Cst * 102 + 1 + 1) / 1 ≤ (1632 * Cst + 200) * Q ^ 3 := by
  have hB2 : B ^ 2 ≤ Q ^ 2 := by gcongr
  have h1 : (1 : ℝ) ≤ Q ^ 3 := one_le_pow₀ hQ1
  have h2 : J * B ^ 2 ≤ 8 * Q * Q ^ 2 := mul_le_mul hJ hB2 (by positivity) (by linarith)
  have h3 : Cst * (J * B ^ 2) ≤ Cst * (8 * Q ^ 3) := by
    apply mul_le_mul_of_nonneg_left _ hCst.le
    calc J * B ^ 2 ≤ 8 * Q * Q ^ 2 := h2
      _ = 8 * Q ^ 3 := by ring
  nlinarith

lemma ub_three {P Q ε Cst : ℝ} (hP : 0 ≤ P) (hPQ : P + 1 ≤ Q)
    (hεQ : 1 / ε ≤ Q) (hε : 0 < ε) (hQ1 : 1 ≤ Q) (hCst : 0 < Cst) :
    2 * ((Cst + 3 * P) + 1) / (ε / 6 / 4) ≤ (1632 * Cst + 200) * Q ^ 3 := by
  have e1 : 2 * ((Cst + 3 * P) + 1) / (ε / 6 / 4) = 48 * (Cst + 3 * P + 1) * (1 / ε) := by
    field_simp; ring
  rw [e1]
  have hQ2 : Q ^ 2 ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
  have h3 : Cst + 3 * P + 1 ≤ (Cst + 3) * Q := by
    have : Cst ≤ Cst * Q := le_mul_of_one_le_right hCst.le hQ1
    linarith
  have hC2 : Cst * Q ^ 2 ≤ Cst * Q ^ 3 := mul_le_mul_of_nonneg_left hQ2 hCst.le
  calc 48 * (Cst + 3 * P + 1) * (1 / ε) ≤ 48 * ((Cst + 3) * Q) * Q := by gcongr
    _ = 48 * (Cst * Q ^ 2) + 144 * Q ^ 2 := by ring
    _ ≤ (1632 * Cst + 200) * Q ^ 3 := by nlinarith

lemma Z_le {J H P : ℕ} {Q ε : ℝ} (hJ : (J : ℝ) ≤ 8 * Q) (hH : (H : ℝ) + 1 ≤ Q)
    (hP : (P : ℝ) + 1 ≤ Q) (hεQ : 1 / ε ≤ Q) (hε : 0 < ε) (hQ1 : 1 ≤ Q) :
    ((J + H + 2 * P + ⌈12 * (P : ℝ) * (2 * (H : ℝ) + 6) / (ε / 6)⌉₊ + ⌈288 * (P : ℝ) / ε⌉₊ + 1
      : ℕ) : ℝ) ≤ 1000 * Q ^ 3 := by
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hε' : 0 ≤ 1 / ε := by positivity
  have c1 := Nat.ceil_lt_add_one (show 0 ≤ 12 * (P : ℝ) * (2 * (H : ℝ) + 6) / (ε / 6) by positivity)
  have c2 := Nat.ceil_lt_add_one (show 0 ≤ 288 * (P : ℝ) / ε by positivity)
  have e1 : 12 * (P : ℝ) * (2 * (H : ℝ) + 6) / (ε / 6) = 72 * P * (2 * H + 6) * (1 / ε) := by
    field_simp; ring
  have e2 : 288 * (P : ℝ) / ε = 288 * P * (1 / ε) := by field_simp
  have b1 : 72 * (P : ℝ) * (2 * H + 6) * (1 / ε) ≤ 72 * Q * (6 * Q) * Q := by
    gcongr
    · linarith
    · linarith
  have b2 : 288 * (P : ℝ) * (1 / ε) ≤ 288 * Q * Q := by
    gcongr; linarith
  have hQ2 : Q ≤ Q ^ 2 := le_self_pow₀ hQ1 (by norm_num)
  have hQ3 : Q ^ 2 ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
  push_cast
  have b1' : 12 * (P : ℝ) * (2 * (H : ℝ) + 6) / (ε / 6) ≤ 432 * Q ^ 3 := by
    rw [e1]; linarith [show 72 * Q * (6 * Q) * Q = 432 * Q ^ 3 by ring]
  have b2' : 288 * (P : ℝ) / ε ≤ 288 * Q ^ 3 := by
    rw [e2]; linarith [show 288 * Q * Q = 288 * Q ^ 2 by ring]
  linarith

/-- **N6 core, effective.**  One absolute `A₀` (from TT's and N5's constants): at every cutoff
with `A₀·((P₀ + Hs + 1)·2^r)^{A₀} ≤ 2^e`, `1/ε₂ ≤ 2^r`, `Bmax ≤ 2^r`, the bin-pair cross moments
are `≤ ε₂` at some power-of-two sample. -/
theorem binPair_cov_eff (htt : CastingOut.TTEquidistributedDyadic) : ∃ A₀ : ℕ,
    ∀ K N : ℕ, ∀ hK : 1 ≤ K, ∀ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ 1 → ∀ r : ℕ, 1 / ε₂ ≤ 2 ^ r → ∀ Bmax : ℕ,
    Bmax ≤ 2 ^ r → ∀ e : ℕ,
    A₀ * (((gridOf K N hK).P₀ + (K + N) * gridDm K N + 1) * 2 ^ r) ^ A₀ ≤ 2 ^ e →
    ∀ B ≤ Bmax,
      ∀ bins : Fin B → Finset ℕ, (∀ ℓ, ∀ p ∈ bins ℓ, p.Prime ∧ SchedB.YE K e < p) →
      (∀ ℓ, mass (bins ℓ) ≤ 1) →
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
  set k : ℕ := ⌈1 / c⌉₊ + 1 with hkdef
  have hk1 : 1 ≤ k := by omega
  have hkc : 1 ≤ (k : ℝ) * c := by
    have h1 : 1 / c ≤ (⌈1 / c⌉₊ : ℝ) := Nat.le_ceil _
    have : (1 / c) * c = 1 := by field_simp
    have h2 : (⌈1 / c⌉₊ : ℝ) ≤ k := by rw [hkdef]; push_cast; linarith
    nlinarith
  set D : ℝ := max ((101 : ℝ) ^ 10) X₀ with hD
  have hD101 : (101 : ℝ) ^ 10 ≤ D := le_max_left _ _
  have hDX : X₀ ≤ D := le_max_right _ _
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD101
  set M' : ℝ := 1632 * Cst + 200 with hM'
  have hM'0 : 0 < M' := by positivity
  set Cbig : ℝ := C₅ * D * M' ^ k with hCbig
  set A₀ : ℕ := ⌈Cbig⌉₊ + 1000 + 3 * k with hA₀
  refine ⟨A₀, fun K N hK ε₂ hε hε1' r hr Bmax hBr e hthr => ?_⟩
  set P₀ : ℕ := (gridOf K N hK).P₀ with hP₀
  set Hs : ℕ := (K + N) * gridDm K N with hHs
  set Qn : ℕ := (P₀ + Hs + 1) * 2 ^ r with hQn
  set Q : ℝ := (Qn : ℝ) with hQ
  have h2r1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hPHQ : ((P₀ + Hs + 1 : ℕ) : ℝ) ≤ Q := by
    rw [hQ, hQn]; push_cast; nlinarith [(by positivity : (0:ℝ) ≤ (P₀ : ℝ) + Hs + 1)]
  have h2rQ : (2 : ℝ) ^ r ≤ Q := by
    rw [hQ, hQn]; push_cast
    have : (1 : ℝ) ≤ (P₀ : ℝ) + Hs + 1 := by linarith [(Nat.cast_nonneg P₀ : (0:ℝ) ≤ _), (Nat.cast_nonneg Hs : (0:ℝ) ≤ _)]
    nlinarith
  have hQ1 : 1 ≤ Q := h2r1.trans h2rQ
  have hQ0 : 0 < Q := by linarith
  have hεQ : 1 / ε₂ ≤ Q := hr.trans h2rQ
  have hP₀Q : (P₀ : ℝ) + 1 ≤ Q := by
    have := hPHQ; push_cast at this; linarith [(Nat.cast_nonneg Hs : (0:ℝ) ≤ _)]
  have hHsQ : (Hs : ℝ) + 1 ≤ Q := by
    have := hPHQ; push_cast at this; linarith [(Nat.cast_nonneg P₀ : (0:ℝ) ≤ _)]
  -- the threshold, in ℝ
  have hthrR : (A₀ : ℝ) * Q ^ A₀ ≤ (2 : ℝ) ^ e := by
    rw [hQ]; exact_mod_cast hthr
  clear_value Q Qn
  have hQk : Q ^ (3 * k) ≤ Q ^ A₀ := pow_le_pow_right₀ hQ1 (by omega)
  have hQ3 : Q ^ 3 ≤ Q ^ (3 * k) := pow_le_pow_right₀ hQ1 (by nlinarith)
  set m := SchedB.mE K e with hm
  have hme : e ≤ m := by rw [hm]; unfold SchedB.mE; omega
  have h2em : (2 : ℝ) ^ e ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hme
  have hbig : Cbig * Q ^ (3 * k) ≤ 2 ^ m := by
    have h1 : Cbig ≤ A₀ := by
      have := Nat.le_ceil Cbig
      have : ((⌈Cbig⌉₊ : ℕ) : ℝ) ≤ A₀ := by rw [hA₀]; push_cast; linarith
      linarith
    have hQk0 : 0 ≤ Q ^ (3 * k) := by positivity
    calc Cbig * Q ^ (3 * k) ≤ A₀ * Q ^ A₀ := mul_le_mul h1 hQk hQk0 (by positivity)
      _ ≤ 2 ^ m := hthrR.trans h2em
  have h1000 : 1000 * Q ^ 3 ≤ 2 ^ m := by
    have h1 : (1000 : ℝ) ≤ A₀ := by rw [hA₀]; push_cast; linarith [(Nat.cast_nonneg ⌈Cbig⌉₊ : (0:ℝ) ≤ _), (Nat.cast_nonneg k : (0:ℝ) ≤ _)]
    calc 1000 * Q ^ 3 ≤ A₀ * Q ^ A₀ :=
          mul_le_mul h1 (hQ3.trans hQk) (by positivity) (by positivity)
      _ ≤ 2 ^ m := hthrR.trans h2em
  -- `L` and the generic good-`L` step
  set L : ℝ := 101 * 2 ^ m * Real.log 2 / C₅ with hL
  have hLge : (2 : ℝ) ^ m / C₅ ≤ L := by
    rw [hL]
    apply div_le_div_of_nonneg_right _ (by linarith)
    have : (1 : ℝ) ≤ 101 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith [(by positivity : (0:ℝ) < 2 ^ m)]
  have hgood : ∀ A η : ℝ, 0 ≤ A → 0 < η → η ≤ 1 → 2 * (A + 1) / η ≤ M' * Q ^ 3 →
      GoodL c C₅ X₀ A η L := by
    intro A η hA hη hη1 hu
    refine goodL_of_ge hc hC₅1 hkc hk1 hD101 hDX hA hη hη1 ?_
    have hu0 : 0 ≤ 2 * (A + 1) / η := by positivity
    calc D * (2 * (A + 1) / η) ^ k ≤ D * (M' * Q ^ 3) ^ k := by gcongr
      _ = Cbig * Q ^ (3 * k) / C₅ := by
          rw [hCbig, mul_pow, ← pow_mul]; field_simp
      _ ≤ 2 ^ m / C₅ := by gcongr
      _ ≤ L := hLge
  have hε1 : 1 / ε₂ * ε₂ = 1 := by field_simp
  -- `J₀ = r + 7`
  set J₀ : ℕ := r + 7 with hJ₀
  have hJ₀ε : (1 / 2 : ℝ) ^ J₀ < ε₂ / 96 := by
    have h1 : (1 / 2 : ℝ) ^ r ≤ ε₂ := by
      rw [one_div_pow, div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hε] at hr; linarith
    rw [hJ₀, pow_add]
    have : (1 / 2 : ℝ) ^ 7 = 1 / 128 := by norm_num
    rw [this]; linarith
  have hJQ : (J₀ : ℝ) ≤ 8 * Q := by
    have h1 : r + 1 ≤ 2 ^ r := Nat.lt_two_pow_self
    have h2 : ((r + 7 : ℕ) : ℝ) ≤ 8 * (2 : ℝ) ^ r := by
      have : r + 7 ≤ 8 * 2 ^ r := by have := Nat.one_le_two_pow (n := r); omega
      exact_mod_cast this
    rw [hJ₀]; linarith
  have hBQ : (Bmax : ℝ) ≤ Q := by
    have : (Bmax : ℝ) ≤ 2 ^ r := by exact_mod_cast hBr
    linarith
  have hQ2 : Q ≤ Q ^ 2 := le_self_pow₀ hQ1 (by norm_num)
  have hQ32 : Q ^ 2 ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hCQ : 0 ≤ Cst * Q ^ 3 := by positivity
  have hQ30 : 0 ≤ Q ^ 3 := by positivity
  have hMQ : M' * Q ^ 3 = 1632 * (Cst * Q ^ 3) + 200 * Q ^ 3 := by rw [hM']; ring
  have hP0 : (0 : ℝ) ≤ P₀ := Nat.cast_nonneg _
  have hHs0 : (0 : ℝ) ≤ Hs := Nat.cast_nonneg _
  have hev : GoodL c C₅ X₀ (((gridOf K N hK).P₀ + (K + N) * gridDm K N : ℕ) : ℝ) (ε₂ / 6) L ∧
      GoodL c C₅ X₀ (J₀ * Bmax ^ 2 * Cst * 102 + 1 : ℝ) 1 L ∧
      GoodL c C₅ X₀ (Cst + 3 * (gridOf K N hK).P₀ : ℝ) (ε₂ / 6 / 4) L := by
    refine ⟨?_, ?_, ?_⟩
    · refine hgood _ _ (by positivity) (by positivity) (by linarith) ?_
      have := ub_one hP0 hHs0 (by have := hPHQ; push_cast at this; exact this) hεQ hε hQ1 hCst
      rw [hM', Nat.cast_add]; exact this
    · refine hgood _ _ (by positivity) one_pos le_rfl ?_
      rw [hM']; exact ub_two (Nat.cast_nonneg _) (Nat.cast_nonneg _) hJQ hBQ hQ1 hCst
    · refine hgood _ _ (by positivity) (by positivity) (by linarith) ?_
      rw [hM']; exact ub_three hP0 hP₀Q hεQ hε hQ1 hCst
  have hZ := Z_le (J := J₀) (H := Hs) (P := P₀) hJQ hHsQ hP₀Q hεQ hε hQ1
  have hmZ : J₀ + Hs + 2 * P₀ + ⌈12 * (P₀ : ℝ) * (2 * (Hs : ℝ) + 6) / (ε₂ / 6)⌉₊
      + ⌈288 * (P₀ : ℝ) / ε₂⌉₊ + 1 ≤ 2 ^ m := by
    have : ((J₀ + Hs + 2 * P₀ + ⌈12 * (P₀ : ℝ) * (2 * (Hs : ℝ) + 6) / (ε₂ / 6)⌉₊
      + ⌈288 * (P₀ : ℝ) / ε₂⌉₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
      exact_mod_cast hZ.trans h1000
    exact_mod_cast this
  exact binPair_cov_core hc hCst hTT hC₅' hC₅1 hC₅C h5 K N hK hε Bmax J₀ hJ₀ε e hev hmZ

end NormalNumbers.G4.Base2
