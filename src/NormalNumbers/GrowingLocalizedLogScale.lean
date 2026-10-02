/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.GrowingLocalizedLogWeyl

/-!
# N9 at one scale, with every parameter chosen

`weyl_scale` feeds `main_bound` the choice `G = 2^{(ℓ+1)^3}`, `H = ⌊N/G⌋`, `B = L+1`, and
discharges all of its numerical hypotheses from three inputs: `π ≤ ℓ+1`,
`2^π ≤ (log N)^{1−ε}`, and the single polynomial-versus-exponential bound
`(c+c'+10)(ℓ+3)^4 ≤ 2^ℓ` (plus `hbig` for `saving_beats_cost`).
-/

namespace NormalNumbers.GrowingLocalizedLog

open Finset Filter NormalNumbers.Literature.VandeheyDiff NormalNumbers.G4

set_option maxHeartbeats 1000000 in
open Classical in
theorem weyl_scale (hV : VandeheyThm51) {S : ℕ → Prop} {z N L ℓ c c' : ℕ} (h : ℤ) (hh : h ≠ 0)
    (hS3 : ∀ K, S (3 ^ K) ∧ S (2 * 3 ^ K))
    (hsupp : ∀ m p, S m → 1 ≤ m → m ≤ N → p.Prime → p ∣ m → p ≤ z)
    (hz3 : 3 ≤ z) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hc1 : 81 * h.natAbs ^ 4 + 6 * h.natAbs + 2 ≤ 2 ^ c) (hc2 : 8 / δ ≤ (2 : ℝ) ^ c)
    (hc' : 4 / δ ≤ (2 : ℝ) ^ c')
    (hNL : 2 ^ L ≤ N) (hNL' : N < 2 ^ (L + 1)) (hLℓ : 2 ^ ℓ ≤ L) (hLℓ' : L < 2 ^ (ℓ + 1))
    (hπ : z.primeCounting ≤ ℓ + 1)
    (hπN : (2 : ℝ) ^ (z.primeCounting : ℝ) ≤ Real.log N ^ (1 - ε))
    (hbig : 512 * Real.exp (ε * Real.log 2) * ((62 + c') * Real.log 2) * ((ℓ : ℝ) + 3) ^ 4 ≤
      Real.exp (ε * Real.log 2 * ℓ))
    (hpoly : (c + c' + 10) * (ℓ + 3) ^ 4 ≤ 2 ^ ℓ) (hℓc : c' + 2 ≤ ℓ) :
    ‖∑ n ∈ range N, ePhase ((h : ℝ) * (Rs S n : ℝ))‖ ≤ δ * N := by
  set π := z.primeCounting with hπdef
  set g := (ℓ + 1) ^ 3 with hg
  set G := 2 ^ g with hG
  set H := N / G with hHdef
  have hGpos : 0 < G := Nat.two_pow_pos _
  -- polynomial bookkeeping
  set u := (ℓ + 3) ^ 4 with hu
  have hu3 : (ℓ + 1) ^ 3 ≤ u := by
    calc (ℓ + 1) ^ 3 ≤ (ℓ + 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ ≤ u := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hu4 : (ℓ + 1) ^ 4 ≤ u := Nat.pow_le_pow_left (by omega) 4
  have hu1 : ℓ + 1 ≤ u := by
    calc ℓ + 1 ≤ (ℓ + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      _ ≤ u := hu3
  have hcu : (c + c' + 10) * u = c * u + c' * u + 10 * u := by ring
  have hcu1 : c ≤ c * u := Nat.le_mul_of_pos_right _ (by positivity)
  have hcu2 : c' ≤ c' * u := Nat.le_mul_of_pos_right _ (by positivity)
  have hL : g + ℓ + 1 + c + c' + (ℓ + 1) ^ 4 + (ℓ + 1) ≤ L := by omega
  have hgπ : π * (g + 1) + g ≤ L := by
    have : π * (g + 1) ≤ (ℓ + 1) * (g + 1) := Nat.mul_le_mul_right _ hπ
    have e : (ℓ + 1) * (g + 1) = (ℓ + 1) ^ 4 + (ℓ + 1) := by rw [hg]; ring
    omega
  have hgL : 2 * g ≤ L := by omega
  -- `H`
  have hH : 2 ^ (L - g) ≤ H := by
    rw [hHdef, Nat.le_div_iff_mul_le hGpos, hG, ← pow_add]
    exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hNL
  have hHc : 2 ^ (ℓ + 1) * 2 ^ c ≤ H := by
    rw [← pow_add]; exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hH
  have hHc' : 2 ^ c ≤ H := le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hHc
  have hGH : G * H ≤ N := by rw [mul_comm]; exact Nat.div_mul_le_self N G
  have hNG : N ≤ G * H + G := by
    have := Nat.div_add_mod N G
    have := Nat.mod_lt N hGpos
    rw [hHdef]; linarith
  have hBH : L + 1 ≤ H := by
    have : L + 1 ≤ 2 ^ (ℓ + 1) := hLℓ'
    have : 2 ^ (ℓ + 1) ≤ 2 ^ (ℓ + 1) * 2 ^ c := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    omega
  have hH2 : 2 ≤ H := by omega
  have hH6 : 6 * h.natAbs ≤ H := by omega
  have hH3 : 81 * h.natAbs ^ 4 ≤ H ^ 3 := by
    have : H ≤ H ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have hHr : (2 : ℝ) ^ c ≤ H := by exact_mod_cast hHc'
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (Nat.two_pow_pos L) hNL)
  refine main_bound hV h hh hS3 hsupp hz3 hGH hNG hNL' hBH hH2 hH6 hH3 δ hδ ?_ ?_ ?_
  · -- the clean blocks
    intro k hk
    have hL1 : 1 ≤ L := le_trans Nat.one_le_two_pow hLℓ
    have s1 : Real.log N ≤ (L + 1) * Real.log 2 := by
      have : Real.log N ≤ Real.log ((2 : ℝ) ^ (L + 1)) :=
        Real.log_le_log hNpos (by exact_mod_cast hNL'.le)
      rw [Real.log_pow] at this; push_cast at this; linarith
    have s2 : ((L - g : ℕ) : ℝ) * Real.log 2 ≤ Real.log H := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) (by exact_mod_cast hH)
    have hLg : ((L - g : ℕ) : ℝ) = L - g := by push_cast [show g ≤ L by omega]; ring
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hLg0 : (0 : ℝ) < L - g := by
      have : g < L := by omega
      have : (g : ℝ) < L := by exact_mod_cast this
      linarith
    have hlogH : 0 < Real.log H := by
      rw [hLg] at s2; nlinarith
    have hπr : (π : ℝ) * (g + 1) + g ≤ L := by exact_mod_cast hgπ
    have hπ0 : (0 : ℝ) ≤ π := by positivity
    have hlN0 : 0 ≤ Real.log N :=
      Real.log_nonneg (by exact_mod_cast (le_trans Nat.one_le_two_pow hNL))
    have hratio : (π : ℝ) * Real.log N / Real.log H ≤ π + 1 := by
      rw [div_le_iff₀ hlogH]
      rw [hLg] at s2
      have e1 : (π : ℝ) * Real.log N ≤ π * ((L + 1) * Real.log 2) :=
        mul_le_mul_of_nonneg_left s1 hπ0
      have e2 : ((π : ℝ) + 1) * ((L - g) * Real.log 2) ≤ (π + 1) * Real.log H :=
        mul_le_mul_of_nonneg_left s2 (by positivity)
      have e3 : (π : ℝ) * (L + 1) ≤ (π + 1) * (L - g) := by nlinarith
      nlinarith
    have hk3 : k ≤ π + 3 := by
      have : (k : ℝ) ≤ π + 3 := by linarith
      exact_mod_cast this
    have hsave := saving_beats_cost (π := π) hε hε1 hδ hc' hNL hNL' hLℓ hLℓ' hgL hH hπ hk3
      hπN hbig
    set a : ℝ := 1 / (2 : ℝ) ^ (k + 4)
    have hHa : (H : ℝ) ^ a * (H : ℝ) ^ (1 - a) = H := by
      rw [← Real.rpow_add hHpos]; simp
    have hH1a : 0 ≤ (H : ℝ) ^ (1 - a) := by positivity
    have hmain : (2 : ℝ) ^ (60 * (π + 2) ^ 4) * 2 ^ ((k + 5) * π) * (H : ℝ) ^ (1 - a) *
        (1 + π * Real.log N) ≤ δ / 4 * H := by
      calc (2 : ℝ) ^ (60 * (π + 2) ^ 4) * 2 ^ ((k + 5) * π) * (H : ℝ) ^ (1 - a) *
            (1 + π * Real.log N)
          = ((2 : ℝ) ^ (60 * (π + 2) ^ 4) * 2 ^ ((k + 5) * π) * (1 + π * Real.log N)) *
            (H : ℝ) ^ (1 - a) := by ring
        _ ≤ (δ / 4 * (H : ℝ) ^ a) * (H : ℝ) ^ (1 - a) :=
            mul_le_mul_of_nonneg_right hsave hH1a
        _ = δ / 4 * H := by rw [mul_assoc, hHa]
    have h2 : 2 ≤ δ / 4 * H := by
      have : 8 / δ ≤ H := hc2.trans hHr
      rw [div_le_iff₀ hδ] at this; linarith
    linarith
  · -- the bad blocks
    have hcard : ((Icc 1 N).filter S).card ≤ (L + 1) ^ π := by
      refine (Finset.card_le_card ?_).trans ((card_smooth_le z N).trans ?_)
      · intro m hm
        rw [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
        exact ⟨hm.1, fun p hp hpm => hsupp m p hm.2 hm.1.1 hm.1.2 hp hpm⟩
      · rw [Nat.log_eq_of_pow_le_of_lt_pow hNL hNL']
    have hpow : (L + 1) ^ π ≤ 2 ^ ((ℓ + 1) ^ 2) := by
      calc (L + 1) ^ π ≤ (2 ^ (ℓ + 1)) ^ π := Nat.pow_le_pow_left hLℓ' _
        _ ≤ (2 ^ (ℓ + 1)) ^ (ℓ + 1) := Nat.pow_le_pow_right (Nat.two_pow_pos _) hπ
        _ = 2 ^ ((ℓ + 1) ^ 2) := by rw [← pow_mul, sq]
    have hexp : (ℓ + 1) ^ 2 + c' + 2 ≤ g := by
      have : (ℓ + 1) ^ 2 * (ℓ + 1) = g := by rw [hg]; ring
      have : (ℓ + 1) ^ 2 * 1 + c' + 2 ≤ (ℓ + 1) ^ 2 * (ℓ + 1) := by
        have : 1 ≤ (ℓ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        nlinarith
      omega
    have hA : (1 + 2 * ((Icc 1 N).filter S).card) * 2 ^ c' ≤ G := by
      have : 1 + 2 * ((Icc 1 N).filter S).card ≤ 4 * 2 ^ ((ℓ + 1) ^ 2) := by
        have := Nat.one_le_two_pow (n := (ℓ + 1) ^ 2); omega
      calc (1 + 2 * ((Icc 1 N).filter S).card) * 2 ^ c' ≤ 4 * 2 ^ ((ℓ + 1) ^ 2) * 2 ^ c' :=
            Nat.mul_le_mul_right _ this
        _ = 2 ^ ((ℓ + 1) ^ 2 + c' + 2) := by rw [pow_add, pow_add]; ring
        _ ≤ G := Nat.pow_le_pow_right (by norm_num) hexp
    have hAr : ((1 : ℝ) + 2 * ((Icc 1 N).filter S).card) * 2 ^ c' ≤ G := by exact_mod_cast hA
    have hGHr : (G : ℝ) * H ≤ N := by exact_mod_cast hGH
    have h4 : 4 ≤ δ * 2 ^ c' := by rw [div_le_iff₀ hδ] at hc'; linarith
    have hA0 : (0 : ℝ) ≤ (1 + 2 * ((Icc 1 N).filter S).card) := by positivity
    have : 4 * (((1 : ℝ) + 2 * ((Icc 1 N).filter S).card) * H) ≤ δ * N := by
      calc 4 * (((1 : ℝ) + 2 * ((Icc 1 N).filter S).card) * H)
          ≤ (δ * 2 ^ c') * (((1 : ℝ) + 2 * ((Icc 1 N).filter S).card) * H) :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
        _ = δ * ((((1 : ℝ) + 2 * ((Icc 1 N).filter S).card) * 2 ^ c') * H) := by ring
        _ ≤ δ * (G * H) := by gcongr
        _ ≤ δ * N := by gcongr
    linarith
  · -- the remainder
    have hGc : G * 2 ^ c' ≤ N := by
      rw [hG, ← pow_add]; exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hNL
    have hGcr : (G : ℝ) * 2 ^ c' ≤ N := by exact_mod_cast hGc
    have h4 : 4 ≤ δ * 2 ^ c' := by rw [div_le_iff₀ hδ] at hc'; linarith
    have : 4 * (G : ℝ) ≤ δ * N := by
      calc 4 * (G : ℝ) ≤ δ * 2 ^ c' * G := mul_le_mul_of_nonneg_right h4 (by positivity)
        _ = δ * (G * 2 ^ c') := by ring
        _ ≤ δ * N := by gcongr
    linarith

end NormalNumbers.GrowingLocalizedLog
