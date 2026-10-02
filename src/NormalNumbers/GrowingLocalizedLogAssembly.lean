/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.GrowingLocalizedLogCostBound
import NormalNumbers.GrowingLocalizedLogAsymp

/-!
# N9: the Weyl sums of `R_n` are `o(N)` (block assembly)

`main_bound` is the deterministic heart.  At one scale `N`, cut `[0, GH)` into `G` blocks of
length `H`.  A block `j ≥ 1` with no index of `S` in `[jH − B, jH + H)` is clean, and
`block_bound` controls it.  The other blocks number at most `1 + 2Ψ`, where `Ψ` is the number
of indices `≤ N`.  The numerical hypotheses (`hk`, `hbad`, …) are discharged asymptotically in
`weyl_Rs`.
-/

namespace NormalNumbers.GrowingLocalizedLog

open Finset Filter NormalNumbers.Literature.VandeheyDiff NormalNumbers.G4

lemma sum_range_mul_blocks (f : ℕ → ℂ) (G H : ℕ) :
    ∑ n ∈ range (G * H), f n = ∑ j ∈ range G, ∑ t ∈ range H, f (j * H + t) := by
  induction G with
  | zero => simp
  | succ G ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- The cost of a depth-`k` block, in closed form. -/
lemma constPair_sum_le' (Z k : ℕ) :
    (constPair 2 (oddPrimes Z) k).1 + (constPair 2 (oddPrimes Z) k).2 ≤
      (2 : ℝ) ^ (60 * (Z.primeCounting + 2) ^ 4) * 2 ^ ((k + 5) * Z.primeCounting) := by
  have hP : ∀ p ∈ oddPrimes Z, 2 ≤ p := fun p hp => (mem_oddPrimes.1 hp).1.two_le
  refine (constPair_sum_le 2 hP k).trans ?_
  have h1 := nine_costX_le Z
  have h2 : (2 : ℝ) ^ ((k + 5) * (oddPrimes Z).card) ≤ 2 ^ ((k + 5) * Z.primeCounting) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (oddPrimes_card_le Z))
  have h0 : 0 ≤ costX 2 (oddPrimes Z) := by
    unfold costX; positivity
  calc 9 * costX 2 (oddPrimes Z) * 2 ^ ((k + 5) * (oddPrimes Z).card)
      ≤ 2 ^ (60 * (Z.primeCounting + 2) ^ 4) * 2 ^ ((k + 5) * Z.primeCounting) := by
        gcongr

/-- At most two blocks of length `H ≥ B` meet `[m − B, m]`. -/
lemma bad_block_mem {m j H B : ℕ} (hH : 0 < H) (hBH : B ≤ H) (h1 : j * H ≤ m + B)
    (h2 : m < j * H + H) : j = m / H ∨ j = m / H + 1 := by
  have ha : m / H ≤ j := by
    have : m < (j + 1) * H := by rw [Nat.succ_mul]; exact h2
    have := (Nat.div_lt_iff_lt_mul hH).2 this
    omega
  have hb : j ≤ m / H + 1 := by
    have : j * H ≤ m + H := h1.trans (by omega)
    have h' : j ≤ (m + H) / H := (Nat.le_div_iff_mul_le hH).2 this
    rwa [Nat.add_div_right _ hH] at h'
  omega

open Classical in
theorem main_bound (hV : VandeheyThm51) {S : ℕ → Prop} {z N G H B : ℕ} (h : ℤ) (hh : h ≠ 0)
    (hS3 : ∀ K, S (3 ^ K) ∧ S (2 * 3 ^ K))
    (hsupp : ∀ m p, S m → 1 ≤ m → m ≤ N → p.Prime → p ∣ m → p ≤ z)
    (hz3 : 3 ≤ z) (hGH : G * H ≤ N) (hNG : N ≤ G * H + G)
    (hB : N < 2 ^ B) (hBH : B ≤ H) (hH2 : 2 ≤ H) (hH6 : 6 * h.natAbs ≤ H)
    (hH3 : 81 * h.natAbs ^ 4 ≤ H ^ 3) (δ : ℝ) (hδ : 0 < δ)
    (hk : ∀ k : ℕ, (k : ℝ) ≤ z.primeCounting * Real.log N / Real.log H + 2 →
      2 + (2 : ℝ) ^ (60 * (z.primeCounting + 2) ^ 4) * 2 ^ ((k + 5) * z.primeCounting) *
        (H : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) * (1 + z.primeCounting * Real.log N) ≤ δ / 2 * H)
    (hbad : ((1 : ℝ) + 2 * ((Icc 1 N).filter S).card) * H ≤ δ / 4 * N)
    (hG : (G : ℝ) ≤ δ / 4 * N) :
    ‖∑ n ∈ range N, ePhase ((h : ℝ) * (Rs S n : ℝ))‖ ≤ δ * N := by
  classical
  set f : ℕ → ℂ := fun n => ePhase ((h : ℝ) * (Rs S n : ℝ)) with hfdef
  have hf1 : ∀ n, ‖f n‖ = 1 := fun n => norm_ePhase _
  set Sf := (Icc 1 N).filter S
  -- split off the remainder
  have hsplit : ∑ n ∈ range N, f n =
      ∑ j ∈ range G, ∑ t ∈ range H, f (j * H + t) + ∑ t ∈ range (N - G * H), f (G * H + t) := by
    conv_lhs => rw [show N = G * H + (N - G * H) by omega]
    rw [Finset.sum_range_add, sum_range_mul_blocks]
  have hrest : ‖∑ t ∈ range (N - G * H), f (G * H + t)‖ ≤ G := by
    refine (norm_sum_le _ _).trans ?_
    simp only [hf1, Finset.sum_const, card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast (by omega : N - G * H ≤ G)
  -- bad blocks
  let bad : ℕ → Prop := fun j => j = 0 ∨ ∃ m ∈ Sf, j * H ≤ m + B ∧ m < j * H + H
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hblock : ∀ j ∈ range G, ‖∑ t ∈ range H, f (j * H + t)‖ ≤
      (if bad j then (H : ℝ) else 0) + δ / 2 * H := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases hbj : bad j
    · rw [if_pos hbj]
      have : ‖∑ t ∈ range H, f (j * H + t)‖ ≤ H := by
        refine (norm_sum_le _ _).trans ?_
        simp [hf1]
      have : 0 ≤ δ / 2 * H := by positivity
      linarith
    rw [if_neg hbj, zero_add]
    simp only [bad, not_or, not_exists, not_and] at hbj
    obtain ⟨hj0, hjm⟩ := hbj
    set n₀ := j * H with hn₀
    have hjH : n₀ + H ≤ N := by
      have : (j + 1) * H ≤ G * H := Nat.mul_le_mul_right _ hj
      rw [Nat.succ_mul] at this; omega
    have hn1 : 1 ≤ n₀ := by
      have : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hj0
      nlinarith
    have hHn : H ≤ n₀ := by
      have : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hj0
      nlinarith
    have hc : CleanAt S z n₀ := by
      refine ⟨fun m p hS hm hmn => hsupp m p hS hm (by omega), ?_⟩
      intro m hS hm hmn
      have hmS : m ∈ Sf := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hm, by omega⟩, hS⟩
      have hlt : m + B < n₀ := by
        by_contra hc; push Not at hc
        exact hjm m hmS hc (by omega)
      calc m ≤ N := by omega
        _ < 2 ^ B := hB
        _ ≤ 2 ^ (n₀ - m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hfree : ∀ j', n₀ < j' → j' < n₀ + H → ¬ S j' := by
      intro j' h1 h2 hS
      have hmS : j' ∈ Sf := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, hS⟩
      exact hjm j' hmS (by omega) (by omega)
    set K := Nat.log 3 n₀
    have hK : n₀ < 3 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) n₀
    rw [pow_succ] at hK
    have hq2 : 2 * h.natAbs ≤ 3 ^ K := by omega
    have hab : (0 : ℝ) < h.natAbs := by exact_mod_cast Int.natAbs_pos.2 hh
    have hHq : (H : ℝ) ≤ (((3 ^ K : ℕ) : ℝ) / h.natAbs) ^ 4 := by
      have hT : (H : ℝ) / 3 ≤ ((3 ^ K : ℕ) : ℝ) := by
        have : (H : ℝ) ≤ ((3 ^ K : ℕ) : ℝ) * 3 := by
          have : H ≤ 3 ^ K * 3 := by omega
          exact_mod_cast this
        linarith
      have h4 : (H : ℝ) ≤ ((H : ℝ) / 3 / h.natAbs) ^ 4 := by
        have e : ((H : ℝ) / 3 / h.natAbs) ^ 4 = (H : ℝ) ^ 4 / (81 * (h.natAbs : ℝ) ^ 4) := by
          field_simp; ring
        rw [e, le_div_iff₀ (by positivity)]
        have : (81 * (h.natAbs : ℝ) ^ 4) ≤ (H : ℝ) ^ 3 := by exact_mod_cast hH3
        nlinarith
      refine h4.trans (pow_le_pow_left₀ (by positivity) ?_ 4)
      exact div_le_div_of_nonneg_right hT hab.le
    obtain ⟨k, hk1, hk2⟩ := block_bound hV hc hz3 hn1 (hS3 K).1 (hS3 K).2 hfree h hh hH2 hq2 hHq
    have hlogn : Real.log n₀ ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast (by omega : n₀ ≤ N))
    have hlogH : 0 < Real.log H := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
    have hpi0 : (0 : ℝ) ≤ z.primeCounting := by positivity
    have hk' : (k : ℝ) ≤ z.primeCounting * Real.log N / Real.log H + 2 := by
      refine hk1.trans ?_
      gcongr
    have hfin := hk k hk'
    have hcost := constPair_sum_le' z k
    have hHp : 0 ≤ (H : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) := by positivity
    have hlog1 : 1 + z.primeCounting * Real.log n₀ ≤ 1 + z.primeCounting * Real.log N := by
      gcongr
    have hlog0 : 0 ≤ 1 + z.primeCounting * Real.log n₀ := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ n₀ by exact_mod_cast hn1); positivity
    calc ‖∑ t ∈ range H, f (n₀ + t)‖ ≤ 2 + ((constPair 2 (oddPrimes z) k).1 +
          (constPair 2 (oddPrimes z) k).2) * (H : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) *
          (1 + z.primeCounting * Real.log n₀) := hk2
      _ ≤ 2 + (2 : ℝ) ^ (60 * (z.primeCounting + 2) ^ 4) * 2 ^ ((k + 5) * z.primeCounting) *
          (H : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) * (1 + z.primeCounting * Real.log N) := by
        gcongr
      _ ≤ δ / 2 * H := hfin
  -- count bad blocks
  have hbadsub : (range G).filter bad ⊆
      insert 0 (Sf.biUnion fun m => ({m / H, m / H + 1} : Finset ℕ)) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rcases hj.2 with h0 | ⟨m, hm, h1, h2⟩
    · rw [h0]; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_biUnion]
      refine ⟨m, hm, ?_⟩
      rcases bad_block_mem (by omega) hBH h1 h2 with e | e <;> simp [e]
  have hbadcard : (((range G).filter bad).card : ℝ) ≤ 1 + 2 * Sf.card := by
    have h1 := Finset.card_le_card hbadsub
    have h2 := Finset.card_insert_le 0 (Sf.biUnion fun m => ({m / H, m / H + 1} : Finset ℕ))
    have h3 : (Sf.biUnion fun m => ({m / H, m / H + 1} : Finset ℕ)).card ≤ Sf.card * 2 := by
      refine (Finset.card_biUnion_le).trans ?_
      calc ∑ m ∈ Sf, ({m / H, m / H + 1} : Finset ℕ).card ≤ ∑ m ∈ Sf, 2 :=
            Finset.sum_le_sum fun m _ => Finset.card_le_two
        _ = Sf.card * 2 := by rw [Finset.sum_const, smul_eq_mul]
    have : ((range G).filter bad).card ≤ 1 + 2 * Sf.card := by omega
    exact_mod_cast this
  have hblocks : ‖∑ j ∈ range G, ∑ t ∈ range H, f (j * H + t)‖ ≤
      (1 + 2 * Sf.card) * H + G * (δ / 2 * H) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hblock).trans ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    gcongr
  have hGHr : (G : ℝ) * H ≤ N := by exact_mod_cast hGH
  rw [hsplit]
  calc ‖∑ j ∈ range G, ∑ t ∈ range H, f (j * H + t) + ∑ t ∈ range (N - G * H), f (G * H + t)‖
      ≤ ‖∑ j ∈ range G, ∑ t ∈ range H, f (j * H + t)‖ +
          ‖∑ t ∈ range (N - G * H), f (G * H + t)‖ := norm_add_le _ _
    _ ≤ (1 + 2 * Sf.card) * H + G * (δ / 2 * H) + G := add_le_add hblocks hrest
    _ ≤ δ * N := by
      have := mul_le_mul_of_nonneg_left hGHr (by positivity : (0 : ℝ) ≤ δ / 2)
      nlinarith

end NormalNumbers.GrowingLocalizedLog
