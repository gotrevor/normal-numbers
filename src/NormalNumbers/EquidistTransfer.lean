/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Wall

/-!
# Normality descends from a power base: `IsNormal (b^K) x → IsNormal b x`

The converse of `PowerBase.isNormal_pow`, proved through equidistribution, with no Weyl
criterion:

* `equidistributed_fract_nat_mul`: `u` equidistributed in `[0,1)` ⇒ `m·u mod 1` equidistributed
  (the preimage of `[a,c)` is `m` disjoint intervals of length `(c−a)/m`);
* `equidistributed_of_interleave`: if every residue-class subsequence `n ↦ v(Kn + r)` is
  equidistributed, so is `v`;
* `isNormal_of_isNormal_pow`: `orbit b x (Kn + r) = b^r · orbit (b^K) x n mod 1`.
-/

namespace NormalNumbers

open Filter

theorem visitCount_eq_sum (u : ℕ → ℝ) (a c : ℝ) (N : ℕ) :
    (visitCount u a c N : ℝ) = ∑ n ∈ Finset.range N, if u n ∈ Set.Ico a c then (1 : ℝ) else 0 := by
  rw [visitCount, Finset.card_filter]; push_cast; rfl

theorem fract_eq_sub_natFloor {t : ℝ} (ht : 0 ≤ t) : Int.fract t = t - (⌊t⌋₊ : ℝ) := by
  rw [Int.fract, ← Int.natCast_floor_eq_floor ht]; push_cast; rfl

/-- Multiplying an equidistributed `[0,1)`-sequence by a positive integer, mod 1, keeps it
equidistributed. -/
theorem equidistributed_fract_nat_mul (u : ℕ → ℝ) (hu : Equidistributed u)
    (hu01 : ∀ n, u n ∈ Set.Ico (0 : ℝ) 1) (m : ℕ) (hm : 0 < m) :
    Equidistributed (fun n => Int.fract (m * u n)) := by
  intro a c ha hac hc
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- pointwise decomposition
  have hpt : ∀ n, (if Int.fract (m * u n) ∈ Set.Ico a c then (1 : ℝ) else 0)
      = ∑ j ∈ Finset.range m,
          if u n ∈ Set.Ico ((a + j) / m) ((c + j) / m) then (1 : ℝ) else 0 := by
    intro n
    set t := (m : ℝ) * u n with ht
    have ht0 : 0 ≤ t := mul_nonneg hmR.le (hu01 n).1
    have htm : t < m := by
      have := (hu01 n).2; rw [ht]; nlinarith
    have hiff : ∀ j : ℕ, u n ∈ Set.Ico ((a + j) / m) ((c + j) / m) ↔ a ≤ t - j ∧ t - j < c := by
      intro j
      simp only [Set.mem_Ico, div_le_iff₀ hmR, lt_div_iff₀ hmR, ht]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    set j0 := ⌊t⌋₊
    have hj0 : j0 < m := by
      have := Nat.floor_lt ht0 |>.2 htm; exact_mod_cast this
    rw [Finset.sum_eq_single j0]
    · rw [fract_eq_sub_natFloor ht0]
      by_cases hP : a ≤ t - j0 ∧ t - j0 < c
      · rw [if_pos (show t - (⌊t⌋₊ : ℝ) ∈ Set.Ico a c from hP), if_pos ((hiff j0).2 hP)]
      · rw [if_neg (show t - (⌊t⌋₊ : ℝ) ∉ Set.Ico a c from hP),
          if_neg (fun h => hP ((hiff j0).1 h))]
    · intro j _ hj
      rw [if_neg]
      intro h
      obtain ⟨h1, h2⟩ := (hiff j).1 h
      apply hj
      refine ((Nat.floor_eq_iff ht0).2 ⟨?_, ?_⟩).symm <;> linarith
    · intro h; exact absurd (Finset.mem_range.2 hj0) h
  have hkey : ∀ N, (visitCount (fun n => Int.fract (m * u n)) a c N : ℝ) / N
      = ∑ j ∈ Finset.range m, (visitCount u ((a + j) / m) ((c + j) / m) N : ℝ) / N := by
    intro N
    rw [← Finset.sum_div, visitCount_eq_sum]
    simp_rw [visitCount_eq_sum, hpt]
    rw [Finset.sum_comm]
  simp_rw [hkey]
  have hlim : c - a = ∑ j ∈ Finset.range m, ((c + j) / m - (a + j) / m) := by
    simp only [show ∀ j : ℕ, (c + j) / (m : ℝ) - (a + j) / m = (c - a) / m from
      fun j => by ring, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [hlim]
  refine tendsto_finsetSum _ (fun j hj => hu _ _ ?_ ?_ ?_)
  · positivity
  · rw [div_le_div_iff_of_pos_right hmR]; linarith
  · rw [div_le_one hmR]
    have : (j : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.1 hj
    linarith

/-- **Interleaving**: if each residue-class subsequence is equidistributed, so is the whole. -/
theorem equidistributed_of_interleave (v : ℕ → ℝ) (K : ℕ) (hK : 0 < K)
    (h : ∀ r < K, Equidistributed (fun n => v (K * n + r))) : Equidistributed v := by
  intro a c ha hac hc
  set f : ℕ → ℝ := fun n => if v n ∈ Set.Ico a c then 1 else 0 with hf
  have hf01 : ∀ n, 0 ≤ f n ∧ f n ≤ 1 := by
    intro n; simp only [hf]; split_ifs <;> norm_num
  have hblock : ∀ q, ∑ n ∈ Finset.range (K * q), f n
      = ∑ r ∈ Finset.range K, (visitCount (fun n => v (K * n + r)) a c q : ℝ) := by
    intro q
    simp_rw [visitCount_eq_sum]
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      simp_rw [Finset.sum_range_succ]
      rw [Finset.sum_add_distrib]
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  -- the error term
  have herr : ∀ N, |(∑ n ∈ Finset.range N, f n) - ∑ n ∈ Finset.range (K * (N / K)), f n| ≤ K := by
    intro N
    have hN : N = K * (N / K) + N % K := (Nat.div_add_mod N K).symm
    have hlt : N % K < K := Nat.mod_lt _ hK
    have hsplit := Finset.sum_range_add f (K * (N / K)) (N % K)
    rw [← hN] at hsplit
    rw [hsplit, add_sub_cancel_left, abs_of_nonneg (Finset.sum_nonneg fun i _ => (hf01 _).1)]
    calc ∑ x ∈ Finset.range (N % K), f (K * (N / K) + x) ≤ ∑ x ∈ Finset.range (N % K), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (hf01 _).2
      _ = (N % K : ℕ) := by simp
      _ ≤ K := by exact_mod_cast hlt.le
  have hq : Tendsto (fun N : ℕ => N / K) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b; refine ⟨b * K, fun N hN => ?_⟩
    exact (Nat.le_div_iff_mul_le hK).2 hN
  -- ratio q/N → 1/K
  have hratio : Tendsto (fun N : ℕ => ((N / K : ℕ) : ℝ) / N) atTop (nhds (1 / K)) := by
    have hup : ∀ N : ℕ, ((N / K : ℕ) : ℝ) / N ≤ 1 / K := by
      intro N
      rcases Nat.eq_zero_or_pos N with h0 | hN
      · subst h0; simp
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_le_div_iff₀ hNR hKR, one_mul]
      have : (N / K : ℕ) * K ≤ N := Nat.div_mul_le_self N K
      exact_mod_cast this
    have hlow : ∀ᶠ N : ℕ in atTop, 1 / K - 1 / N ≤ ((N / K : ℕ) : ℝ) / N := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      have h1 : N < (N / K + 1) * K := by
        have := Nat.lt_div_mul_add (a := N) hK; linarith
      have h1R : (N : ℝ) < ((N / K : ℕ) + 1) * K := by exact_mod_cast h1
      rw [div_sub_div _ _ hKR.ne' hNR.ne', div_le_div_iff₀ (by positivity) hNR]
      nlinarith
    have hl : Tendsto (fun N : ℕ => 1 / (K : ℝ) - 1 / N) atTop (nhds (1 / K)) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds hlow (Eventually.of_forall hup)
  -- main term
  have hmain : Tendsto (fun N : ℕ => ∑ r ∈ Finset.range K,
      ((visitCount (fun n => v (K * n + r)) a c (N / K) : ℝ) / (N / K : ℕ))
        * (((N / K : ℕ) : ℝ) / N)) atTop (nhds (∑ r ∈ Finset.range K, (c - a) * (1 / K))) :=
    tendsto_finsetSum _ fun r hr =>
      ((h r (Finset.mem_range.1 hr) a c ha hac hc).comp hq).mul hratio
  have hval : ∑ r ∈ Finset.range K, (c - a) * (1 / (K : ℝ)) = c - a := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
  rw [hval] at hmain
  have hE : Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N, f n)
      - ∑ n ∈ Finset.range (K * (N / K)), f n) / N) atTop (nhds 0) := by
    refine squeeze_zero_norm (fun N => ?_) (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (herr N) (Nat.cast_nonneg _)
  have hsum := hmain.add hE
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop K] with N hN
  have hq0 : (0 : ℝ) < (N / K : ℕ) := by
    have : 0 < N / K := Nat.div_pos hN hK
    exact_mod_cast this
  rw [visitCount_eq_sum]
  show _ = (∑ n ∈ Finset.range N, f n) / N
  rw [sub_div, hblock]
  have : ∀ r ∈ Finset.range K, (visitCount (fun n => v (K * n + r)) a c (N / K) : ℝ)
      / (N / K : ℕ) * (((N / K : ℕ) : ℝ) / N)
      = (visitCount (fun n => v (K * n + r)) a c (N / K) : ℝ) / N := by
    intro r _; field_simp
  rw [Finset.sum_congr rfl this, ← Finset.sum_div]
  ring

theorem fract_natCast_mul_fract (m : ℕ) (t : ℝ) :
    Int.fract (m * Int.fract t) = Int.fract (m * t) := by
  have : (m : ℝ) * Int.fract t = m * t - ((m * ⌊t⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [this, Int.fract_sub_intCast]

/-- **Normality descends from a power base.** -/
theorem isNormal_of_isNormal_pow {b K : ℕ} (hb : 2 ≤ b) (hK : 0 < K) {x : ℝ}
    (h : IsNormal (b ^ K) x) : IsNormal b x := by
  have hbK : 2 ≤ b ^ K := le_trans hb (Nat.le_self_pow hK.ne' b)
  rw [isNormal_iff_equidistributed_orbit b hb]
  rw [isNormal_iff_equidistributed_orbit _ hbK] at h
  refine equidistributed_of_interleave _ K hK fun r _ => ?_
  have hr : (fun n => orbit b x (K * n + r))
      = fun n => Int.fract (((b ^ r : ℕ) : ℝ) * orbit (b ^ K) x n) := by
    funext n
    rw [orbit, orbit, fract_natCast_mul_fract]
    congr 1; push_cast; rw [pow_add, pow_mul]; ring
  rw [hr]
  exact equidistributed_fract_nat_mul _ h (fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) _
    (pow_pos (by omega) r)

end NormalNumbers
