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

theorem sum_le_sum_add_of_eventually (f g : ℕ → ℝ) (N₀ : ℕ) (hf : ∀ k, f k ≤ 1)
    (hg : ∀ k, 0 ≤ g k) (h : ∀ k, N₀ ≤ k → f k ≤ g k) (n : ℕ) :
    ∑ k ∈ Finset.range n, f k ≤ ∑ k ∈ Finset.range n, g k + N₀ := by
  have h1 : ∑ k ∈ Finset.range n, f k
      ≤ ∑ k ∈ Finset.range n, (g k + if k < N₀ then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum fun k _ => ?_
    split_ifs with hk
    · linarith [hf k, hg k]
    · linarith [h k (by omega)]
  have h2 : ∑ k ∈ Finset.range n, (if k < N₀ then (1 : ℝ) else 0) ≤ N₀ := by
    rw [Finset.sum_boole]
    have : ((Finset.range n).filter (· < N₀)).card ≤ N₀ := by
      calc ((Finset.range n).filter (· < N₀)).card ≤ (Finset.range N₀).card :=
            Finset.card_le_card fun k hk => by
              simp only [Finset.mem_filter] at hk; exact Finset.mem_range.2 hk.2
        _ = N₀ := Finset.card_range _
    simpa using (show (((Finset.range n).filter (· < N₀)).card : ℝ) ≤ N₀ by exact_mod_cast this)
  rw [Finset.sum_add_distrib] at h1
  linarith

/-- **Two-sided equidistribution stability**: perturbing an equidistributed `[0,1)`-sequence by
any vanishing amount (either sign), mod 1, preserves equidistribution. -/
theorem equidistributed_of_fract_perturb_abs (u δ : ℕ → ℝ)
    (hu : Equidistributed u) (hu01 : ∀ n, u n ∈ Set.Ico (0 : ℝ) 1)
    (hδ : Tendsto δ atTop (nhds 0)) :
    Equidistributed (fun n => Int.fract (u n + δ n)) := by
  intro a c ha hac hc1
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e : ℝ := min (ε / 16) (1 / 4) with he_def
  have he0 : 0 < e := lt_min (by positivity) (by norm_num)
  have hee : e ≤ ε / 16 := min_le_left _ _
  have he4 : e ≤ 1 / 4 := min_le_right _ _
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.1 hδ) e he0
  have hδe : ∀ k, N₀ ≤ k → |δ k| < e := fun k hk => by
    simpa [Real.dist_eq] using hN₀ k hk
  set I : (ℕ → ℝ) → ℝ → ℝ → ℕ → ℝ := fun w a' c' k => if w k ∈ Set.Ico a' c' then 1 else 0
  have hI01 : ∀ w a' c' k, 0 ≤ I w a' c' k ∧ I w a' c' k ≤ 1 := by
    intro w a' c' k; simp only [I]; split_ifs <;> norm_num
  set v : ℕ → ℝ := fun n => Int.fract (u n + δ n)
  -- intervals
  set a1 := max (a - e) 0; set c1 := min (c + e) 1
  set a2 := min (a + 1 - e) 1
  set c3 := max (c + e - 1) 0
  set a4 := min (a + e) c; set c4 := max a4 (c - e)
  have hupper : ∀ k, N₀ ≤ k → I v a c k ≤ I u a1 (max a1 c1) k + I u a2 1 k + I u 0 c3 k := by
    intro k hk
    have hd := abs_lt.1 (hδe k hk)
    obtain ⟨hx0, hx1⟩ := hu01 k
    simp only [I, v]
    by_cases hP : Int.fract (u k + δ k) ∈ Set.Ico a c
    · rw [if_pos hP]
      obtain ⟨hp1, hp2⟩ := hP
      have hcases : (0 ≤ u k + δ k ∧ u k + δ k < 1) ∨ u k + δ k < 0 ∨ 1 ≤ u k + δ k := by
        by_cases h0 : 0 ≤ u k + δ k
        · by_cases h1 : u k + δ k < 1
          · exact Or.inl ⟨h0, h1⟩
          · exact Or.inr (Or.inr (not_lt.1 h1))
        · exact Or.inr (Or.inl (not_le.1 h0))
      rcases hcases with ⟨h0, h1⟩ | h0 | h1
      · rw [Int.fract_eq_self.mpr ⟨h0, h1⟩] at hp1 hp2
        have : u k ∈ Set.Ico a1 (max a1 c1) :=
          ⟨max_le (by linarith) hx0, lt_max_of_lt_right (lt_min (by linarith) hx1)⟩
        rw [if_pos this]
        split_ifs <;> norm_num
      · have hfr : Int.fract (u k + δ k) = u k + δ k + 1 := by
          rw [← Int.fract_add_one, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
        rw [hfr] at hp1 hp2
        have : u k ∈ Set.Ico 0 c3 := ⟨hx0, lt_max_of_lt_left (by linarith)⟩
        rw [if_pos this]
        split_ifs <;> norm_num
      · have hfr : Int.fract (u k + δ k) = u k + δ k - 1 := by
          rw [← Int.fract_sub_one, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
        rw [hfr] at hp1 hp2
        have : u k ∈ Set.Ico a2 1 := ⟨(min_le_left _ _).trans (by linarith), hx1⟩
        rw [if_pos this]
        split_ifs <;> norm_num
    · rw [if_neg hP]
      linarith [(hI01 u a1 (max a1 c1) k).1, (hI01 u a2 1 k).1, (hI01 u 0 c3 k).1]
  have hlower : ∀ k, N₀ ≤ k → I u a4 c4 k ≤ I v a c k := by
    intro k hk
    have hd := abs_lt.1 (hδe k hk)
    obtain ⟨hx0, hx1⟩ := hu01 k
    simp only [I, v]
    by_cases hP : u k ∈ Set.Ico a4 c4
    · obtain ⟨hp1, hp2⟩ := hP
      have hlt : u k < c - e := by
        rcases lt_max_iff.1 hp2 with h | h
        · linarith
        · exact h
      have hae : a + e ≤ u k := by
        rcases min_cases (a + e) c with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [show a4 = a + e from h1] at hp1; exact hp1
        · rw [show a4 = c from h1] at hp1; linarith
      rw [if_pos ⟨hp1, hp2⟩, if_pos]
      rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
      exact ⟨by linarith, by linarith⟩
    · rw [if_neg hP]; exact (hI01 v a c k).1
  have hfreq : ∀ a' c', 0 ≤ a' → a' ≤ c' → c' ≤ 1 → Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.range n, I u a' c' k) / n) atTop (nhds (c' - a')) := by
    intro a' c' h1 h2 h3
    have := hu a' c' h1 h2 h3
    simp_rw [visitCount_eq_sum] at this
    exact this
  have hc0 : 0 ≤ c := ha.trans hac
  have hle1 : a1 ≤ max a1 c1 := le_max_left _ _
  have hmx : max a1 c1 ≤ 1 := max_le (max_le (by linarith) zero_le_one) (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 (hfreq a1 (max a1 c1) (le_max_right _ _) hle1 hmx) e he0
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1
    (hfreq a2 1 (le_min (by linarith) zero_le_one) (min_le_right _ _) le_rfl) e he0
  obtain ⟨N₃, hN₃⟩ := Metric.tendsto_atTop.1
    (hfreq 0 c3 le_rfl (le_max_right _ _) (max_le (by linarith) zero_le_one)) e he0
  have ha4 : 0 ≤ a4 := le_min (by positivity) hc0
  obtain ⟨N₅, hN₅⟩ := Metric.tendsto_atTop.1
    (hfreq a4 c4 ha4 (le_max_left _ _) (max_le ((min_le_right _ _).trans hc1) (by linarith))) e he0
  obtain ⟨N₄, hN₄⟩ := Metric.tendsto_atTop.mp
    (tendsto_const_div_atTop_nhds_zero_nat (N₀ : ℝ)) e he0
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) (max N₅ 1)), fun n hn => ?_⟩
  have b₁ := hN₁ n (by omega)
  have b₂ := hN₂ n (by omega)
  have b₃ := hN₃ n (by omega)
  have b₄ := hN₄ n (by omega)
  have b₅ := hN₅ n (by omega)
  rw [Real.dist_eq, abs_sub_lt_iff] at b₁ b₂ b₃ b₄ b₅
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hup := sum_le_sum_add_of_eventually (I v a c)
    (fun k => I u a1 (max a1 c1) k + I u a2 1 k + I u 0 c3 k) N₀ (fun k => (hI01 v a c k).2)
    (fun k => by linarith [(hI01 u a1 (max a1 c1) k).1, (hI01 u a2 1 k).1, (hI01 u 0 c3 k).1])
    hupper n
  have hlo := sum_le_sum_add_of_eventually (I u a4 c4) (I v a c) N₀
    (fun k => (hI01 u a4 c4 k).2) (fun k => (hI01 v a c k).1) hlower n
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hup
  have hup' := div_le_div_of_nonneg_right hup hnR
  have hlo' := div_le_div_of_nonneg_right hlo hnR
  simp only [add_div] at hup' hlo'
  have hV : (visitCount (fun n => Int.fract (u n + δ n)) a c n : ℝ) / n
      = (∑ k ∈ Finset.range n, I v a c k) / n := by rw [visitCount_eq_sum]
  rw [Real.dist_eq, abs_sub_lt_iff, hV]
  have l1 : max a1 c1 - a1 ≤ c - a + 2 * e := by
    rcases max_cases a1 c1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
    · linarith
    · have : a - e ≤ a1 := le_max_left _ _
      have : c1 ≤ c + e := min_le_left _ _
      linarith
  have l2 : 1 - a2 ≤ e := by
    have : 1 - e ≤ a2 := le_min (by linarith) (by linarith)
    linarith
  have l3 : c3 - 0 ≤ e := by
    have : c3 ≤ e := max_le (by linarith) he0.le
    linarith
  have l5 : c - a - 2 * e ≤ c4 - a4 := by
    have : c - e ≤ c4 := le_max_right _ _
    have : a4 ≤ a + e := min_le_left _ _
    linarith
  constructor <;> linarith

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
