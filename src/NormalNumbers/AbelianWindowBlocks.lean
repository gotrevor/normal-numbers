/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AbelianBlockDensity

/-!
# Block densities at an arbitrary block length

`AbelianBlockDensity.tendsto_blockEvent` is the analytic workhorse behind `AbelianBinaryExample`,
but it is hard-wired to hex digits read four bits at a time.  The C4 constructions
(`AbelianWindowSets.lean`) need the SAME statement at every block length `q`, since a multi-scale
witness uses blocks of unboundedly many bits.  This file is the port: for a sequence `c` normal in
base `B`, any event determined by `n % q` together with the `S` base-`B` digits of `c` starting at
`n / q` has density `#{admissible (residue, word) pairs} / (q · B ^ S)`.

Everything here is a parametrised re-proof; the word-value API (`blk`, `wordVal`, …) is reused
verbatim from `AbelianBlockDensity`.
-/

open Filter Finset Topology

namespace NormalNumbers.Abelian

open NormalNumbers NormalNumbers.PowerBase

/-! ### Counting blocks in a residue class -/

/-- Number of blocks touched by positions `< N` in the residue class `r` mod `q`. -/
def blocksG (q r N : ℕ) : ℕ := (N - r + (q - 1)) / q

lemma lt_blocksG_iff {q r : ℕ} (hq : 0 < q) (hr : r < q) (N m : ℕ) :
    m < blocksG q r N ↔ q * m + r < N := by
  have key : m < (N - r + (q - 1)) / q ↔ (m + 1) * q ≤ N - r + (q - 1) := by
    rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le hq]
  rw [blocksG, key, show (m + 1) * q = q * m + q from by ring]
  omega

lemma blocksG_bounds {q r : ℕ} (hq : 0 < q) (hr : r < q) (N : ℕ) :
    q * blocksG q r N ≤ N + (q - 1) ∧ N ≤ q * blocksG q r N + (q - 1) := by
  set b := blocksG q r N with hb
  clear_value b
  have hupper : ¬ (b < b) := lt_irrefl b
  have h1 : ¬ (q * b + r < N) := by
    intro h
    have hcon : b < blocksG q r N := (lt_blocksG_iff hq hr N b).mpr h
    rw [← hb] at hcon
    exact lt_irrefl b hcon
  refine ⟨?_, by omega⟩
  rcases Nat.eq_zero_or_pos b with hb0 | hb0
  · rw [hb0]; omega
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have h2 : q * b' + r < N := (lt_blocksG_iff hq hr N b').mp (by rw [← hb]; omega)
    have h3 : q * (b' + 1) = q * b' + q := by ring
    omega

lemma tendsto_blocksG_atTop {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    Tendsto (blocksG q r) atTop atTop := by
  refine tendsto_atTop_atTop.2 (fun Bd => ⟨q * Bd + r + 1, fun N hN => ?_⟩)
  by_contra hcon
  push_neg at hcon
  have := (lt_blocksG_iff hq hr N Bd).not.mpr
  have h2 : ¬ (Bd < blocksG q r N) := by omega
  have h3 : ¬ (q * Bd + r < N) := fun h => h2 ((lt_blocksG_iff hq hr N Bd).mpr h)
  omega

lemma tendsto_blocksG_div {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    Tendsto (fun N => (blocksG q r N : ℝ) / N) atTop (𝓝 (1 / q)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have key : ∀ᶠ N : ℕ in atTop, ‖(blocksG q r N : ℝ) / N - 1 / q‖ ≤ (q : ℝ) / N := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨hb1, hb2⟩ := blocksG_bounds hq hr N
    have h1 : (q : ℝ) * (blocksG q r N : ℝ) ≤ (N : ℝ) + (q : ℝ) := by
      have : (q * blocksG q r N : ℕ) ≤ N + q := by omega
      exact_mod_cast this
    have h2 : (N : ℝ) ≤ (q : ℝ) * (blocksG q r N : ℝ) + (q : ℝ) := by
      have : N ≤ q * blocksG q r N + q := by omega
      exact_mod_cast this
    have heq : (blocksG q r N : ℝ) / N - 1 / q
        = ((q : ℝ) * (blocksG q r N : ℝ) - N) / (q * N) := by
      field_simp
    have habs : |(q : ℝ) * (blocksG q r N : ℝ) - N| ≤ q := abs_le.2 ⟨by linarith, by linarith⟩
    have hpos : (0 : ℝ) < (q : ℝ) * N := by positivity
    rw [heq, Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    have h4 : |(q : ℝ) * (blocksG q r N : ℝ) - N| / ((q : ℝ) * N) ≤ (q : ℝ) / ((q : ℝ) * N) := by
      gcongr
    have h5 : (q : ℝ) / ((q : ℝ) * N) = 1 / N := by field_simp
    have h6 : (1 : ℝ) / N ≤ (q : ℝ) / N := by
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      gcongr
    rw [h5] at h4
    linarith
  have h3 : Tendsto (fun N : ℕ => (q : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hz := squeeze_zero_norm' key h3
  have := hz.add (tendsto_const_nhds (x := (1 : ℝ) / q) (f := atTop (α := ℕ)))
  simpa using this

lemma card_res_eq_winCountG (c : ℕ → ℕ) (w : List ℕ) {q r : ℕ} (hq : 0 < q) (hr : r < q) (N : ℕ) :
    ((range N).filter (fun n => n % q = r ∧ MatchesAt c w (n / q))).card
      = winCount c w (blocksG q r N) := by
  classical
  rw [winCount]
  refine Finset.card_nbij' (fun n => n / q) (fun m => q * m + r) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hn
    obtain ⟨hlt, hmod, hmatch⟩ := hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
    refine ⟨(lt_blocksG_iff hq hr N (n / q)).2 ?_, hmatch⟩
    have hd := Nat.div_add_mod n q
    rw [hmod] at hd
    rw [hd]
    exact hlt
  · intro m hm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hm
    obtain ⟨hlt, hmatch⟩ := hm
    have hlt' := (lt_blocksG_iff hq hr N m).1 hlt
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
    refine ⟨hlt', by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hr, ?_⟩
    rw [show (q * m + r) / q = m by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hr]; omega]
    exact hmatch
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hn
    obtain ⟨-, hmod, -⟩ := hn
    show q * (n / q) + r = n
    have hd := Nat.div_add_mod n q
    rw [hmod] at hd
    exact hd
  · intro m hm
    show (q * m + r) / q = m
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hr]
    omega

/-- The density of the positions in residue class `r` mod `q` whose block of `S` base-`B` digits
is a prescribed word. -/
theorem tendsto_res_blkG (c : ℕ → ℕ) {B : ℕ} (hB : 0 < B) (hc : IsNormalSequence B c)
    {q r : ℕ} (hq : 0 < q) (hr : r < q) (S k : ℕ) :
    Tendsto (fun N => (((range N).filter
        (fun n => n % q = r ∧ blk c S (n / q) = wordOf B S k)).card : ℝ) / N)
      atTop (𝓝 (1 / (q * B ^ S))) := by
  classical
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlen : (wordOf B S k).length = S := length_wordOf B S k
  have hcongr : ∀ N : ℕ,
      (((range N).filter (fun n => n % q = r ∧ blk c S (n / q) = wordOf B S k)).card : ℝ)
        = (winCount c (wordOf B S k) (blocksG q r N) : ℝ) := by
    intro N
    have : ((range N).filter (fun n => n % q = r ∧ blk c S (n / q) = wordOf B S k))
        = ((range N).filter (fun n => n % q = r ∧ MatchesAt c (wordOf B S k) (n / q))) := by
      refine Finset.filter_congr (fun n _ => ?_)
      rw [matchesAt_iff_blk, hlen]
    rw [this, card_res_eq_winCountG c _ hq hr N]
  have hw : Tendsto (fun M : ℕ => (winCount c (wordOf B S k) M : ℝ) / M) atTop
      (𝓝 (((B : ℝ) ^ S)⁻¹)) := tendsto_winCount_wordOf hB hc S k
  have hcomp : Tendsto (fun N : ℕ => (winCount c (wordOf B S k) (blocksG q r N) : ℝ) /
      (blocksG q r N : ℝ)) atTop (𝓝 (((B : ℝ) ^ S)⁻¹)) :=
    hw.comp (tendsto_blocksG_atTop hq hr)
  have hprod := hcomp.mul (tendsto_blocksG_div hq hr)
  have hval : ((B : ℝ) ^ S)⁻¹ * (1 / q) = 1 / (q * B ^ S) := by
    field_simp
  rw [hval] at hprod
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hcase : (winCount c (wordOf B S k) (blocksG q r N) : ℝ) / (blocksG q r N : ℝ) *
      ((blocksG q r N : ℝ) / N) = (winCount c (wordOf B S k) (blocksG q r N) : ℝ) / N := by
    rcases Nat.eq_zero_or_pos (blocksG q r N) with hb | hb
    · rw [hb]
      simp [winCount_zero]
    · have : (blocksG q r N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
  rw [hcase, ← hcongr N]

section EventG

variable (c : ℕ → ℕ) (B S q : ℕ) (P : ℕ → List ℕ → Prop) [∀ r v, Decidable (P r v)]

lemma blkG_lt (hcB : ∀ m, c m < B) (m : ℕ) : ∀ d ∈ blk c S m, d < B := by
  intro d hd
  rw [blk, List.mem_map] at hd
  obtain ⟨i, -, rfl⟩ := hd
  exact hcB _

lemma blkG_eq_wordOf (hB : 0 < B) (hcB : ∀ m, c m < B) (m : ℕ) :
    blk c S m = wordOf B S (wordVal B (blk c S m)) := by
  conv_lhs => rw [← wordOf_wordVal B hB (blk c S m) (blkG_lt c B S hcB m)]
  rw [blk_length]

lemma wordVal_blkG_lt (hB : 0 < B) (hcB : ∀ m, c m < B) (m : ℕ) :
    wordVal B (blk c S m) < B ^ S := by
  have := wordVal_lt B hB (blk c S m) (blkG_lt c B S hcB m)
  rwa [blk_length] at this

/-- Pointwise: the event indicator splits over (residue, block word) pairs. -/
lemma indicator_decompG (hB : 0 < B) (hq : 0 < q) (hcB : ∀ m, c m < B) (n : ℕ) :
    (if P (n % q) (blk c S (n / q)) then (1 : ℝ) else 0)
      = ∑ r ∈ range q, ∑ k ∈ range (B ^ S),
          (if P r (wordOf B S k) then (1 : ℝ) else 0) *
            (if n % q = r ∧ blk c S (n / q) = wordOf B S k then (1 : ℝ) else 0) := by
  classical
  set m := n / q with hm
  set k₀ := wordVal B (blk c S m) with hk₀
  have hk₀lt : k₀ < B ^ S := wordVal_blkG_lt c B S hB hcB m
  have hblk : blk c S m = wordOf B S k₀ := blkG_eq_wordOf c B S hB hcB m
  have hr₀ : n % q ∈ range q := Finset.mem_range.mpr (Nat.mod_lt _ hq)
  rw [Finset.sum_eq_single (n % q)]
  · rw [Finset.sum_eq_single k₀]
    · rw [show (if n % q = n % q ∧ blk c S m = wordOf B S k₀ then (1:ℝ) else 0) = 1 from
        if_pos ⟨rfl, hblk⟩, mul_one, ← hblk]
    · intro k hk hne
      have : ¬ (n % q = n % q ∧ blk c S m = wordOf B S k) := by
        rintro ⟨-, h⟩
        exact hne (wordOf_injOn B hB S k₀ k hk₀lt (Finset.mem_range.mp hk) (hblk ▸ h)).symm
      rw [if_neg this, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr hk₀lt) h
  · intro r hr hne
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have : ¬ (n % q = r ∧ blk c S m = wordOf B S k) := fun h => hne h.1.symm
    rw [if_neg this, mul_zero]
  · intro h; exact absurd hr₀ h

/-- **Block-density workhorse, any block length.**  Any event determined by the residue of the
position mod `q` and the `S` base-`B` digits of `c` starting at the block index has the density
predicted by the i.i.d. uniform model on base-`B` words. -/
theorem tendsto_blockEventG (hB : 0 < B) (hq : 0 < q) (hcB : ∀ m, c m < B)
    (hc : IsNormalSequence B c) :
    Tendsto (fun N => (((range N).filter (fun n => P (n % q) (blk c S (n / q)))).card : ℝ) / N)
      atTop (𝓝 ((∑ r ∈ range q, ∑ k ∈ range (B ^ S),
        if P r (wordOf B S k) then (1 : ℝ) else 0) / (q * B ^ S))) := by
  classical
  have hdecomp : ∀ N : ℕ,
      (((range N).filter (fun n => P (n % q) (blk c S (n / q)))).card : ℝ)
        = ∑ r ∈ range q, ∑ k ∈ range (B ^ S),
            (if P r (wordOf B S k) then (1 : ℝ) else 0) *
              (((range N).filter
                (fun n => n % q = r ∧ blk c S (n / q) = wordOf B S k)).card : ℝ) := by
    intro N
    have hL : (((range N).filter (fun n => P (n % q) (blk c S (n / q)))).card : ℝ)
        = ∑ n ∈ range N, (if P (n % q) (blk c S (n / q)) then (1 : ℝ) else 0) := by
      rw [Finset.card_filter]; push_cast; rfl
    have hR : ∀ r k, (((range N).filter
          (fun n => n % q = r ∧ blk c S (n / q) = wordOf B S k)).card : ℝ)
        = ∑ n ∈ range N, (if n % q = r ∧ blk c S (n / q) = wordOf B S k then (1 : ℝ) else 0) := by
      intro r k; rw [Finset.card_filter]; push_cast; rfl
    rw [hL, Finset.sum_congr rfl (fun n _ => indicator_decompG c B S q P hB hq hcB n),
      Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hR r k, Finset.mul_sum]
  have hlim : Tendsto (fun N => ∑ r ∈ range q, ∑ k ∈ range (B ^ S),
      (if P r (wordOf B S k) then (1 : ℝ) else 0) *
        ((((range N).filter
          (fun n => n % q = r ∧ blk c S (n / q) = wordOf B S k)).card : ℝ) / N)) atTop
      (𝓝 (∑ r ∈ range q, ∑ k ∈ range (B ^ S),
        (if P r (wordOf B S k) then (1 : ℝ) else 0) * (1 / (q * B ^ S)))) := by
    refine tendsto_finsetSum _ (fun r hr => tendsto_finsetSum _ (fun k _ => ?_))
    exact tendsto_const_nhds.mul
      (tendsto_res_blkG c hB hc hq (Finset.mem_range.mp hr) S k)
  have hval : (∑ r ∈ range q, ∑ k ∈ range (B ^ S),
      (if P r (wordOf B S k) then (1 : ℝ) else 0) * (1 / (q * B ^ S)))
      = (∑ r ∈ range q, ∑ k ∈ range (B ^ S),
        if P r (wordOf B S k) then (1 : ℝ) else 0) / (q * B ^ S) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hval] at hlim
  refine hlim.congr (fun N => ?_)
  rw [hdecomp N, Finset.sum_div]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun k _ => by ring)

end EventG

end NormalNumbers.Abelian
