/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AbelianBlockDensity
import NormalNumbers.AbelianNormal

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

open NormalNumbers NormalNumbers.PowerBase NormalNumbers.Walsh

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

/-! ### Block-driven binary sequences and their exact window laws

`blockSeq g c q n = g (n % q) (c (n / q))` reads a base-`B` normal sequence `c` `q` bits at a
time through an arbitrary table `g`.  This is the aperiodic block-i.i.d. class: the blocks are
i.i.d. with the law `g_*(uniform on B letters)`, and the residue `n % q` supplies the uniform
random offset that makes it stationary.  Every window statistic is an exact finite sum. -/

section BlockSeq

/-- The binary sequence read off `c` in blocks of `q` bits through the table `g`. -/
def blockSeq (g : ℕ → ℕ → ℕ) (c : ℕ → ℕ) (q : ℕ) (n : ℕ) : ℕ := g (n % q) (c (n / q))

/-- One-count of the length-`L` window at residue `r` inside a block word `v`. -/
def winOnes (g : ℕ → ℕ → ℕ) (q L r : ℕ) (v : List ℕ) : ℕ :=
  ((range L).filter (fun i => g ((r + i) % q) (v.getD ((r + i) / q) 0) = 1)).card

theorem onesCount_blockSeq (g : ℕ → ℕ → ℕ) (c : ℕ → ℕ) {q : ℕ} (hq : 0 < q) (L S : ℕ)
    (hS : q + L ≤ S) (n : ℕ) :
    onesCount (blockSeq g c q) L n = winOnes g q L (n % q) (blk c S (n / q)) := by
  classical
  unfold onesCount windowSet winOnes
  congr 1
  refine Finset.filter_congr (fun i hi => ?_)
  have hiL : i < L := Finset.mem_range.mp hi
  have hr : n % q < q := Nat.mod_lt _ hq
  have hidx : (n % q + i) / q < S := by
    have h1 : (n % q + i) / q ≤ n % q + i := Nat.div_le_self _ _
    omega
  have hn : n + i = q * (n / q) + (n % q + i) := by
    have := Nat.div_add_mod n q
    omega
  have hmod : (n + i) % q = (n % q + i) % q := by
    rw [hn, Nat.add_comm (q * (n / q)) _, Nat.mul_comm q (n / q),
      Nat.add_mul_mod_self_right]
  have hdiv : (n + i) / q = n / q + (n % q + i) / q := by
    rw [hn, Nat.add_comm (q * (n / q)) _, Nat.mul_comm q (n / q),
      Nat.add_mul_div_right _ _ hq]
    omega
  rw [blockSeq, hmod, hdiv, blk_getD c S (n / q) _ hidx]

/-- The exact limiting weight-`j` frequency of a block-driven sequence. -/
noncomputable def blockFreq (g : ℕ → ℕ → ℕ) (q B S L j : ℕ) : ℝ :=
  (∑ r ∈ range q, ∑ k ∈ range (B ^ S),
    if winOnes g q L r (wordOf B S k) = j then (1 : ℝ) else 0) / (q * B ^ S)

/-- **The block-driven window law.** -/
theorem tendsto_onesFreq_blockSeq (g : ℕ → ℕ → ℕ) (c : ℕ → ℕ) {B q : ℕ} (hB : 0 < B)
    (hq : 0 < q) (hcB : ∀ m, c m < B) (hc : IsNormalSequence B c) (L S : ℕ) (hS : q + L ≤ S)
    (j : ℕ) :
    Tendsto (onesFreq (blockSeq g c q) L j) atTop (𝓝 (blockFreq g q B S L j)) := by
  classical
  have h := tendsto_blockEventG c B S q (fun r v => winOnes g q L r v = j) hB hq hcB hc
  refine h.congr (fun N => ?_)
  have hset : ((range N).filter (fun n => onesCount (blockSeq g c q) L n = j))
      = ((range N).filter (fun n => winOnes g q L (n % q) (blk c S (n / q)) = j)) := by
    ext n
    simp only [Finset.mem_filter, onesCount_blockSeq g c hq L S hS n]
  unfold onesFreq
  rw [hset]

end BlockSeq

end NormalNumbers.Abelian
