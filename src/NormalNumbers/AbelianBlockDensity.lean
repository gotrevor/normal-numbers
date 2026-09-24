/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerBaseLimit

/-!
# Block densities along an arithmetic progression of bit positions

The binary construction of `AbelianBinaryExample` reads a base-16 normal sequence `c` four bits
at a time.  Every statistic of a bounded window of the resulting bit sequence is a function of
`n % 4` together with a bounded block of hex digits `c (n/4), …, c (n/4 + S - 1)`.  This file
supplies the analytic workhorse: such an event has density
`(number of admissible (residue, hex word) pairs) / (4 · 16^S)`.
-/

open Filter Finset Topology

namespace NormalNumbers.Abelian

open NormalNumbers NormalNumbers.PowerBase

/-! ### Words read off a sequence -/

/-- The length-`S` word of `c` starting at position `m`. -/
def blk (c : ℕ → ℕ) (S m : ℕ) : List ℕ := (List.range S).map (fun i => c (m + i))

@[simp] lemma blk_length (c : ℕ → ℕ) (S m : ℕ) : (blk c S m).length = S := by simp [blk]

lemma blk_getElem (c : ℕ → ℕ) (S m j : ℕ) (hj : j < S) :
    (blk c S m)[j]'(by simpa using hj) = c (m + j) := by
  simp [blk]

lemma blk_getD (c : ℕ → ℕ) (S m j : ℕ) (hj : j < S) : (blk c S m).getD j 0 = c (m + j) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), blk_getElem c S m j hj]

lemma matchesAt_iff_blk (s : ℕ → ℕ) (v : List ℕ) (m : ℕ) :
    MatchesAt s v m ↔ blk s v.length m = v := by
  constructor
  · intro h
    refine List.ext_getElem (by simp) (fun j h1 h2 => ?_)
    have hj : j < v.length := h2
    rw [blk_getElem s v.length m j hj, h j hj, List.getD_eq_getElem _ _ hj]
  · intro h j hj
    rw [← blk_getD s v.length m j hj]
    exact congrArg (fun l => List.getD l j 0) h

/-! ### Numeric value of a word -/

/-- The numeric value in base `b` of a word, most significant digit first. -/
def wordVal (b : ℕ) (v : List ℕ) : ℕ := v.foldl (fun a d => a * b + d) 0

@[simp] lemma wordVal_nil (b : ℕ) : wordVal b [] = 0 := rfl

lemma wordVal_append (b : ℕ) (v : List ℕ) (d : ℕ) :
    wordVal b (v ++ [d]) = wordVal b v * b + d := by
  simp [wordVal]

lemma wordVal_lt (b : ℕ) (hb : 0 < b) (v : List ℕ) (hv : ∀ d ∈ v, d < b) :
    wordVal b v < b ^ v.length := by
  induction v using List.reverseRecOn with
  | nil => simpa using hb
  | append_singleton v d ih =>
    have hd : d < b := hv d (by simp)
    have hv' : ∀ x ∈ v, x < b := fun x hx => hv x (by simp [hx])
    have := ih hv'
    rw [wordVal_append, List.length_append]
    simp only [List.length_cons, List.length_nil, pow_succ]
    calc wordVal b v * b + d < wordVal b v * b + b := by omega
      _ = (wordVal b v + 1) * b := by ring
      _ ≤ b ^ v.length * b := Nat.mul_le_mul_right b (by omega)

lemma wordOf_wordVal (b : ℕ) (hb : 0 < b) (v : List ℕ) (hv : ∀ d ∈ v, d < b) :
    wordOf b v.length (wordVal b v) = v := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v d ih =>
    have hd : d < b := hv d (by simp)
    have hv' : ∀ x ∈ v, x < b := fun x hx => hv x (by simp [hx])
    rw [List.length_append]
    simp only [List.length_cons, List.length_nil]
    rw [wordVal_append, wordOf_append b v.length (wordVal b v) d hb hd, ih hv']

lemma wordVal_wordOf (b : ℕ) (hb : 0 < b) (m k : ℕ) (hk : k < b ^ m) :
    wordVal b (wordOf b m k) = k := by
  induction m generalizing k with
  | zero =>
    have hk0 : k = 0 := by simp only [pow_zero] at hk; omega
    subst hk0; simp
  | succ m ih =>
    rw [pow_succ] at hk
    have hkb : k / b < b ^ m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)
    have hmod : k % b < b := Nat.mod_lt _ hb
    have hsplit : k / b * b + k % b = k := Nat.div_add_mod' k b
    conv_lhs => rw [← hsplit]
    rw [wordOf_append b m (k / b) (k % b) hb hmod, wordVal_append, ih _ hkb, hsplit]

lemma wordOf_injOn (b : ℕ) (hb : 0 < b) (m k k' : ℕ) (hk : k < b ^ m) (hk' : k' < b ^ m)
    (h : wordOf b m k = wordOf b m k') : k = k' := by
  rw [← wordVal_wordOf b hb m k hk, ← wordVal_wordOf b hb m k' hk', h]


/-! ### The density of a residue-and-block event -/

/-- Number of blocks touched by bit positions `< N` in the residue class `r` mod `4`. -/
def blocks (r N : ℕ) : ℕ := (N - r + 3) / 4

lemma lt_blocks_iff {r : ℕ} (hr : r < 4) (N q : ℕ) : q < blocks r N ↔ 4 * q + r < N := by
  rw [blocks, Nat.lt_div_iff_mul_lt (by norm_num)]
  omega

lemma blocks_bounds (r N : ℕ) (hr : r < 4) : 4 * blocks r N ≤ N + 3 ∧ N ≤ 4 * blocks r N + 3 := by
  have h := Nat.div_add_mod (N - r + 3) 4
  have h2 : (N - r + 3) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  unfold blocks
  omega

lemma tendsto_blocks_atTop (r : ℕ) (hr : r < 4) : Tendsto (blocks r) atTop atTop := by
  refine tendsto_atTop_atTop.2 (fun B => ⟨4 * B + r, fun N hN => ?_⟩)
  have := blocks_bounds r N hr
  omega

/-- Counting the residue class `r` mod `4` of bit positions below `N` whose block index carries
the word `w` is the same as counting the word among the first `blocks r N` block positions. -/
lemma card_res_eq_winCount (c : ℕ → ℕ) (w : List ℕ) (r N : ℕ) (hr : r < 4) :
    ((range N).filter (fun n => n % 4 = r ∧ MatchesAt c w (n / 4))).card
      = winCount c w (blocks r N) := by
  classical
  rw [winCount]
  refine Finset.card_nbij' (fun n => n / 4) (fun m => 4 * m + r) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hn
    obtain ⟨hlt, hmod, hmatch⟩ := hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
    refine ⟨(lt_blocks_iff hr N (n / 4)).2 ?_, hmatch⟩
    omega
  · intro m hm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hm
    obtain ⟨hlt, hmatch⟩ := hm
    have hlt' := (lt_blocks_iff hr N m).1 hlt
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
    refine ⟨hlt', by omega, ?_⟩
    rw [show (4 * m + r) / 4 = m by omega]
    exact hmatch
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hn
    obtain ⟨-, hmod, -⟩ := hn
    show 4 * (n / 4) + r = n
    omega
  · intro m hm
    show (4 * m + r) / 4 = m
    omega

lemma tendsto_blocks_div (r : ℕ) (hr : r < 4) :
    Tendsto (fun N => (blocks r N : ℝ) / N) atTop (𝓝 (1 / 4)) := by
  have key : ∀ᶠ N : ℕ in atTop, ‖(blocks r N : ℝ) / N - 1 / 4‖ ≤ 3 / N := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : 4 * (blocks r N : ℝ) ≤ (N : ℝ) + 3 := by exact_mod_cast (blocks_bounds r N hr).1
    have h2 : (N : ℝ) ≤ 4 * (blocks r N : ℝ) + 3 := by exact_mod_cast (blocks_bounds r N hr).2
    have heq : (blocks r N : ℝ) / N - 1 / 4 = (4 * (blocks r N : ℝ) - N) / (4 * N) := by
      field_simp
    have habs : |4 * (blocks r N : ℝ) - N| ≤ 3 := abs_le.2 ⟨by linarith, by linarith⟩
    have hpos : (0 : ℝ) < 4 * N := by positivity
    rw [heq, Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    have hs1 : |4 * (blocks r N : ℝ) - N| / (4 * N) ≤ 3 / (4 * N) := by gcongr
    have hs2 : (3 : ℝ) / (4 * N) = (3 / N) / 4 := by field_simp
    have hs3 : (0 : ℝ) ≤ 3 / N := by positivity
    linarith [hs1, hs2 ▸ hs1]
  have h3 : Tendsto (fun N : ℕ => (3 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 3
  have hz := squeeze_zero_norm' key h3
  have := hz.add (tendsto_const_nhds (x := (1 : ℝ) / 4) (f := atTop (α := ℕ)))
  simpa using this


/-- The density of the bit positions in residue class `r` mod `4` whose block of `S` hex digits
is a prescribed word. -/
theorem tendsto_res_blk (c : ℕ → ℕ) (hc : IsNormalSequence 16 c) (S k r : ℕ) (hr : r < 4) :
    Tendsto (fun N => (((range N).filter
        (fun n => n % 4 = r ∧ blk c S (n / 4) = wordOf 16 S k)).card : ℝ) / N)
      atTop (𝓝 (1 / (4 * 16 ^ S))) := by
  classical
  have hlen : (wordOf 16 S k).length = S := length_wordOf 16 S k
  have hcongr : ∀ N : ℕ,
      (((range N).filter (fun n => n % 4 = r ∧ blk c S (n / 4) = wordOf 16 S k)).card : ℝ)
        = (winCount c (wordOf 16 S k) (blocks r N) : ℝ) := by
    intro N
    have : ((range N).filter (fun n => n % 4 = r ∧ blk c S (n / 4) = wordOf 16 S k))
        = ((range N).filter (fun n => n % 4 = r ∧ MatchesAt c (wordOf 16 S k) (n / 4))) := by
      refine Finset.filter_congr (fun n _ => ?_)
      rw [matchesAt_iff_blk, hlen]
    rw [this, card_res_eq_winCount c _ r N hr]
  have hw : Tendsto (fun M : ℕ => (winCount c (wordOf 16 S k) M : ℝ) / M) atTop
      (𝓝 (((16 : ℝ) ^ S)⁻¹)) := tendsto_winCount_wordOf (by norm_num) hc S k
  have hcomp : Tendsto (fun N : ℕ => (winCount c (wordOf 16 S k) (blocks r N) : ℝ) /
      (blocks r N : ℝ)) atTop (𝓝 (((16 : ℝ) ^ S)⁻¹)) :=
    hw.comp (tendsto_blocks_atTop r hr)
  have hprod := hcomp.mul (tendsto_blocks_div r hr)
  have hval : ((16 : ℝ) ^ S)⁻¹ * (1 / 4) = 1 / (4 * 16 ^ S) := by
    rw [one_div, one_div]
    rw [← mul_inv]
    ring_nf
  rw [hval] at hprod
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hcase : (winCount c (wordOf 16 S k) (blocks r N) : ℝ) / (blocks r N : ℝ) *
      ((blocks r N : ℝ) / N) = (winCount c (wordOf 16 S k) (blocks r N) : ℝ) / N := by
    rcases Nat.eq_zero_or_pos (blocks r N) with hb | hb
    · rw [hb]
      simp [winCount_zero]
    · have : (blocks r N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
  rw [hcase, ← hcongr N]


section Event

variable (c : ℕ → ℕ) (S : ℕ) (P : ℕ → List ℕ → Prop) [∀ r v, Decidable (P r v)]

lemma blk_lt (hc16 : ∀ m, c m < 16) (m : ℕ) : ∀ d ∈ blk c S m, d < 16 := by
  intro d hd
  rw [blk, List.mem_map] at hd
  obtain ⟨i, -, rfl⟩ := hd
  exact hc16 _

lemma blk_eq_wordOf (hc16 : ∀ m, c m < 16) (m : ℕ) :
    blk c S m = wordOf 16 S (wordVal 16 (blk c S m)) := by
  conv_lhs => rw [← wordOf_wordVal 16 (by norm_num) (blk c S m) (blk_lt c S hc16 m)]
  rw [blk_length]

lemma wordVal_blk_lt (hc16 : ∀ m, c m < 16) (m : ℕ) : wordVal 16 (blk c S m) < 16 ^ S := by
  have := wordVal_lt 16 (by norm_num) (blk c S m) (blk_lt c S hc16 m)
  rwa [blk_length] at this

/-- Pointwise: the event indicator splits over (residue, block word) pairs. -/
lemma indicator_decomp (hc16 : ∀ m, c m < 16) (n : ℕ) :
    (if P (n % 4) (blk c S (n / 4)) then (1 : ℝ) else 0)
      = ∑ r ∈ range 4, ∑ k ∈ range (16 ^ S),
          (if P r (wordOf 16 S k) then (1 : ℝ) else 0) *
            (if n % 4 = r ∧ blk c S (n / 4) = wordOf 16 S k then (1 : ℝ) else 0) := by
  classical
  set m := n / 4 with hm
  set k₀ := wordVal 16 (blk c S m) with hk₀
  have hk₀lt : k₀ < 16 ^ S := wordVal_blk_lt c S hc16 m
  have hblk : blk c S m = wordOf 16 S k₀ := blk_eq_wordOf c S hc16 m
  have hr₀ : n % 4 ∈ range 4 := Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num))
  rw [Finset.sum_eq_single (n % 4)]
  · rw [Finset.sum_eq_single k₀]
    · rw [show (if n % 4 = n % 4 ∧ blk c S m = wordOf 16 S k₀ then (1:ℝ) else 0) = 1 from
        if_pos ⟨rfl, hblk⟩, mul_one, ← hblk]
    · intro k hk hne
      have : ¬ (n % 4 = n % 4 ∧ blk c S m = wordOf 16 S k) := by
        rintro ⟨-, h⟩
        exact hne (wordOf_injOn 16 (by norm_num) S k₀ k hk₀lt (Finset.mem_range.mp hk)
          (hblk ▸ h)).symm
      rw [if_neg this, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr hk₀lt) h
  · intro r hr hne
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have : ¬ (n % 4 = r ∧ blk c S m = wordOf 16 S k) := fun h => hne h.1.symm
    rw [if_neg this, mul_zero]
  · intro h; exact absurd hr₀ h

/-- **Block-density workhorse.**  Any event determined by the residue of the bit position mod `4`
and the `S` hex digits of `c` starting at the block index has the density predicted by the
i.i.d. uniform model on hex words. -/
theorem tendsto_blockEvent (hc16 : ∀ m, c m < 16) (hc : IsNormalSequence 16 c) :
    Tendsto (fun N => (((range N).filter (fun n => P (n % 4) (blk c S (n / 4)))).card : ℝ) / N)
      atTop (𝓝 ((∑ r ∈ range 4, ∑ k ∈ range (16 ^ S),
        if P r (wordOf 16 S k) then (1 : ℝ) else 0) / (4 * 16 ^ S))) := by
  classical
  have hdecomp : ∀ N : ℕ,
      (((range N).filter (fun n => P (n % 4) (blk c S (n / 4)))).card : ℝ)
        = ∑ r ∈ range 4, ∑ k ∈ range (16 ^ S),
            (if P r (wordOf 16 S k) then (1 : ℝ) else 0) *
              (((range N).filter
                (fun n => n % 4 = r ∧ blk c S (n / 4) = wordOf 16 S k)).card : ℝ) := by
    intro N
    have hL : (((range N).filter (fun n => P (n % 4) (blk c S (n / 4)))).card : ℝ)
        = ∑ n ∈ range N, (if P (n % 4) (blk c S (n / 4)) then (1 : ℝ) else 0) := by
      rw [Finset.card_filter]; push_cast; rfl
    have hR : ∀ r k, (((range N).filter
          (fun n => n % 4 = r ∧ blk c S (n / 4) = wordOf 16 S k)).card : ℝ)
        = ∑ n ∈ range N, (if n % 4 = r ∧ blk c S (n / 4) = wordOf 16 S k then (1 : ℝ) else 0) := by
      intro r k; rw [Finset.card_filter]; push_cast; rfl
    rw [hL, Finset.sum_congr rfl (fun n _ => indicator_decomp c S P hc16 n), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hR r k, Finset.mul_sum]
  have hlim : Tendsto (fun N => ∑ r ∈ range 4, ∑ k ∈ range (16 ^ S),
      (if P r (wordOf 16 S k) then (1 : ℝ) else 0) *
        ((((range N).filter
          (fun n => n % 4 = r ∧ blk c S (n / 4) = wordOf 16 S k)).card : ℝ) / N)) atTop
      (𝓝 (∑ r ∈ range 4, ∑ k ∈ range (16 ^ S),
        (if P r (wordOf 16 S k) then (1 : ℝ) else 0) * (1 / (4 * 16 ^ S)))) := by
    refine tendsto_finsetSum _ (fun r hr => tendsto_finsetSum _ (fun k _ => ?_))
    exact tendsto_const_nhds.mul (tendsto_res_blk c hc S k r (Finset.mem_range.mp hr))
  have hval : (∑ r ∈ range 4, ∑ k ∈ range (16 ^ S),
      (if P r (wordOf 16 S k) then (1 : ℝ) else 0) * (1 / (4 * 16 ^ S)))
      = (∑ r ∈ range 4, ∑ k ∈ range (16 ^ S),
        if P r (wordOf 16 S k) then (1 : ℝ) else 0) / (4 * 16 ^ S) := by
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

end Event

end NormalNumbers.Abelian
