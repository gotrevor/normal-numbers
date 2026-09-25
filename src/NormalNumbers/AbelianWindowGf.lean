/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AbelianWindowSets

/-!
# The block-window generating function, at an arbitrary block length

`AbelianWindowOdd.lean` computes `blockFreq` for one hand-built table (`q = 2`, `B = 8`) by
explicit polynomial algebra.  This file is the general engine behind that computation, and behind
every further C4 witness.

For a table `g : ℕ → ℕ → ℕ` read `q` bits at a time off a base-`B` digit stream, the one-count of
the length-`L` window at residue `r` is a SUM over the blocks it meets of a per-block statistic of
that block's digit alone.  Hence the window generating function over all base-`B` words of length
`S` factors as a PRODUCT of per-block digit generating functions (`wordGf_eq`,
`winGf_eq_prod`).

The consequence used downstream (`blockFreq_eq_binomial_of_seg`): if every trace the window makes
on a block has a digit generating function equal to `B · ((1+X)/2) ^ (length of the trace)` — i.e.
that segment of the block law has an exactly Binomial one-count — then the whole window law is
exactly Binomial(`L`, 1/2), so the sequence is abelian at `L`.
-/

open Finset Polynomial

namespace NormalNumbers.Abelian

open NormalNumbers.PowerBase

/-! ## Words factor -/

/-- The generating function of a position-dependent digit statistic, over all base-`B` words of
length `m`. -/
noncomputable def wordGf (B m : ℕ) (f : ℕ → ℕ → ℕ) : ℝ[X] :=
  ∑ k ∈ range (B ^ m), X ^ (∑ i ∈ range m, f i ((wordOf B m k).getD i 0))

/-- **Words factor (ring form).**  A sum over all base-`B` words of length `m` of a product of
per-position functions of that position's digit is the product of the per-position digit sums.
This is the workhorse behind every exact block-law computation: coupled positions are handled by
splitting the sum into product sets first, and each piece is then a product over positions. -/
theorem sum_prod_wordOf {R : Type*} [CommRing R] (B : ℕ) (hB : 0 < B) (F : ℕ → ℕ → R) (m : ℕ) :
    ∑ k ∈ range (B ^ m), ∏ i ∈ range m, F i ((wordOf B m k).getD i 0)
      = ∏ i ∈ range m, ∑ d ∈ range B, F i d := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
      have hR : (∏ i ∈ range m, ∑ d ∈ range B, F i d) * (∑ d ∈ range B, F m d)
          = ∑ p ∈ (range (B ^ m)) ×ˢ (range B),
              (∏ i ∈ range m, F i ((wordOf B m p.1).getD i 0)) * F m p.2 := by
        rw [← ih, Finset.sum_mul, Finset.sum_product]
        exact Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])
      rw [Finset.prod_range_succ, hR]
      have hpow : B ^ (m + 1) = B ^ m * B := by ring
      rw [hpow]
      refine Finset.sum_nbij' (i := fun k => (k / B, k % B)) (j := fun p => p.1 * B + p.2)
        ?_ ?_ ?_ ?_ ?_
      · intro k hk
        rw [Finset.mem_range] at hk
        exact Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)),
            Finset.mem_range.mpr (Nat.mod_lt _ hB)⟩
      · intro p hp
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
        rw [Finset.mem_range] at h1 h2 ⊢
        calc p.1 * B + p.2 < p.1 * B + B := by omega
          _ = (p.1 + 1) * B := by ring
          _ ≤ B ^ m * B := Nat.mul_le_mul_right B (by omega)
      · intro k _
        exact Nat.div_add_mod' k B
      · intro p hp
        obtain ⟨-, h2⟩ := Finset.mem_product.mp hp
        rw [Finset.mem_range] at h2
        have h3 : (p.1 * B + p.2) / B = p.1 := by
          rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt h2]
          omega
        have h4 : (p.1 * B + p.2) % B = p.2 := by
          rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt h2
        exact Prod.ext h3 h4
      · intro k hk
        rw [Finset.mem_range] at hk
        have hd : k % B < B := Nat.mod_lt _ hB
        have hk8 : k / B * B + k % B = k := Nat.div_add_mod' k B
        have hw : wordOf B (m + 1) k = wordOf B m (k / B) ++ [k % B] := by
          conv_lhs => rw [← hk8]
          exact wordOf_append B m (k / B) (k % B) hB hd
        have hlen : (wordOf B m (k / B)).length = m := length_wordOf _ _ _
        have hA : ∀ i ∈ range m, F i ((wordOf B m (k / B) ++ [k % B]).getD i 0)
            = F i ((wordOf B m (k / B)).getD i 0) := fun i hi => by
          rw [List.getD_append _ _ _ _ (by rw [hlen]; exact Finset.mem_range.mp hi)]
        have hlast : (wordOf B m (k / B) ++ [k % B]).getD m 0 = k % B := by
          rw [List.getD_append_right _ _ _ _ (by rw [hlen]), hlen, Nat.sub_self]
          simp
        rw [hw, Finset.prod_range_succ, Finset.prod_congr rfl hA, hlast]

/-- **Words factor.**  The word generating function is the product of the per-position digit
generating functions. -/
theorem wordGf_eq (B : ℕ) (hB : 0 < B) (f : ℕ → ℕ → ℕ) (m : ℕ) :
    wordGf B m f = ∏ i ∈ range m, (∑ d ∈ range B, (X : ℝ[X]) ^ f i d) := by
  have key := sum_prod_wordOf (R := ℝ[X]) B hB (fun i d => X ^ f i d) m
  rw [wordGf, ← key]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.prod_pow_eq_pow_sum]

/-! ## Windows factor over blocks -/

/-- The number of window positions that land in block `i`. -/
def segLen (q L r i : ℕ) : ℕ := ((range L).filter (fun t => (r + t) / q = i)).card

/-- The one-count contributed by block `i`, as a function of that block's digit alone. -/
def segOnes (g : ℕ → ℕ → ℕ) (q L r i d : ℕ) : ℕ :=
  ((range L).filter (fun t => (r + t) / q = i ∧ g ((r + t) % q) d = 1)).card

theorem sum_segLen (q L r S : ℕ) (hS : ∀ t < L, (r + t) / q < S) :
    ∑ i ∈ range S, segLen q L r i = L := by
  classical
  have := Finset.card_eq_sum_card_fiberwise (f := fun t => (r + t) / q)
    (s := range L) (t := range S)
    (fun t ht => Finset.mem_range.mpr (hS t (Finset.mem_range.mp ht)))
  simpa [segLen, eq_comm] using this.symm

theorem winOnes_eq_sum_segOnes (g : ℕ → ℕ → ℕ) (q L r S : ℕ) (v : List ℕ)
    (hS : ∀ t < L, (r + t) / q < S) :
    winOnes g q L r v = ∑ i ∈ range S, segOnes g q L r i (v.getD i 0) := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun t => (r + t) / q)
    (s := (range L).filter (fun t => g ((r + t) % q) (v.getD ((r + t) / q) 0) = 1))
    (t := range S)
    (fun t ht => Finset.mem_range.mpr (hS t (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)))
  rw [winOnes, hfib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, segOnes]
  constructor
  · rintro ⟨⟨ht, h1⟩, h2⟩
    exact ⟨ht, h2, by rwa [h2] at h1⟩
  · rintro ⟨ht, h2, h1⟩
    exact ⟨⟨ht, by rwa [h2]⟩, h2⟩

/-- The window generating function at residue `r`, over all base-`B` words of length `S`. -/
noncomputable def winGf (g : ℕ → ℕ → ℕ) (q B S L r : ℕ) : ℝ[X] :=
  ∑ k ∈ range (B ^ S), X ^ winOnes g q L r (wordOf B S k)

/-- **Windows factor.** -/
theorem winGf_eq_prod (g : ℕ → ℕ → ℕ) {B : ℕ} (hB : 0 < B) (q S L r : ℕ)
    (hS : ∀ t < L, (r + t) / q < S) :
    winGf g q B S L r = ∏ i ∈ range S, (∑ d ∈ range B, (X : ℝ[X]) ^ segOnes g q L r i d) := by
  have h : winGf g q B S L r = wordGf B S (fun i d => segOnes g q L r i d) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [winOnes_eq_sum_segOnes g q L r S _ hS]
  rw [h, wordGf_eq B hB]

/-- `blockFreq` is a coefficient of the window generating function. -/
theorem blockFreq_eq_coeff (g : ℕ → ℕ → ℕ) (q B S L j : ℕ) :
    blockFreq g q B S L j
      = (∑ r ∈ range q, (winGf g q B S L r).coeff j) / (q * B ^ S) := by
  classical
  simp only [blockFreq]
  congr 1
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [winGf, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.coeff_X_pow]
  by_cases h : winOnes g q L r (wordOf B S k) = j
  · simp [h]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-! ## The criterion: binomial segments give a binomial window -/

/-- **The block engine.**  If every trace the length-`L` window makes on a block has an exactly
Binomial one-count over the `B` digits, then the sequence is abelian at `L`. -/
theorem blockFreq_eq_binomial_of_seg (g : ℕ → ℕ → ℕ) {B q : ℕ} (hB : 0 < B) (hq : 0 < q)
    (S L : ℕ) (hS : ∀ r < q, ∀ t < L, (r + t) / q < S)
    (hseg : ∀ r < q, ∀ i < S, (∑ d ∈ range B, (X : ℝ[X]) ^ segOnes g q L r i d)
      = C ((B : ℝ) / 2 ^ segLen q L r i) * (1 + X) ^ segLen q L r i)
    (j : ℕ) : blockFreq g q B S L j = (L.choose j : ℝ) / 2 ^ L := by
  classical
  have hgf : ∀ r ∈ range q, winGf g q B S L r
      = C ((B : ℝ) ^ S / 2 ^ L) * (1 + X) ^ L := by
    intro r hr
    rw [winGf_eq_prod g hB q S L r (hS r (Finset.mem_range.mp hr)),
      Finset.prod_congr rfl (fun i hi => hseg r (Finset.mem_range.mp hr) i
        (Finset.mem_range.mp hi)),
      Finset.prod_mul_distrib, ← map_prod C, Finset.prod_pow_eq_pow_sum,
      sum_segLen q L r S (hS r (Finset.mem_range.mp hr))]
    congr 2
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
      sum_segLen q L r S (hS r (Finset.mem_range.mp hr))]
    simp
  have hcoeff : ∀ r ∈ range q, (winGf g q B S L r).coeff j
      = (B : ℝ) ^ S / 2 ^ L * (L.choose j : ℝ) := by
    intro r hr
    rw [hgf r hr, Polynomial.coeff_C_mul, add_comm (1 : ℝ[X]) X,
      Polynomial.coeff_X_add_one_pow]
  rw [blockFreq_eq_coeff, Finset.sum_congr rfl hcoeff, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have hB' : (B : ℝ) ^ S ≠ 0 := by positivity
  have hq' : (q : ℝ) ≠ 0 := by positivity
  field_simp

/-! ## Traces of a long window are prefixes and suffixes -/

/-- The set of in-block positions that the length-`L` window at residue `r` occupies in block
`b`. -/
def segSet (q L r b : ℕ) : Finset ℕ :=
  (range q).filter (fun u => r ≤ b * q + u ∧ b * q + u < r + L)

theorem segOnes_eq_card (g : ℕ → ℕ → ℕ) {q : ℕ} (hq : 0 < q) (L r b d : ℕ) :
    segOnes g q L r b d = ((segSet q L r b).filter (fun u => g u d = 1)).card := by
  refine Finset.card_nbij' (i := fun t => r + t - b * q) (j := fun u => b * q + u - r) ?_ ?_ ?_ ?_
  · intro t ht
    dsimp only
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨htL, hdiv, hg⟩ := ht
    have hdm : r + t = b * q + (r + t) % q := by
      conv_lhs => rw [← Nat.div_add_mod (r + t) q, hdiv, Nat.mul_comm]
    have hmlt : (r + t) % q < q := Nat.mod_lt _ hq
    have h1 : b * q ≤ r + t := by omega
    have h2 : r + t < b * q + q := by omega
    have hmod : (r + t) % q = r + t - b * q := by omega
    rw [Finset.mem_coe, Finset.mem_filter, segSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨by omega, by omega, by omega⟩, by rwa [hmod] at hg⟩
  · intro u hu
    dsimp only
    rw [Finset.mem_coe, Finset.mem_filter, segSet, Finset.mem_filter, Finset.mem_range] at hu
    obtain ⟨⟨huq, h1, h2⟩, hg⟩ := hu
    have he : r + (b * q + u - r) = b * q + u := by omega
    have hdiv : (r + (b * q + u - r)) / q = b := by
      rw [he, Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt huq]
      omega
    have hmod : (r + (b * q + u - r)) % q = u := by
      rw [he, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt huq]
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hdiv, by rw [hmod]; exact hg⟩
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨-, hdiv, -⟩ := ht
    have hdm : r + t = b * q + (r + t) % q := by
      conv_lhs => rw [← Nat.div_add_mod (r + t) q, hdiv, Nat.mul_comm]
    show b * q + (r + t - b * q) - r = t
    omega
  · intro u hu
    rw [Finset.mem_coe, Finset.mem_filter, segSet, Finset.mem_filter, Finset.mem_range] at hu
    show r + (b * q + u - r) - b * q = u
    omega

theorem segLen_eq_card (q L r b : ℕ) (hq : 0 < q) :
    segLen q L r b = (segSet q L r b).card := by
  have h := segOnes_eq_card (fun _ _ => 1) hq L r b 0
  simp only [segOnes, segLen] at h ⊢
  simpa using h

/-- A long window meets each block in a prefix or a suffix of the block. -/
theorem segSet_eq_Ico (q L r b : ℕ) (hq : 0 < q) (hr : r < q) (hL : q ≤ L) :
    (b = 0 ∧ segSet q L r b = Finset.Ico r q) ∨
      (segSet q L r b = Finset.Ico 0 (min q (r + L - b * q))) := by
  classical
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · refine Or.inl ⟨rfl, ?_⟩
    ext u
    simp only [segSet, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Nat.zero_mul,
      Nat.zero_add]
    omega
  · refine Or.inr ?_
    ext u
    simp only [segSet, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Nat.zero_le,
      true_and, lt_min_iff]
    have : q ≤ b * q := Nat.le_mul_of_pos_left q hb
    omega

/-- **Prefix/suffix binomiality.**  Every prefix and every suffix of a block has an exactly
Binomial one-count over the `B` digits. -/
def BinomSeg (g : ℕ → ℕ → ℕ) (q B : ℕ) : Prop :=
  ∀ a b : ℕ, b ≤ q → (a = 0 ∨ b = q) →
    (∑ d ∈ range B, (X : ℝ[X]) ^ (((Finset.Ico a b).filter (fun u => g u d = 1)).card))
      = C ((B : ℝ) / 2 ^ (b - a)) * (1 + X) ^ (b - a)

/-- **The long-window theorem.**  If every prefix and every suffix of the block law has an exactly
Binomial one-count, then the block-driven sequence is abelian at every window length `L ≥ q`. -/
theorem isAbelianAt_blockSeq_of_binomSeg (g : ℕ → ℕ → ℕ) (c : ℕ → ℕ) {B q : ℕ} (hB : 0 < B)
    (hq : 0 < q) (hcB : ∀ m, c m < B) (hc : IsNormalSequence B c) (hbin : BinomSeg g q B)
    (L : ℕ) (hL : q ≤ L) : IsAbelianAt (blockSeq g c q) L := by
  classical
  set S := q + L with hSdef
  have hSle : q + L ≤ q * S + 1 := by
    have : S ≤ q * S := Nat.le_mul_of_pos_left S hq
    omega
  have hfib : ∀ r < q, ∀ t < L, (r + t) / q < S := by
    intro r hr t ht
    have := Nat.div_le_self (r + t) q
    omega
  refine (isAbelianAt_blockSeq_iff g c hB hq hcB hc L S hSle).mpr (fun j _ => ?_)
  refine blockFreq_eq_binomial_of_seg g hB hq S L hfib (fun r hr b hb => ?_) j
  have hcard : ∀ d, segOnes g q L r b d
      = ((segSet q L r b).filter (fun u => g u d = 1)).card :=
    fun d => segOnes_eq_card g hq L r b d
  have hlen : segLen q L r b = (segSet q L r b).card := segLen_eq_card q L r b hq
  rcases segSet_eq_Ico q L r b hq hr hL with ⟨-, hset⟩ | hset
  · have hc2 : (Finset.Ico r q).card = q - r := by simp
    rw [hlen, hset, hc2]
    have := hbin r q (le_refl q) (Or.inr rfl)
    rw [← this]
    exact Finset.sum_congr rfl (fun d _ => by rw [hcard d, hset])
  · set t := min q (r + L - b * q) with ht
    have hc2 : (Finset.Ico 0 t).card = t - 0 := by simp
    rw [hlen, hset, hc2]
    have := hbin 0 t (min_le_left _ _) (Or.inl rfl)
    rw [← this]
    exact Finset.sum_congr rfl (fun d _ => by rw [hcard d, hset])

end NormalNumbers.Abelian
