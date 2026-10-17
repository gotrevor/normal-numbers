/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.StonehamSumsNormal

/-!
# Boundary witnesses for Stoneham combinations

This file formalizes the elementary integer-block witnesses at the boundary of the
Bailey--Borwein classification of rational Stoneham combinations.
-/

namespace NormalNumbers

open ReciprocalNormal
open Filter Topology

/-- Fermat followed by the elementary prime-power lift: the numerator of the
`j`-th block in the Bailey--Borwein L1 witness is divisible by `p^j`. -/
theorem prime_pow_dvd_stoneham_boundary_block (b p j : ℕ) (hp : p.Prime)
    (hpb : ¬ p ∣ b) :
    p ^ j ∣ b ^ ((p - 1) * p ^ j) - 1 := by
  have hcop : b.Coprime p := ((hp.coprime_iff_not_dvd).2 hpb).symm
  have hfermat := Nat.ModEq.pow_card_sub_one_eq_one hp hcop
  have hb0 : b ≠ 0 := by
    intro hb
    subst b
    simp at hpb
  have hbase : 1 ≤ b ^ (p - 1) := Nat.one_le_pow _ _ (Nat.one_le_iff_ne_zero.2 hb0)
  have hdvd : p ∣ b ^ (p - 1) - 1 := hfermat.symm.dvd'
  obtain ⟨a, ha⟩ := hdvd
  have hshape : b ^ (p - 1) = 1 + p * a := by omega
  have hlift := pow_pow_modEq_one p j a
  rw [← hshape] at hlift
  rw [← pow_mul] at hlift
  exact hlift.symm.dvd'

/-- The positive paired summand in the L1 boundary witness.  It combines the
`(2k+1)`-st and `(2k+2)`-nd `p`-terms with the `k`-th `p²`-term. -/
noncomputable def stonehamBoundaryTerm (b p k : ℕ) : ℝ :=
  1 / ((p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 1))) -
    1 / ((p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 2)))

/-- The natural-number coefficient of a paired L1 block. -/
def stonehamBoundaryBlock (b p k : ℕ) : ℕ :=
  (b ^ ((p - 1) * p ^ (2 * k + 1)) - 1) / p ^ (2 * k + 1)

/-- The first (and larger) summand of `stonehamBoundaryTerm`.  It is the
positive majorant used to control the tail between consecutive blocks. -/
noncomputable def stonehamBoundaryMajorant (b p k : ℕ) : ℝ :=
  1 / ((p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 1)))

/-- The paired summand is an integer block whose right endpoint is
`p^(2k+2)`. -/
theorem stonehamBoundaryTerm_scaled_eq_block (b p k : ℕ) (hb : 2 ≤ b)
    (hp : p.Prime) (hpb : ¬ p ∣ b) :
    (b : ℝ) ^ (p ^ (2 * k + 2)) * stonehamBoundaryTerm b p k =
      stonehamBoundaryBlock b p k := by
  have hdvd := prime_pow_dvd_stoneham_boundary_block b p (2 * k + 1) hp hpb
  set q : ℕ := stonehamBoundaryBlock b p k with hq
  have hqN : p ^ (2 * k + 1) * q =
      b ^ ((p - 1) * p ^ (2 * k + 1)) - 1 := by
    rw [hq, stonehamBoundaryBlock]
    exact Nat.mul_div_cancel' hdvd
  have hone : 1 ≤ b ^ ((p - 1) * p ^ (2 * k + 1)) :=
    Nat.one_le_pow _ _ (by omega)
  have hqR : (p : ℝ) ^ (2 * k + 1) * q =
      b ^ ((p - 1) * p ^ (2 * k + 1)) - 1 := by
    norm_cast
  have hdiff : p ^ (2 * k + 2) =
      (p - 1) * p ^ (2 * k + 1) + p ^ (2 * k + 1) := by
    calc
      p ^ (2 * k + 2) = p ^ (2 * k + 1) * p := by
        simpa only [show 2 * k + 2 = 2 * k + 1 + 1 by omega] using
          pow_succ p (2 * k + 1)
      _ = ((p - 1) + 1) * p ^ (2 * k + 1) := by
        rw [Nat.sub_add_cancel hp.one_le, mul_comm]
      _ = (p - 1) * p ^ (2 * k + 1) + p ^ (2 * k + 1) := by ring
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hqdiv : ((b : ℝ) ^ ((p - 1) * p ^ (2 * k + 1)) - 1) /
      (p : ℝ) ^ (2 * k + 1) = q := by
    rw [div_eq_iff (pow_ne_zero _ hpR.ne')]
    linarith [hqR]
  rw [stonehamBoundaryTerm]
  rw [hdiff, pow_add]
  rw [← hqdiv]
  field_simp

/-- Once scaled beyond its right endpoint, a paired summand is an integer
base-`b` block followed by zeros. -/
theorem stonehamBoundaryTerm_scaled_eq_shifted_block (b p k q : ℕ) (hb : 2 ≤ b)
    (hp : p.Prime) (hpb : ¬ p ∣ b) (hq : p ^ (2 * k + 2) ≤ q) :
    (b : ℝ) ^ q * stonehamBoundaryTerm b p k =
      (b ^ (q - p ^ (2 * k + 2)) * stonehamBoundaryBlock b p k : ℕ) := by
  have hpow : (b : ℝ) ^ (q - p ^ (2 * k + 2)) * b ^ (p ^ (2 * k + 2)) =
      b ^ q := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (b : ℝ) ^ q * stonehamBoundaryTerm b p k =
        (b ^ (q - p ^ (2 * k + 2)) * b ^ (p ^ (2 * k + 2))) *
          stonehamBoundaryTerm b p k := by rw [hpow]
    _ = b ^ (q - p ^ (2 * k + 2)) *
          (b ^ (p ^ (2 * k + 2)) * stonehamBoundaryTerm b p k) := by ring
    _ = b ^ (q - p ^ (2 * k + 2)) * stonehamBoundaryBlock b p k := by
      rw [stonehamBoundaryTerm_scaled_eq_block b p k hb hp hpb]
    _ = (b ^ (q - p ^ (2 * k + 2)) * stonehamBoundaryBlock b p k : ℕ) := by
      push_cast
      rfl

/-- Every boundary term is nonnegative. -/
theorem stonehamBoundaryTerm_nonneg (b p k : ℕ) (hb : 2 ≤ b) (hp : p.Prime) :
    0 ≤ stonehamBoundaryTerm b p k := by
  unfold stonehamBoundaryTerm
  apply sub_nonneg.mpr
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hexp : p ^ (2 * k + 1) ≤ p ^ (2 * k + 2) :=
    Nat.pow_le_pow_right hp.pos (by omega)
  have hbpow : (b : ℝ) ^ (p ^ (2 * k + 1)) ≤ b ^ (p ^ (2 * k + 2)) :=
    pow_le_pow_right₀ hbR hexp
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_left hbpow (pow_nonneg hpR.le _)

/-- The first summand majorizes the positive boundary term. -/
theorem stonehamBoundaryTerm_le_majorant (b p k : ℕ) :
    stonehamBoundaryTerm b p k ≤ stonehamBoundaryMajorant b p k := by
  unfold stonehamBoundaryTerm stonehamBoundaryMajorant
  have hnonneg : 0 ≤
      1 / ((p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 2))) := by positivity
  linarith

/-- Later majorants decrease at least geometrically, uniformly in the prime
and the base. -/
theorem stonehamBoundaryMajorant_shift_le (b p k j : ℕ) (hb : 2 ≤ b)
    (hp : p.Prime) :
    stonehamBoundaryMajorant b p (j + k) ≤
      stonehamBoundaryMajorant b p k * (1 / 2 : ℝ) ^ j := by
  have hjp : j + 1 ≤ p ^ (2 * j) := by
    calc
      j + 1 ≤ p ^ j := Nat.lt_pow_self hp.two_le
      _ ≤ p ^ (2 * j) := Nat.pow_le_pow_right hp.pos (by omega)
  have hexp : p ^ (2 * k + 1) + j ≤ p ^ (2 * (j + k) + 1) := by
    have hP : 1 ≤ p ^ (2 * k + 1) := Nat.one_le_pow _ _ hp.one_le
    calc
      p ^ (2 * k + 1) + j ≤ p ^ (2 * k + 1) * (j + 1) := by nlinarith
      _ ≤ p ^ (2 * k + 1) * p ^ (2 * j) := Nat.mul_le_mul_left _ hjp
      _ = p ^ (2 * (j + k) + 1) := by rw [← pow_add]; congr 1 <;> omega
  have hpcoeff : (p : ℝ) ^ (2 * k + 1) ≤ p ^ (2 * (j + k) + 1) := by
    exact_mod_cast Nat.pow_le_pow_right hp.pos (by omega)
  have hbbase : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpow : (b : ℝ) ^ (p ^ (2 * k + 1)) * 2 ^ j ≤
      b ^ (p ^ (2 * (j + k) + 1)) := by
    calc
      (b : ℝ) ^ (p ^ (2 * k + 1)) * 2 ^ j ≤
          b ^ (p ^ (2 * k + 1)) * b ^ j := by gcongr
      _ = b ^ (p ^ (2 * k + 1) + j) := (pow_add _ _ _).symm
      _ ≤ b ^ (p ^ (2 * (j + k) + 1)) :=
        pow_le_pow_right₀ (by linarith) hexp
  have hden : (p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 1)) * 2 ^ j ≤
      p ^ (2 * (j + k) + 1) * b ^ (p ^ (2 * (j + k) + 1)) := by
    calc
      (p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 1)) * 2 ^ j =
          p ^ (2 * k + 1) * (b ^ (p ^ (2 * k + 1)) * 2 ^ j) := by ring
      _ ≤ p ^ (2 * (j + k) + 1) * b ^ (p ^ (2 * (j + k) + 1)) :=
        mul_le_mul hpcoeff hbpow (by positivity) (by positivity)
  unfold stonehamBoundaryMajorant
  rw [div_pow, one_pow, div_mul_div_comm, one_mul]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  exact div_le_div_of_nonneg_left one_pos.le (by positivity) hden

/-- At any positive block index, twice a majorized tail scaled no farther
than its left endpoint is still below one. -/
theorem stonehamBoundaryMajorant_scaled_lt_half (b p k q : ℕ) (hb : 2 ≤ b)
    (hp : p.Prime) (hk : 1 ≤ k) (hq : q ≤ p ^ (2 * k + 1)) :
    2 * ((b : ℝ) ^ q * stonehamBoundaryMajorant b p k) < 1 := by
  have hbpow : (b : ℝ) ^ q ≤ b ^ (p ^ (2 * k + 1)) :=
    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ b by omega)) hq
  have hscaled : (b : ℝ) ^ q * stonehamBoundaryMajorant b p k ≤
      1 / (p : ℝ) ^ (2 * k + 1) := by
    calc
      (b : ℝ) ^ q * stonehamBoundaryMajorant b p k ≤
          b ^ (p ^ (2 * k + 1)) * stonehamBoundaryMajorant b p k :=
        mul_le_mul_of_nonneg_right hbpow (by unfold stonehamBoundaryMajorant; positivity)
      _ = 1 / (p : ℝ) ^ (2 * k + 1) := by
        unfold stonehamBoundaryMajorant
        field_simp
  have hp8 : 8 ≤ p ^ (2 * k + 1) := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp.two_le 3
      _ ≤ p ^ (2 * k + 1) := Nat.pow_le_pow_right hp.pos (by omega)
  have hp8R : (8 : ℝ) ≤ (p : ℝ) ^ (2 * k + 1) := by exact_mod_cast hp8
  have hrecip : 2 * (1 / (p : ℝ) ^ (2 * k + 1)) ≤ 1 / 4 := by
    apply (mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (by norm_num) hp8R) (by norm_num)).trans_eq
    norm_num
  nlinarith

/-- The block summand is exactly the termwise pairing of the two Stoneham
series in `α_{b,p} - (p+1)α_{b,p²}`. -/
theorem stonehamBoundaryTerm_eq_pair (b p k : ℕ) (hb : 2 ≤ b) (hp : p.Prime) :
    stonehamBoundaryTerm b p k =
      1 / ((p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 1))) +
        1 / ((p : ℝ) ^ (2 * k + 2) * b ^ (p ^ (2 * k + 2))) -
          (p + 1) *
            (1 / (((p ^ 2 : ℕ) : ℝ) ^ (k + 1) *
              b ^ ((p ^ 2) ^ (k + 1)))) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hp_pow : (p ^ 2) ^ (k + 1) = p ^ (2 * k + 2) := by
    rw [← pow_mul]
    congr 1
  have hp_powR : (((p ^ 2 : ℕ) : ℝ) ^ (k + 1)) =
      (p : ℝ) ^ (2 * k + 2) := by exact_mod_cast hp_pow
  rw [stonehamBoundaryTerm, hp_pow, hp_powR]
  field_simp
  ring

/-- The positive block series is summable. -/
theorem summable_stonehamBoundaryTerm (b p : ℕ) (hb : 2 ≤ b) (hp : p.Prime) :
    Summable (stonehamBoundaryTerm b p) := by
  let f : ℕ → ℝ := fun j =>
    1 / ((p : ℝ) ^ (j + 1) * b ^ (p ^ (j + 1)))
  let g : ℕ → ℝ := fun k =>
    1 / (((p ^ 2 : ℕ) : ℝ) ^ (k + 1) * b ^ ((p ^ 2) ^ (k + 1)))
  have hf : Summable f := by
    simpa only [f] using StonehamSumsNormal.summable_stonehamAlpha_term b p
      (by omega) hp.two_le
  have hg : Summable g := by
    simpa only [g] using StonehamSumsNormal.summable_stonehamAlpha_term b (p ^ 2) (by omega)
      (by nlinarith [hp.two_le])
  have he : Summable (fun k => f (2 * k)) := hf.comp_injective (by
    intro a c h
    omega)
  have ho : Summable (fun k => f (2 * k + 1)) := hf.comp_injective (by
    intro a c h
    change 2 * a + 1 = 2 * c + 1 at h
    omega)
  have hpair : Summable (fun k => f (2 * k) + f (2 * k + 1) - (p + 1) * g k) :=
    (he.add ho).sub (hg.mul_left _)
  refine hpair.congr fun k => ?_
  symm
  simpa only [f, g, show 2 * k + 1 + 1 = 2 * k + 2 by omega,
    show 2 * k + 0 + 1 = 2 * k + 1 by omega] using
      stonehamBoundaryTerm_eq_pair b p k hb hp

/-- The L1 combination is the sum of its positive integer blocks. -/
theorem stoneham_sub_succ_mul_eq_tsum_boundary (b p : ℕ) (hb : 2 ≤ b)
    (hp : p.Prime) :
    stonehamAlpha b p - (p + 1) * stonehamAlpha b (p ^ 2) =
      ∑' k, stonehamBoundaryTerm b p k := by
  let f : ℕ → ℝ := fun j =>
    1 / ((p : ℝ) ^ (j + 1) * b ^ (p ^ (j + 1)))
  let g : ℕ → ℝ := fun k =>
    1 / (((p ^ 2 : ℕ) : ℝ) ^ (k + 1) * b ^ ((p ^ 2) ^ (k + 1)))
  have hf : Summable f := by
    simpa only [f] using StonehamSumsNormal.summable_stonehamAlpha_term b p
      (by omega) hp.two_le
  have hg : Summable g := by
    simpa only [g] using StonehamSumsNormal.summable_stonehamAlpha_term b (p ^ 2) (by omega)
      (by nlinarith [hp.two_le])
  have he : Summable (fun k => f (2 * k)) := hf.comp_injective (by
    intro a c h
    omega)
  have ho : Summable (fun k => f (2 * k + 1)) := hf.comp_injective (by
    intro a c h
    change 2 * a + 1 = 2 * c + 1 at h
    omega)
  have hsplit : (∑' k, f (2 * k)) + ∑' k, f (2 * k + 1) = ∑' j, f j :=
    tsum_even_add_odd he ho
  have hpair : ∑' k, stonehamBoundaryTerm b p k =
      (∑' k, f (2 * k)) + (∑' k, f (2 * k + 1)) - (p + 1) * ∑' k, g k := by
    calc
      ∑' k, stonehamBoundaryTerm b p k =
          ∑' k, (f (2 * k) + f (2 * k + 1) - (p + 1) * g k) := by
            apply tsum_congr
            intro k
            simpa only [f, g, show 2 * k + 1 + 1 = 2 * k + 2 by omega,
              show 2 * k + 0 + 1 = 2 * k + 1 by omega] using
                stonehamBoundaryTerm_eq_pair b p k hb hp
      _ = (∑' k, (f (2 * k) + f (2 * k + 1))) - ∑' k, (p + 1) * g k :=
        (he.add ho).tsum_sub (hg.mul_left _)
      _ = (∑' k, f (2 * k)) + (∑' k, f (2 * k + 1)) -
          (p + 1) * ∑' k, g k := by rw [he.tsum_add ho, hg.tsum_mul_left]
  have hf_eq : (∑' j, f j) = stonehamAlpha b p := rfl
  have hg_eq : (∑' k, g k) = stonehamAlpha b (p ^ 2) := rfl
  rw [← hf_eq, ← hg_eq, ← hsplit, ← hpair]

/-- A uniform geometric majorant for all boundary blocks. -/
theorem stonehamBoundaryMajorant_le_geom (b p j : ℕ) (hb : 2 ≤ b) (hp : p.Prime) :
    stonehamBoundaryMajorant b p j ≤ (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ j := by
  have hbp : 4 ≤ b ^ p := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ b ^ 2 := Nat.pow_le_pow_left hb 2
      _ ≤ b ^ p := Nat.pow_le_pow_right (by omega) hp.two_le
  have hdenN : 8 ≤ p * b ^ p := by nlinarith [hp.two_le]
  have hdenR : (8 : ℝ) ≤ (p : ℝ) * b ^ p := by exact_mod_cast hdenN
  have hzero : stonehamBoundaryMajorant b p 0 ≤ (1 / 8 : ℝ) := by
    rw [stonehamBoundaryMajorant]
    simp only [mul_zero, zero_add, pow_one]
    exact one_div_le_one_div_of_le (by norm_num) hdenR
  have hshift := stonehamBoundaryMajorant_shift_le b p 0 j hb hp
  simpa only [Nat.add_zero] using
    hshift.trans (mul_le_mul_of_nonneg_right hzero (by positivity))

/-- The L1 boundary combination itself lies in `[0,1)`, so its standard
base-`b` digits can be read without an integer-part correction. -/
theorem stoneham_sub_succ_mul_mem_Ico (b p : ℕ) (hb : 2 ≤ b) (hp : p.Prime) :
    stonehamAlpha b p - (p + 1) * stonehamAlpha b (p ^ 2) ∈ Set.Ico (0 : ℝ) 1 := by
  rw [stoneham_sub_succ_mul_eq_tsum_boundary b p hb hp]
  constructor
  · exact tsum_nonneg fun k => stonehamBoundaryTerm_nonneg b p k hb hp
  · have hgeom : Summable fun k : ℕ => (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ k :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle : ∀ k, stonehamBoundaryTerm b p k ≤
        (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ k := fun k =>
      (stonehamBoundaryTerm_le_majorant b p k).trans
        (stonehamBoundaryMajorant_le_geom b p k hb hp)
    have hsum := (summable_stonehamBoundaryTerm b p hb hp).tsum_le_tsum hle hgeom
    rw [tsum_mul_left, tsum_geometric_two] at hsum
    linarith

/-- Between the end of one L1 integer block and the beginning of the next,
all base-`b` digits vanish.  The indices are 0-based. -/
theorem digitOf_stoneham_sub_succ_mul_eq_zero (b p k i : ℕ) (hb : 2 ≤ b)
    (hp : p.Prime) (hpb : ¬ p ∣ b) (h₁ : p ^ (2 * k + 2) ≤ i)
    (h₂ : i < p ^ (2 * k + 3)) :
    digitOf b (Int.fract (stonehamAlpha b p - (p + 1) * stonehamAlpha b (p ^ 2))) i = 0 := by
  set x : ℝ := stonehamAlpha b p - (p + 1) * stonehamAlpha b (p ^ 2) with hx
  set q : ℕ := i + 1 with hq
  have hq_le : q ≤ p ^ (2 * k + 3) := by omega
  have hxfrac : Int.fract x = x :=
    Int.fract_eq_self.mpr (stoneham_sub_succ_mul_mem_Ico b p hb hp)
  set g : ℕ → ℝ := fun j => (b : ℝ) ^ q * stonehamBoundaryTerm b p j with hg
  have hgsum : Summable g := (summable_stonehamBoundaryTerm b p hb hp).mul_left _
  have hmul : x * (b : ℝ) ^ q = ∑' j, g j := by
    rw [hx, stoneham_sub_succ_mul_eq_tsum_boundary b p hb hp, tsum_mul_left, mul_comm]
  have hshift : Summable fun j => g (j + (k + 1)) :=
    (summable_nat_add_iff (k + 1)).2 hgsum
  have hsplit : ∑' j, g j =
      (∑ j ∈ Finset.range (k + 1), g j) + ∑' j, g (j + (k + 1)) :=
    (hgsum.sum_add_tsum_nat_add (k + 1)).symm
  set T : ℝ := ∑' j, g (j + (k + 1)) with hT
  set A : ℕ := ∑ j ∈ Finset.range (k + 1),
    b ^ (q - p ^ (2 * j + 2)) * stonehamBoundaryBlock b p j with hA
  have hHead : (∑ j ∈ Finset.range (k + 1), g j) = (A : ℝ) := by
    rw [hA]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    have hjk : j ≤ k := by omega
    have hjpow : p ^ (2 * j + 2) ≤ p ^ (2 * k + 2) :=
      Nat.pow_le_pow_right hp.pos (by omega)
    rw [hg]
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      stonehamBoundaryTerm_scaled_eq_shifted_block b p j q hb hp hpb
        (hjpow.trans (h₁.trans (by omega)))
  have hAb : b ∣ A := by
    rw [hA]
    refine Finset.dvd_sum fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    have hjk : j ≤ k := by omega
    have hjpow : p ^ (2 * j + 2) ≤ p ^ (2 * k + 2) :=
      Nat.pow_le_pow_right hp.pos (by omega)
    have hexp : 0 < q - p ^ (2 * j + 2) := by omega
    exact Dvd.dvd.mul_right (dvd_pow_self b hexp.ne') _
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact tsum_nonneg fun j => by
      rw [hg]
      exact mul_nonneg (pow_nonneg (by positivity) _)
        (stonehamBoundaryTerm_nonneg b p _ hb hp)
  have hTlt : T < 1 := by
    have hterm : ∀ j, g (j + (k + 1)) ≤
        ((b : ℝ) ^ q * stonehamBoundaryMajorant b p (k + 1)) *
          (1 / 2 : ℝ) ^ j := by
      intro j
      rw [hg]
      calc
        (b : ℝ) ^ q * stonehamBoundaryTerm b p (j + (k + 1)) ≤
            b ^ q * stonehamBoundaryMajorant b p (j + (k + 1)) :=
          mul_le_mul_of_nonneg_left (stonehamBoundaryTerm_le_majorant b p _) (by positivity)
        _ ≤ b ^ q *
            (stonehamBoundaryMajorant b p (k + 1) * (1 / 2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left
            (stonehamBoundaryMajorant_shift_le b p (k + 1) j hb hp) (by positivity)
        _ = (b ^ q * stonehamBoundaryMajorant b p (k + 1)) *
            (1 / 2 : ℝ) ^ j := by ring
    have hgeom : Summable fun j : ℕ =>
        ((b : ℝ) ^ q * stonehamBoundaryMajorant b p (k + 1)) *
          (1 / 2 : ℝ) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle := hshift.tsum_le_tsum hterm hgeom
    rw [hT]
    refine lt_of_le_of_lt hle ?_
    rw [tsum_mul_left, tsum_geometric_two]
    simpa [mul_comm] using
      stonehamBoundaryMajorant_scaled_lt_half b p (k + 1) q hb hp (by omega) (by
        simpa only [show 2 * (k + 1) + 1 = 2 * k + 3 by omega] using hq_le)
  have hval : x * (b : ℝ) ^ q = (A : ℝ) + T := by
    rw [hmul, hsplit, hHead]
  have hfl : ⌊x * (b : ℝ) ^ q⌋ = (A : ℤ) := by
    rw [hval, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  unfold digitOf
  rw [hxfrac, ← hq, hfl, Int.toNat_natCast, Nat.mod_eq_zero_of_dvd hAb]

/-- **Bailey--Borwein boundary witness L1.**  For every prime `p` coprime to
the base, the same-class combination `α_{b,p} - (p+1)α_{b,p²}` has arbitrarily
long zero windows and is therefore not even simply normal. -/
@[blueprint (title := "Same-class Stoneham combinations need not be simply normal")]
theorem not_isSimplyNormal_stoneham_sub_succ_mul (b p : ℕ) (hb : 2 ≤ b) (hp : p.Prime)
    (hpb : ¬ p ∣ b) :
    ¬ IsSimplyNormal b (stonehamAlpha b p - (p + 1) * stonehamAlpha b (p ^ 2)) := by
  classical
  intro hnormal
  let x := stonehamAlpha b p - (p + 1) * stonehamAlpha b (p ^ 2)
  let s : ℕ → ℕ := digitOf b (Int.fract x)
  let Z : ℕ → ℕ := fun n => ((Finset.range n).filter fun i => s i = 0).card
  have hcount (n : ℕ) : countOccurrences [0] ((List.range n).map s) = Z n :=
    Failures.countOccurrences_zero_eq_card s n
  have hlim : Tendsto (fun n => (Z n : ℝ) / n) atTop (nhds (1 / b : ℝ)) := by
    simpa [x, s, hcount, Z] using hnormal 0 (by omega)
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨K, hK⟩ := hlim (1 / (4 * (b : ℝ))) (by positivity)
  let k := max K 1
  let n₁ := p ^ (2 * k + 2)
  let n₂ := p ^ (2 * k + 3)
  have hkK : K ≤ k := le_max_left _ _
  have hkpow : k ≤ p ^ k := (Nat.lt_pow_self hp.two_le).le
  have hn₁K : K ≤ n₁ := by
    dsimp [n₁]
    exact hkK.trans (hkpow.trans (Nat.pow_le_pow_right hp.pos (by omega)))
  have hn₂K : K ≤ n₂ := by
    dsimp [n₂]
    exact hkK.trans (hkpow.trans (Nat.pow_le_pow_right hp.pos (by omega)))
  have hn₁₂ : n₁ ≤ n₂ := by
    dsimp [n₁, n₂]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hforced : ∀ i, i ∈ Finset.Ico n₁ n₂ → s i = 0 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact digitOf_stoneham_sub_succ_mul_eq_zero b p k i hb hp hpb hi.1 hi.2
  have hstep : Z n₁ + (n₂ - n₁) ≤ Z n₂ := by
    have hdisj : Disjoint ((Finset.range n₁).filter fun i => s i = 0)
        (Finset.Ico n₁ n₂) := by
      rw [Finset.disjoint_left]
      intro a ha hab
      rw [Finset.mem_filter, Finset.mem_range] at ha
      rw [Finset.mem_Ico] at hab
      omega
    have hsub : ((Finset.range n₁).filter fun i => s i = 0) ∪ Finset.Ico n₁ n₂
        ⊆ (Finset.range n₂).filter fun i => s i = 0 := by
      intro a ha
      rw [Finset.mem_union] at ha
      rw [Finset.mem_filter, Finset.mem_range]
      rcases ha with ha | ha
      · rw [Finset.mem_filter, Finset.mem_range] at ha
        exact ⟨ha.1.trans_le hn₁₂, ha.2⟩
      · rw [Finset.mem_Ico] at ha
        exact ⟨ha.2, hforced a (Finset.mem_Ico.mpr ha)⟩
    have hc := Finset.card_le_card hsub
    simpa [Z, Finset.card_union_of_disjoint hdisj, Nat.card_Ico] using hc
  have h₁ := hK n₁ hn₁K
  have h₂ := hK n₂ hn₂K
  rw [Real.dist_eq, abs_lt] at h₁ h₂
  have hn₁pos : (0 : ℝ) < n₁ := by
    exact_mod_cast (pow_pos hp.pos (2 * k + 2))
  have hn₂pos : (0 : ℝ) < n₂ := by
    exact_mod_cast (pow_pos hp.pos (2 * k + 3))
  have heps : (1 / (b : ℝ) - 1 / (4 * b)) = 3 / (4 * b) := by
    have hb0 : (b : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have heps' : (1 / (b : ℝ) + 1 / (4 * b)) = 5 / (4 * b) := by
    have hb0 : (b : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have e₁ : (3 / (4 * (b : ℝ))) * (n₁ : ℝ) < Z n₁ := by
    have hx : (1 / (b : ℝ) - 1 / (4 * b)) < (Z n₁ : ℝ) / n₁ := by
      linarith [h₁.1]
    rw [heps, lt_div_iff₀ hn₁pos] at hx
    exact hx
  have e₂ : (Z n₂ : ℝ) < (5 / (4 * (b : ℝ))) * n₂ := by
    have hx : (Z n₂ : ℝ) / n₂ <
        (1 / (b : ℝ) + 1 / (4 * b)) := by linarith [h₂.2]
    rw [heps', div_lt_iff₀ hn₂pos] at hx
    exact hx
  have e₃ : (Z n₁ : ℝ) + ((n₂ : ℝ) - n₁) ≤ Z n₂ := by
    have hc := (Nat.cast_le (α := ℝ)).2 hstep
    push_cast [Nat.cast_sub hn₁₂] at hc
    linarith
  have hn₂eq : (n₂ : ℝ) = (p : ℝ) * n₁ := by
    dsimp [n₁, n₂]
    rw [show 2 * k + 3 = (2 * k + 2) + 1 by omega, pow_succ]
    push_cast
    ring
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hb4pos : (0 : ℝ) < 4 * b := by positivity
  have e₁' : 3 * (n₁ : ℝ) < 4 * b * Z n₁ := by
    have := mul_lt_mul_of_pos_left e₁ hb4pos
    field_simp at this
    nlinarith
  have e₂' : 4 * b * Z n₂ < 5 * (n₂ : ℝ) := by
    have := mul_lt_mul_of_pos_left e₂ hb4pos
    field_simp at this
    nlinarith
  have e₃' : 4 * b * ((Z n₁ : ℝ) + ((n₂ : ℝ) - n₁)) ≤
      4 * b * Z n₂ := mul_le_mul_of_nonneg_left e₃ hb4pos.le
  have hmul : 2 * (p - 1) ≤ b * (p - 1) := Nat.mul_le_mul_right (p - 1) hb
  have hmul4 : 8 * (p - 1) ≤ 4 * b * (p - 1) := by
    calc
      8 * (p - 1) = 4 * (2 * (p - 1)) := by ring
      _ ≤ 4 * (b * (p - 1)) := Nat.mul_le_mul_left 4 hmul
      _ = 4 * b * (p - 1) := by ring
  have hp2 : 2 ≤ p := hp.two_le
  have hcoefN : 5 * p < 3 + 4 * b * (p - 1) := by omega
  have hcoefCast : ((5 * p : ℕ) : ℝ) < ((3 + 4 * b * (p - 1) : ℕ) : ℝ) := by
    exact_mod_cast hcoefN
  have hcoef : (5 : ℝ) * p < 3 + 4 * b * (p - 1) := by
    push_cast [Nat.cast_sub hp.one_le] at hcoefCast
    exact hcoefCast
  rw [hn₂eq] at e₂' e₃'
  have hn₁nonneg : (0 : ℝ) ≤ n₁ := hn₁pos.le
  nlinarith [mul_pos (sub_pos.mpr hcoef) hn₁pos]

end NormalNumbers
