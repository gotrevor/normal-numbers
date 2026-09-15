/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyFullSeqW

/-!
# The prefix cut is an **atom-dependent** scale cut — and its two honest flanks

`tendsto_fullWRead_freq` controls the wide read at the band cutoffs `fTW (i+1)`.
`IsNormalSequence 2` needs *every* read index, and the read consumes band `i`'s distinct window
starts **in increasing order**, so a read index cuts the band at a **position** threshold `c`:
the consumed starts are `(winStartsW i).filter (· ≤ c)`.

A start is `2·kIdx (gridAt i) n α`, and `d_α·kIdx(n,α) ≤ n < d_α·(kIdx(n,α)+1)`, so

> `2·kIdx(n,α) ≤ c`  is  `n ≲ c·d_α/2` — **a cutoff that depends on the atom**.

That is *not* a truncated sample, which is why `abs_posAvg_bandWLaw_le` does not apply verbatim
to a mid-band prefix.  But the grid's multipliers agree to within `1 + 1/K`
(`gridOf.mul_d_le_mul_d`: `K·d_α ≤ (K+1)·d_β`), so the consumed set is **bracketed between two
plain truncations**:

  `cutLo i c := K·d_ref·c / (2(K+1))`      every sample time below it is consumed at *every* atom
  `cutHi i c := (K+1)·d_ref·(c+4) / (2K) + 1`   every sample time consumed at *some* atom is below it

with `cutHi / cutLo ≤ (1 + 1/K)²·(1 + 4/c) + o(1)`.  Both flanks are honest outer scales, both
certified by `H₂_bandWLaw_ge` / `abs_posAvg_bandWLaw_le` when they lie in `[Xlo (KK i), wTop i]`,
and the sandwich costs a **relative `O(1/K)`** — negligible against the capture error
`2√(808 log 2·ℓ/√K) = O(K^{−1/4})` the band law already carries.

This module proves the two inclusions and the flank cardinality ratio.  Nothing here mentions
the read; the read side is `G4EntropyWPrefix`.
-/

open Finset

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The reference multiplier -/

/-- A reference atom of level `i`'s grid. -/
noncomputable def refAtom (i : ℕ) : (gridAt i).Atom := Classical.arbitrary _

/-- The reference multiplier `d_ref` of level `i`.  Every multiplier of the level agrees with it
to within `1 + 1/K` (`KK_mul_dRef_le`, `KK_mul_d_le`). -/
noncomputable def dRef (i : ℕ) : ℕ := (gridAt i).d (refAtom i)

lemma dRef_pos (i : ℕ) : 0 < dRef i := (gridAt i).d_pos _

lemma KK_pos (i : ℕ) : 0 < KK i := KK_one_le i

/-- `K·d_ref ≤ (K+1)·d_α`: no multiplier is more than `1 + 1/K` below the reference. -/
lemma KK_mul_dRef_le (i : ℕ) (α : (gridAt i).Atom) :
    KK i * dRef i ≤ (KK i + 1) * (gridAt i).d α :=
  gridOf.mul_d_le_mul_d (K := KK i) (N := N (KK i)) (KK_one_le i) (refAtom i) α

/-- `K·d_α ≤ (K+1)·d_ref`: no multiplier is more than `1 + 1/K` above the reference. -/
lemma KK_mul_d_le (i : ℕ) (α : (gridAt i).Atom) :
    KK i * (gridAt i).d α ≤ (KK i + 1) * dRef i :=
  gridOf.mul_d_le_mul_d (K := KK i) (N := N (KK i)) (KK_one_le i) α (refAtom i)

/-! ### The two flanks -/

/-- **The lower flank** of the position cutoff `c`: every sample time below it has *all* of its
windows (at every atom) consumed by the cutoff. -/
noncomputable def cutLo (i c : ℕ) : ℕ := KK i * dRef i * c / (2 * (KK i + 1))

/-- **The upper flank** of the position cutoff `c`: every sample time with *some* window consumed
by the cutoff lies below it. -/
noncomputable def cutHi (i c : ℕ) : ℕ := (KK i + 1) * dRef i * (c + 4) / (2 * KK i) + 1

lemma cutLo_eq (i c : ℕ) : cutLo i c = KK i * dRef i * c / (2 * (KK i + 1)) := rfl
lemma cutHi_eq (i c : ℕ) : cutHi i c = (KK i + 1) * dRef i * (c + 4) / (2 * KK i) + 1 := rfl

/-- The defining inequality of the lower flank. -/
lemma two_mul_succ_mul_cutLo_le (i c : ℕ) :
    2 * (KK i + 1) * cutLo i c ≤ KK i * dRef i * c := by
  have h := Nat.div_add_mod (KK i * dRef i * c) (2 * (KK i + 1))
  have hlt : KK i * dRef i * c % (2 * (KK i + 1)) < 2 * (KK i + 1) :=
    Nat.mod_lt _ (by have := KK_pos i; omega)
  rw [cutLo_eq]
  omega

/-- The defining inequality of the upper flank. -/
lemma lt_two_mul_KK_mul_cutHi (i c : ℕ) :
    (KK i + 1) * dRef i * (c + 4) < 2 * KK i * cutHi i c := by
  have hKpos : 0 < KK i := KK_pos i
  have h := Nat.div_add_mod ((KK i + 1) * dRef i * (c + 4)) (2 * KK i)
  have hlt : (KK i + 1) * dRef i * (c + 4) % (2 * KK i) < 2 * KK i :=
    Nat.mod_lt _ (by omega)
  rw [cutHi_eq]
  have hexp : 2 * KK i * ((KK i + 1) * dRef i * (c + 4) / (2 * KK i) + 1)
      = 2 * KK i * ((KK i + 1) * dRef i * (c + 4) / (2 * KK i)) + 2 * KK i := by ring
  omega

/-! ### The flanks are ordered, and the gap is a `3/K` fraction -/

lemma KK_mul_dRef_mul_le (i c : ℕ) :
    KK i * dRef i * c ≤ 2 * (KK i + 1) * cutLo i c + 2 * (KK i + 1) := by
  have h := Nat.div_add_mod (KK i * dRef i * c) (2 * (KK i + 1))
  have hlt : KK i * dRef i * c % (2 * (KK i + 1)) < 2 * (KK i + 1) :=
    Nat.mod_lt _ (by have := KK_pos i; omega)
  rw [cutLo_eq]
  omega

lemma two_KK_mul_cutHi_le (i c : ℕ) :
    2 * KK i * cutHi i c ≤ (KK i + 1) * dRef i * (c + 4) + 2 * KK i := by
  have hKpos : 0 < KK i := KK_pos i
  have h := Nat.div_add_mod ((KK i + 1) * dRef i * (c + 4)) (2 * KK i)
  rw [cutHi_eq]
  have hexp : 2 * KK i * ((KK i + 1) * dRef i * (c + 4) / (2 * KK i) + 1)
      = 2 * KK i * ((KK i + 1) * dRef i * (c + 4) / (2 * KK i)) + 2 * KK i := by ring
  omega

lemma cutLo_le_cutHi (i c : ℕ) : cutLo i c ≤ cutHi i c := by
  have hKpos : 0 < KK i := KK_pos i
  have hnum : KK i * dRef i * c ≤ (KK i + 1) * dRef i * (c + 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_succ _)) (by omega)
  have hden : 2 * KK i ≤ 2 * (KK i + 1) := by omega
  have h := Nat.div_le_div hnum hden (by omega)
  rw [cutLo_eq, cutHi_eq]
  omega

/-- **The flank gap is a `3/K` fraction of the lower flank**, plus `4·d_ref + 5`.  Stated times
`2K²` to stay division-free: this is `cutHi ≤ cutLo·(1 + 3/K) + 4·d_ref + 5`. -/
lemma flank_gap (i c : ℕ) :
    2 * (KK i : ℝ) ^ 2 * (cutHi i c : ℝ)
      ≤ 2 * (KK i : ℝ) ^ 2 * (cutLo i c : ℝ) + 6 * (KK i : ℝ) * (cutLo i c : ℝ)
        + 8 * (KK i : ℝ) ^ 2 * (dRef i : ℝ) + 10 * (KK i : ℝ) ^ 2 := by
  have hk : (1 : ℝ) ≤ (KK i : ℝ) := by
    have := KK_pos i
    exact_mod_cast this
  have ha : (0 : ℝ) ≤ (dRef i : ℝ) := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ (cutLo i c : ℝ) := Nat.cast_nonneg _
  have hcc : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  have hH : 2 * (KK i : ℝ) * (cutHi i c : ℝ)
      ≤ ((KK i : ℝ) + 1) * (dRef i : ℝ) * ((c : ℝ) + 4) + 2 * (KK i : ℝ) := by
    have h := two_KK_mul_cutHi_le i c
    have := (Nat.cast_le (α := ℝ)).2 h
    push_cast at this
    linarith
  have hLo : (KK i : ℝ) * (dRef i : ℝ) * (c : ℝ)
      ≤ 2 * ((KK i : ℝ) + 1) * (cutLo i c : ℝ) + 2 * ((KK i : ℝ) + 1) := by
    have h := KK_mul_dRef_mul_le i c
    have := (Nat.cast_le (α := ℝ)).2 h
    push_cast at this
    linarith
  have h1 : 2 * (KK i : ℝ) * (KK i : ℝ) * (cutHi i c : ℝ)
      ≤ ((KK i : ℝ) + 1) * ((KK i : ℝ) * (dRef i : ℝ) * (c : ℝ))
        + 4 * (KK i : ℝ) * ((KK i : ℝ) + 1) * (dRef i : ℝ) + 2 * (KK i : ℝ) * (KK i : ℝ) := by
    nlinarith [hH, hk]
  have h2 : ((KK i : ℝ) + 1) * ((KK i : ℝ) * (dRef i : ℝ) * (c : ℝ))
      ≤ ((KK i : ℝ) + 1) * (2 * ((KK i : ℝ) + 1) * (cutLo i c : ℝ) + 2 * ((KK i : ℝ) + 1)) := by
    nlinarith [hLo, hk]
  have e1 : (0 : ℝ) ≤ ((KK i : ℝ) - 1) * (cutLo i c : ℝ) :=
    mul_nonneg (by linarith) hL
  have e2 : (0 : ℝ) ≤ ((KK i : ℝ) - 1) * ((KK i : ℝ) * (dRef i : ℝ)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) ha)
  have e3 : (0 : ℝ) ≤ ((KK i : ℝ) - 1) * (3 * (KK i : ℝ) + 1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [h1, h2, e1, e2, e3, hk]

/-! ### The lower inclusion -/

/-- **Below the lower flank, every atom's window is consumed.**  This is the inclusion
`bandWtr i (cutLo i c) ×ˢ univ ⊆ pairsLe i c`. -/
theorem two_kIdx_le_of_lt_cutLo (i c : ℕ) {n : ℕ} (hn : n < cutLo i c)
    (α : (gridAt i).Atom) : 2 * kIdx (gridAt i) n α ≤ c := by
  have hKpos : 0 < KK i := KK_pos i
  have hdpos : 0 < dRef i := dRef_pos i
  have hflank := two_mul_succ_mul_cutLo_le i c
  have hstep : 2 * (KK i + 1) * n + 2 * (KK i + 1) ≤ 2 * (KK i + 1) * cutLo i c := by
    have h := Nat.mul_le_mul_left (2 * (KK i + 1)) hn
    rw [Nat.mul_succ] at h
    exact h
  have hmulk : (gridAt i).d α * kIdx (gridAt i) n α ≤ n := mul_kIdx_le _ _ _
  have hspread : KK i * dRef i ≤ (KK i + 1) * (gridAt i).d α := KK_mul_dRef_le i α
  have hchain : KK i * dRef i * (2 * kIdx (gridAt i) n α)
      ≤ 2 * (KK i + 1) * ((gridAt i).d α * kIdx (gridAt i) n α) := by
    calc KK i * dRef i * (2 * kIdx (gridAt i) n α)
        ≤ ((KK i + 1) * (gridAt i).d α) * (2 * kIdx (gridAt i) n α) :=
          Nat.mul_le_mul_right _ hspread
      _ = 2 * (KK i + 1) * ((gridAt i).d α * kIdx (gridAt i) n α) := by ring
  have hn' : 2 * (KK i + 1) * ((gridAt i).d α * kIdx (gridAt i) n α)
      ≤ 2 * (KK i + 1) * n := Nat.mul_le_mul_left _ hmulk
  have hfinal : KK i * dRef i * (2 * kIdx (gridAt i) n α) < KK i * dRef i * c :=
    calc KK i * dRef i * (2 * kIdx (gridAt i) n α)
        ≤ 2 * (KK i + 1) * ((gridAt i).d α * kIdx (gridAt i) n α) := hchain
      _ ≤ 2 * (KK i + 1) * n := hn'
      _ < 2 * (KK i + 1) * n + 2 * (KK i + 1) := by omega
      _ ≤ 2 * (KK i + 1) * cutLo i c := hstep
      _ ≤ KK i * dRef i * c := hflank
  have := Nat.lt_of_mul_lt_mul_left hfinal
  omega

/-! ### The upper inclusion -/

/-- **A sample time with a consumed window lies below the upper flank.**  This is the inclusion
`pairsLe i c ⊆ bandWtr i (cutHi i c) ×ˢ univ`. -/
theorem lt_cutHi_of_two_kIdx_le (i X' c : ℕ) {n : ℕ} (hn : n ∈ PKtr i X')
    (α : (gridAt i).Atom) (h : 2 * kIdx (gridAt i) n α ≤ c) : n < cutHi i c := by
  have hKpos : 0 < KK i := KK_pos i
  obtain ⟨hspec, -⟩ := kIdx_spec (gridAt i) (X := X') hn α
  have h2n : 2 * n ≤ (gridAt i).d α * (c + 4) :=
    two_mul_le_of_two_kIdx_le α hspec.symm h
  have hspread : KK i * (gridAt i).d α ≤ (KK i + 1) * dRef i := KK_mul_d_le i α
  have hchain : 2 * KK i * n ≤ (KK i + 1) * dRef i * (c + 4) := by
    calc 2 * KK i * n = KK i * (2 * n) := by ring
      _ ≤ KK i * ((gridAt i).d α * (c + 4)) := Nat.mul_le_mul_left _ h2n
      _ = (KK i * (gridAt i).d α) * (c + 4) := by ring
      _ ≤ ((KK i + 1) * dRef i) * (c + 4) := Nat.mul_le_mul_right _ hspread
      _ = (KK i + 1) * dRef i * (c + 4) := by ring
  have hlt := lt_two_mul_KK_mul_cutHi i c
  have : 2 * KK i * n < 2 * KK i * cutHi i c := by omega
  exact Nat.lt_of_mul_lt_mul_left this

/-! ### The flanks as band truncations -/

/-- The lower flank's band truncation sits inside the wide band as long as the flank does not
overshoot the band top. -/
lemma bandWtr_cutLo_subset_bandW (i c : ℕ) (hle : cutLo i c ≤ wTop i) :
    bandWtr i (cutLo i c) ⊆ bandW i := by
  intro n hn
  rw [bandWtr, Finset.mem_filter] at hn
  rw [bandW, bandWtr, Finset.mem_filter]
  refine ⟨?_, hn.2⟩
  have hlt : n < cutLo i c := mem_bandWtr_lt (by rw [bandWtr, Finset.mem_filter]; exact hn)
  rw [PKtr, apSample, Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨by omega, hn.1.2⟩

/-- **The upper inclusion, on the band.** -/
theorem mem_bandWtr_cutHi (i c : ℕ) {n : ℕ} (hn : n ∈ bandW i) (α : (gridAt i).Atom)
    (h : 2 * kIdx (gridAt i) n α ≤ c) : n ∈ bandWtr i (cutHi i c) := by
  have hnPK : n ∈ PKtr i (wTop i) := bandW_subset i hn
  have hlt : n < cutHi i c := lt_cutHi_of_two_kIdx_le i (wTop i) c hnPK α h
  rw [bandW, bandWtr, Finset.mem_filter] at hn
  rw [bandWtr, Finset.mem_filter]
  refine ⟨?_, hn.2⟩
  rw [PKtr, apSample, Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hlt, hn.1.2⟩


/-! ### The band truncation is a difference of two samples -/

open Classical in
/-- Above the floor, `bandWtr i X'` is exactly `PKtr i X'` minus `PKtr i (wFloor i)`. -/
theorem card_bandWtr_add (i X' : ℕ) (h : wFloor i ≤ X') :
    (bandWtr i X').card + (PKtr i (wFloor i)).card = (PKtr i X').card := by
  classical
  have hcompl : (PKtr i X').filter (fun n => ¬ (wFloor i ≤ n)) = PKtr i (wFloor i) := by
    ext n
    simp only [PKtr, apSample, Finset.mem_filter, Finset.mem_range, not_le]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨lt_of_lt_of_le h1 h, h2⟩, h1⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := PKtr i X') (p := fun n => wFloor i ≤ n)
  rw [hcompl] at hsplit
  exact hsplit

lemma card_bandWtr_le_real (i X' : ℕ) (h : wFloor i ≤ X') :
    ((bandWtr i X').card : ℝ)
      ≤ ((X' : ℝ) - (wFloor i : ℝ)) / ((gridAt i).P₀ : ℝ) + 2 := by
  have hP₀pos : 0 < (gridAt i).P₀ := (gridAt i).P₀_pos
  have hP₀R : (0 : ℝ) < ((gridAt i).P₀ : ℝ) := by exact_mod_cast hP₀pos
  have hup := card_apSample_le X' (gridAt i).P₀ (gridAt i).b₀ hP₀pos (gridAt i).b₀_lt_P₀
  have hdown := card_apSample_ge (wFloor i) (gridAt i).P₀ (gridAt i).b₀ hP₀pos
    (gridAt i).b₀_lt_P₀
  have hadd := card_bandWtr_add i X' h
  have hR : ((bandWtr i X').card : ℝ) + ((PKtr i (wFloor i)).card : ℝ)
      = ((PKtr i X').card : ℝ) := by exact_mod_cast hadd
  have hsub : ((X' : ℝ) - (wFloor i : ℝ)) / ((gridAt i).P₀ : ℝ)
      = (X' : ℝ) / ((gridAt i).P₀ : ℝ) - (wFloor i : ℝ) / ((gridAt i).P₀ : ℝ) := by
    field_simp
  rw [hsub]
  have h1 : ((PKtr i X').card : ℝ) ≤ (X' : ℝ) / ((gridAt i).P₀ : ℝ) + 1 := hup
  have h2 : (wFloor i : ℝ) / ((gridAt i).P₀ : ℝ) - 1 ≤ ((PKtr i (wFloor i)).card : ℝ) := hdown
  linarith

lemma card_bandWtr_ge_real (i X' : ℕ) (h : wFloor i ≤ X') :
    ((X' : ℝ) - (wFloor i : ℝ)) / ((gridAt i).P₀ : ℝ) - 2
      ≤ ((bandWtr i X').card : ℝ) := by
  have hP₀pos : 0 < (gridAt i).P₀ := (gridAt i).P₀_pos
  have hP₀R : (0 : ℝ) < ((gridAt i).P₀ : ℝ) := by exact_mod_cast hP₀pos
  have hdown := card_apSample_ge X' (gridAt i).P₀ (gridAt i).b₀ hP₀pos (gridAt i).b₀_lt_P₀
  have hup := card_apSample_le (wFloor i) (gridAt i).P₀ (gridAt i).b₀ hP₀pos
    (gridAt i).b₀_lt_P₀
  have hadd := card_bandWtr_add i X' h
  have hR : ((bandWtr i X').card : ℝ) + ((PKtr i (wFloor i)).card : ℝ)
      = ((PKtr i X').card : ℝ) := by exact_mod_cast hadd
  have hsub : ((X' : ℝ) - (wFloor i : ℝ)) / ((gridAt i).P₀ : ℝ)
      = (X' : ℝ) / ((gridAt i).P₀ : ℝ) - (wFloor i : ℝ) / ((gridAt i).P₀ : ℝ) := by
    field_simp
  rw [hsub]
  have h1 : (X' : ℝ) / ((gridAt i).P₀ : ℝ) - 1 ≤ ((PKtr i X').card : ℝ) := hdown
  have h2 : ((PKtr i (wFloor i)).card : ℝ) ≤ (wFloor i : ℝ) / ((gridAt i).P₀ : ℝ) + 1 := hup
  linarith


/-! ### The floor dwarfs both `P₀` and the multiplier -/

lemma KK_le_Xlo (i : ℕ) : KK i ≤ Xlo (KK i) := by
  have hcube : KK i ^ 3 ≤ m (KK i) := by
    have h1 := m₁_ge_cube (show 1 ≤ KK i by have := KK_ge i; omega)
    unfold m
    omega
  have hKcube : KK i ≤ KK i ^ 3 := Nat.le_self_pow (by norm_num) _
  have hm : KK i ≤ 50 * 2 ^ m (KK i) := by
    have h2 : m (KK i) < 2 ^ m (KK i) := Nat.lt_two_pow_self
    omega
  have hXlo : Xlo (KK i) = 2 ^ (50 * 2 ^ m (KK i)) := by
    show (2 ^ (2 ^ m (KK i))) ^ 50 = _
    rw [← pow_mul]
    ring_nf
  have : KK i < 2 ^ (KK i) := Nat.lt_two_pow_self
  have hmono : (2 : ℕ) ^ (KK i) ≤ 2 ^ (50 * 2 ^ m (KK i)) :=
    Nat.pow_le_pow_right (by norm_num) hm
  omega

/-- `K·P₀ ≤ Xlo K`: the modulus is a tower below the certificate floor. -/
lemma KK_mul_P₀_le_Xlo (i : ℕ) : KK i * (gridAt i).P₀ ≤ Xlo (KK i) := by
  have hKR : (KK i : ℝ) ≤ (2 : ℝ) ^ (2 ^ m (KK i)) := by
    have hN : KK i ≤ 2 ^ (2 ^ m (KK i)) := by
      have h1 : KK i ≤ m (KK i) := by
        have h2 : KK i ^ 3 ≤ m (KK i) := by
          have h3 := m₁_ge_cube (show 1 ≤ KK i by have := KK_ge i; omega)
          unfold m
          omega
        have h4 : KK i ≤ KK i ^ 3 := Nat.le_self_pow (by norm_num) _
        omega
      have h5 : m (KK i) < 2 ^ m (KK i) := Nat.lt_two_pow_self
      have h6 : (2 : ℕ) ^ m (KK i) ≤ 2 ^ (2 ^ m (KK i)) :=
        Nat.pow_le_pow_right (by norm_num) (le_of_lt h5)
      omega
    exact_mod_cast hN
  have hP₀R := P₀_le_two_pow (K := KK i) (KK_hundred i)
  have hXloR : ((Xlo (KK i) : ℕ) : ℝ) = (2 : ℝ) ^ (50 * 2 ^ m (KK i)) := by
    show (((2 ^ (2 ^ m (KK i))) ^ 50 : ℕ) : ℝ) = _
    push_cast
    rw [← pow_mul]
    ring_nf
  have hprod : (KK i : ℝ) * ((gridAt i).P₀ : ℝ)
      ≤ (2 : ℝ) ^ (2 ^ m (KK i)) * (2 : ℝ) ^ (2 * 2 ^ m (KK i)) := by
    have h1 : (0 : ℝ) ≤ (KK i : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ ((gridAt i).P₀ : ℝ) := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ (2 ^ m (KK i)) := by positivity
    exact mul_le_mul hKR hP₀R h2 h3
  have hpow : (2 : ℝ) ^ (2 ^ m (KK i)) * (2 : ℝ) ^ (2 * 2 ^ m (KK i))
      ≤ (2 : ℝ) ^ (50 * 2 ^ m (KK i)) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have : (KK i : ℝ) * ((gridAt i).P₀ : ℝ) ≤ ((Xlo (KK i) : ℕ) : ℝ) := by
    rw [hXloR]; linarith
  exact_mod_cast this

lemma wFloor_eq' (i : ℕ) : wFloor i = gridDm (KK i) (N (KK i)) * (4 * Xlo (KK i)) := by
  rw [wFloor_eq, wLo_eq]

lemma Xlo_le_wFloor' (i : ℕ) : 4 * Xlo (KK i) ≤ wFloor i := by
  have hDm : 1 ≤ gridDm (KK i) (N (KK i)) := gridDm_pos _ _
  rw [wFloor_eq' i]
  exact Nat.le_mul_of_pos_left _ hDm

lemma KK_mul_P₀_le_wFloor (i : ℕ) : KK i * (gridAt i).P₀ ≤ wFloor i := by
  have h1 := KK_mul_P₀_le_Xlo i
  have h2 := Xlo_le_wFloor' i
  omega

lemma KK_mul_dRef_le_wFloor (i : ℕ) : KK i * dRef i ≤ wFloor i := by
  have hd : dRef i ≤ gridDm (KK i) (N (KK i)) :=
    gridOf.d_le (K := KK i) (N := N (KK i)) (KK_one_le i) (refAtom i)
  have hK := KK_le_Xlo i
  have hDm : 1 ≤ gridDm (KK i) (N (KK i)) := gridDm_pos _ _
  have hstep : KK i * dRef i ≤ Xlo (KK i) * gridDm (KK i) (N (KK i)) :=
    Nat.mul_le_mul hK hd
  have hfl : wFloor i = gridDm (KK i) (N (KK i)) * (4 * Xlo (KK i)) := wFloor_eq' i
  have : Xlo (KK i) * gridDm (KK i) (N (KK i))
      ≤ gridDm (KK i) (N (KK i)) * (4 * Xlo (KK i)) := by ring_nf; omega
  omega

/-! ### THE FLANK RATIO -/

/-- **The two flanks carry the same sample, to within `1 + 16/K`.**  This is the price of the
sandwich, and it vanishes; the band law's own capture error is already `O(K^{−1/4})`.
Stated times `K` to stay division-free. -/
theorem card_flank_ratio (i c : ℕ) (hg : 8 * wFloor i ≤ cutLo i c) :
    (KK i : ℝ) * ((bandWtr i (cutHi i c)).card : ℝ)
      ≤ ((KK i : ℝ) + 16) * ((bandWtr i (cutLo i c)).card : ℝ) := by
  have hWL : wFloor i ≤ cutLo i c := by omega
  have hWH : wFloor i ≤ cutHi i c := le_trans hWL (cutLo_le_cutHi i c)
  have hP₀pos : 0 < (gridAt i).P₀ := (gridAt i).P₀_pos
  have hPpos : (0 : ℝ) < ((gridAt i).P₀ : ℝ) := by exact_mod_cast hP₀pos
  have hPne : ((gridAt i).P₀ : ℝ) ≠ 0 := ne_of_gt hPpos
  have hP1 : (1 : ℝ) ≤ ((gridAt i).P₀ : ℝ) := by exact_mod_cast hP₀pos
  have hk : (1 : ℝ) ≤ (KK i : ℝ) := by
    have := KK_pos i
    exact_mod_cast this
  -- the two flank cardinalities, cleared of the division by `P₀`
  have hidH : ((gridAt i).P₀ : ℝ) * (((cutHi i c : ℝ) - (wFloor i : ℝ))
      / ((gridAt i).P₀ : ℝ)) = (cutHi i c : ℝ) - (wFloor i : ℝ) := by field_simp
  have hidL : ((gridAt i).P₀ : ℝ) * (((cutLo i c : ℝ) - (wFloor i : ℝ))
      / ((gridAt i).P₀ : ℝ)) = (cutLo i c : ℝ) - (wFloor i : ℝ) := by field_simp
  have hcH : ((gridAt i).P₀ : ℝ) * ((bandWtr i (cutHi i c)).card : ℝ)
      ≤ ((cutHi i c : ℝ) - (wFloor i : ℝ)) + 2 * ((gridAt i).P₀ : ℝ) := by
    have h := card_bandWtr_le_real i (cutHi i c) hWH
    have h2 := mul_le_mul_of_nonneg_left h (le_of_lt hPpos)
    rw [mul_add, hidH] at h2
    linarith
  have hcL : ((cutLo i c : ℝ) - (wFloor i : ℝ)) - 2 * ((gridAt i).P₀ : ℝ)
      ≤ ((gridAt i).P₀ : ℝ) * ((bandWtr i (cutLo i c)).card : ℝ) := by
    have h := card_bandWtr_ge_real i (cutLo i c) hWL
    have h2 := mul_le_mul_of_nonneg_left h (le_of_lt hPpos)
    rw [mul_sub, hidL] at h2
    linarith
  -- the flank gap, divided by `2K`
  have hHL : (KK i : ℝ) * (cutHi i c : ℝ)
      ≤ (KK i : ℝ) * (cutLo i c : ℝ) + 3 * (cutLo i c : ℝ)
        + 4 * ((KK i : ℝ) * (dRef i : ℝ)) + 5 * (KK i : ℝ) := by
    have h2k : (0 : ℝ) < 2 * (KK i : ℝ) := by linarith
    refine le_of_mul_le_mul_left ?_ h2k
    calc 2 * (KK i : ℝ) * ((KK i : ℝ) * (cutHi i c : ℝ))
        = 2 * (KK i : ℝ) ^ 2 * (cutHi i c : ℝ) := by ring
      _ ≤ 2 * (KK i : ℝ) ^ 2 * (cutLo i c : ℝ) + 6 * (KK i : ℝ) * (cutLo i c : ℝ)
          + 8 * (KK i : ℝ) ^ 2 * (dRef i : ℝ) + 10 * (KK i : ℝ) ^ 2 := flank_gap i c
      _ = 2 * (KK i : ℝ) * ((KK i : ℝ) * (cutLo i c : ℝ) + 3 * (cutLo i c : ℝ)
          + 4 * ((KK i : ℝ) * (dRef i : ℝ)) + 5 * (KK i : ℝ)) := by ring
  -- the floor dwarfs `P₀` and `d_ref`
  have hka : (KK i : ℝ) * (dRef i : ℝ) ≤ (wFloor i : ℝ) := by
    have h := KK_mul_dRef_le_wFloor i
    have := (Nat.cast_le (α := ℝ)).2 h
    push_cast at this
    linarith
  have hkP : (KK i : ℝ) * ((gridAt i).P₀ : ℝ) ≤ (wFloor i : ℝ) := by
    have h := KK_mul_P₀_le_wFloor i
    have := (Nat.cast_le (α := ℝ)).2 h
    push_cast at this
    linarith
  have hk_le : (KK i : ℝ) ≤ (KK i : ℝ) * ((gridAt i).P₀ : ℝ) :=
    le_mul_of_one_le_right (by linarith) hP1
  have hP_le : ((gridAt i).P₀ : ℝ) ≤ (KK i : ℝ) * ((gridAt i).P₀ : ℝ) :=
    le_mul_of_one_le_left (by linarith) hk
  have hgR : 8 * (wFloor i : ℝ) ≤ (cutLo i c : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 hg
    push_cast at this
    linarith
  have hW0 : (0 : ℝ) ≤ (wFloor i : ℝ) := Nat.cast_nonneg _
  -- the core linear step
  have hstep : (KK i : ℝ) * (((cutHi i c : ℝ) - (wFloor i : ℝ)) + 2 * ((gridAt i).P₀ : ℝ))
      ≤ ((KK i : ℝ) + 16) * (((cutLo i c : ℝ) - (wFloor i : ℝ))
          - 2 * ((gridAt i).P₀ : ℝ)) := by
    nlinarith [hHL, hka, hkP, hk_le, hP_le, hgR, hW0, hk]
  have hmain : ((gridAt i).P₀ : ℝ) * ((KK i : ℝ) * ((bandWtr i (cutHi i c)).card : ℝ))
      ≤ ((gridAt i).P₀ : ℝ) * (((KK i : ℝ) + 16)
          * ((bandWtr i (cutLo i c)).card : ℝ)) := by
    calc ((gridAt i).P₀ : ℝ) * ((KK i : ℝ) * ((bandWtr i (cutHi i c)).card : ℝ))
        = (KK i : ℝ) * (((gridAt i).P₀ : ℝ) * ((bandWtr i (cutHi i c)).card : ℝ)) := by ring
      _ ≤ (KK i : ℝ) * (((cutHi i c : ℝ) - (wFloor i : ℝ)) + 2 * ((gridAt i).P₀ : ℝ)) :=
          mul_le_mul_of_nonneg_left hcH (by linarith)
      _ ≤ ((KK i : ℝ) + 16) * (((cutLo i c : ℝ) - (wFloor i : ℝ))
            - 2 * ((gridAt i).P₀ : ℝ)) := hstep
      _ ≤ ((KK i : ℝ) + 16) * (((gridAt i).P₀ : ℝ)
            * ((bandWtr i (cutLo i c)).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hcL (by linarith)
      _ = ((gridAt i).P₀ : ℝ) * (((KK i : ℝ) + 16)
            * ((bandWtr i (cutLo i c)).card : ℝ)) := by ring
  exact le_of_mul_le_mul_left hmain hPpos

end NormalNumbers.G4.Sched
