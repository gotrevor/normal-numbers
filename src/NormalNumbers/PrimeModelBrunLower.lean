/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# The lower Brun sieve: weights, first-failure decomposition, pointwise minorant

This file builds the **lower** Brun sieve weights of `papers/prime-model-sieve-assessment.md`
from scratch, over an arbitrary finite set `U` of distinct naturals (primality is never used).

For a finite set `E` listed in *decreasing* order `p₁ > p₂ > ⋯ > p_r` and a cutoff sequence
`Y : ℕ → ℕ`, the Brun weight is

    lam Y E = (-1) ^ r   if `p_{2j} ≤ Y j` for every `2j ≤ r`,     0 otherwise.

Instead of lists we use the *rank from the top*: for `q ∈ E`,
`ab E q = #{p ∈ E | q < p}` is the rank of `q` minus one, so "`q` sits at an even position"
means `ab E q` is odd, and the position is then `(ab E q + 1) / 2`.  This makes admissibility
(`Adm`) a purely local, decidable condition and — crucially — one that only depends on the part
of `E` weakly above each element.

## Main results

* `sum_not_adm_eq` — the **first-failure decomposition** (the engine of the file): for any
  weight function `f` and any `B`,
  `∑_{E ⊆ B, ¬ Adm E} (-1)^{#E} ∏_{p ∈ E} f p
     = ∑_{F ⊆ B, FirstFail F} (∏_{p ∈ F} f p) · ∏_{p ∈ B, p < min F} (1 - f p)`.
  Every failed subset is `F ∪ S` for a unique first failed even prefix `F` and an arbitrary
  set `S` of elements below `F`; the inner sum over `S` telescopes by `Finset.prod_sub`.
* `sum_lam_le_indicator` — **the pointwise minorant (property (2))**: for *every* `B ⊆ U`,
  `∑_{E ⊆ B} lam Y E ≤ if B = ∅ then 1 else 0`.  Obtained from `sum_not_adm_eq` with `f = 1`:
  each first-failure block contributes `∏_{p < min F} (1 - 1) ≥ 0`.
* `lam_abs_le_one` — `|lam Y E| ≤ 1` (part of property (1)).
* `defect_eq` — the **exact model defect** `V - ∑_E lam E ∏_E g` as a nonnegative sum over
  first-failure prefixes; this is the starting point of the relative-error estimate (3).
-/

namespace NormalNumbers.PrimeModel.Brun

open Finset

/-- `ab E q` is the number of elements of `E` strictly above `q`.  For `q ∈ E` this is the rank
of `q`, counted from the largest element, minus one. -/
def ab (E : Finset ℕ) (q : ℕ) : ℕ := (E.filter (fun p => q < p)).card

/-- Brun admissibility: every element sitting at an **even** position `(ab + 1)/2` from the top
(i.e. with `ab` odd) is at most the corresponding cutoff. -/
def Adm (Y : ℕ → ℕ) (E : Finset ℕ) : Prop :=
  ∀ q ∈ E, Odd (ab E q) → q ≤ Y ((ab E q + 1) / 2)

instance (Y : ℕ → ℕ) (E : Finset ℕ) : Decidable (Adm Y E) := by unfold Adm; infer_instance

/-- The Brun lower-sieve weight. -/
noncomputable def lam (Y : ℕ → ℕ) (E : Finset ℕ) : ℝ := if Adm Y E then (-1) ^ E.card else 0

lemma lam_abs_le_one (Y : ℕ → ℕ) (E : Finset ℕ) : |lam Y E| ≤ 1 := by
  unfold lam; split
  · simp
  · norm_num

lemma lam_eq_of_adm {Y : ℕ → ℕ} {E : Finset ℕ} (h : Adm Y E) :
    lam Y E = (-1) ^ E.card := if_pos h

lemma lam_eq_zero_of_not_adm {Y : ℕ → ℕ} {E : Finset ℕ} (h : ¬ Adm Y E) : lam Y E = 0 := if_neg h

/-! ### Elementary properties of `ab` -/

lemma ab_filter_ge (E : Finset ℕ) {q0 q : ℕ} (h : q0 ≤ q) :
    ab (E.filter (fun p => q0 ≤ p)) q = ab E q := by
  unfold ab
  congr 1
  ext p
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hp, _⟩, h2⟩; exact ⟨hp, h2⟩
  · rintro ⟨hp, h2⟩; exact ⟨⟨hp, h.trans h2.le⟩, h2⟩

lemma ab_union_of_lt {F S : Finset ℕ} (hS : ∀ p ∈ S, ∀ r ∈ F, p < r) {q : ℕ} (hq : q ∈ F) :
    ab (F ∪ S) q = ab F q := by
  unfold ab
  congr 1
  ext p
  simp only [mem_filter, mem_union]
  constructor
  · rintro ⟨hp | hp, h2⟩
    · exact ⟨hp, h2⟩
    · exact absurd (hS p hp q hq) (by omega)
  · rintro ⟨hp, h2⟩; exact ⟨Or.inl hp, h2⟩

lemma ab_min {F : Finset ℕ} {q0 : ℕ} (hq0 : q0 ∈ F) (h : ∀ p ∈ F, q0 ≤ p) :
    ab F q0 = F.card - 1 := by
  have : F.filter (fun p => q0 < p) = F.erase q0 := by
    ext p
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨hp, h2⟩; exact ⟨by omega, hp⟩
    · rintro ⟨h2, hp⟩; exact ⟨hp, lt_of_le_of_ne (h p hp) (Ne.symm h2)⟩
  unfold ab
  rw [this, card_erase_of_mem hq0]

/-! ### First failures -/

/-- The elements of `E` that violate admissibility. -/
def FailSet (Y : ℕ → ℕ) (E : Finset ℕ) : Finset ℕ :=
  E.filter (fun q => Odd (ab E q) ∧ ¬ q ≤ Y ((ab E q + 1) / 2))

lemma failSet_nonempty_iff (Y : ℕ → ℕ) (E : Finset ℕ) :
    (FailSet Y E).Nonempty ↔ ¬ Adm Y E := by
  unfold FailSet Adm
  rw [Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨q, hq, h1, h2⟩ hA; exact h2 (hA q hq h1)
  · intro h
    by_contra hc
    refine h fun q hq h1 => ?_
    by_contra h2
    exact hc ⟨q, hq, h1, h2⟩

private lemma sup_id_mem {s : Finset ℕ} (h : s.Nonempty) : s.sup id ∈ s := by
  have : s.sup id = s.max' h := by rw [Finset.max'_eq_sup', Finset.sup'_eq_sup]
  rw [this]; exact s.max'_mem h

/-- The largest failing element of `E` (junk value `0` if there is none). -/
def topFail (Y : ℕ → ℕ) (E : Finset ℕ) : ℕ := (FailSet Y E).sup id

/-- The **first failed prefix** of `E`: the part of `E` weakly above the largest failing
element.  Its length is even, and it is the first even prefix that violates its cutoff. -/
def ff (Y : ℕ → ℕ) (E : Finset ℕ) : Finset ℕ := E.filter (fun p => topFail Y E ≤ p)

/-- `F` is a first failed prefix: it has a least element `q0` which fails its (even) cutoff,
and no element above `q0` fails. -/
def FirstFail (Y : ℕ → ℕ) (F : Finset ℕ) : Prop :=
  ∃ q0 ∈ F, (∀ p ∈ F, q0 ≤ p) ∧ Odd (ab F q0) ∧ ¬ q0 ≤ Y ((ab F q0 + 1) / 2) ∧
    ∀ q ∈ F, q ≠ q0 → Odd (ab F q) → q ≤ Y ((ab F q + 1) / 2)

instance (Y : ℕ → ℕ) (F : Finset ℕ) : Decidable (FirstFail Y F) := by
  unfold FirstFail; infer_instance

/-- A first failed prefix has **even** cardinality: its least element sits at an even position
from the top. -/
lemma FirstFail.even_card {Y : ℕ → ℕ} {F : Finset ℕ} (h : FirstFail Y F) : Even F.card := by
  obtain ⟨q0, hq0, hmin, hodd, -, -⟩ := h
  rw [ab_min hq0 hmin] at hodd
  have h1 : 1 ≤ F.card := card_pos.2 ⟨q0, hq0⟩
  rw [Nat.odd_iff] at hodd
  rw [Nat.even_iff]
  omega

/-- The set of elements of `B` lying strictly below every element of `F`. -/
def below (B F : Finset ℕ) : Finset ℕ := B.filter (fun p => ∀ r ∈ F, p < r)

/-! ### Direction A: the first failed prefix of a non-admissible set -/

section DirA

variable {Y : ℕ → ℕ} {E : Finset ℕ} (hE : ¬ Adm Y E)

include hE

private lemma topFail_mem : topFail Y E ∈ FailSet Y E :=
  sup_id_mem ((failSet_nonempty_iff Y E).2 hE)

private lemma topFail_max {q : ℕ} (hq : q ∈ FailSet Y E) : q ≤ topFail Y E :=
  Finset.le_sup (f := id) hq

lemma ff_firstFail : FirstFail Y (ff Y E) := by
  set q0 := topFail Y E with hq0def
  have hmem := topFail_mem hE
  rw [FailSet, mem_filter] at hmem
  obtain ⟨hq0E, hq0odd, hq0fail⟩ := hmem
  have habq0 : ab (ff Y E) q0 = ab E q0 := ab_filter_ge E (le_refl q0)
  refine ⟨q0, mem_filter.2 ⟨hq0E, le_refl q0⟩, fun p hp => (mem_filter.1 hp).2, ?_, ?_, ?_⟩
  · rw [habq0]; exact hq0odd
  · rw [habq0]; exact hq0fail
  · intro q hq hne hodd
    obtain ⟨hqE, hqge⟩ := mem_filter.1 hq
    have habq : ab (ff Y E) q = ab E q := ab_filter_ge E hqge
    rw [habq] at hodd ⊢
    by_contra hcon
    have : q ∈ FailSet Y E := mem_filter.2 ⟨hqE, hodd, hcon⟩
    exact hne (le_antisymm (topFail_max hE this) hqge)

lemma ff_subset : ff Y E ⊆ E := filter_subset _ _

lemma sdiff_ff_mem {B : Finset ℕ} (hEB : E ⊆ B) : E \ ff Y E ⊆ below B (ff Y E) := by
  intro p hp
  rw [mem_sdiff, ff, mem_filter] at hp
  obtain ⟨hpE, hp2⟩ := hp
  have hlt : p < topFail Y E := by
    by_contra hc
    exact hp2 ⟨hpE, by omega⟩
  refine mem_filter.2 ⟨hEB hpE, fun r hr => ?_⟩
  exact lt_of_lt_of_le hlt (mem_filter.1 hr).2

lemma ff_union_sdiff : ff Y E ∪ (E \ ff Y E) = E :=
  Finset.union_sdiff_of_subset (ff_subset hE)

end DirA

/-! ### Direction B: reconstructing a non-admissible set from a prefix and a tail -/

section DirB

variable {Y : ℕ → ℕ} {F S : Finset ℕ}

lemma disjoint_of_below (hS : ∀ p ∈ S, ∀ r ∈ F, p < r) : Disjoint F S := by
  rw [Finset.disjoint_right]
  intro p hpS hpF
  exact absurd (hS p hpS p hpF) (lt_irrefl p)

lemma union_not_adm (hF : FirstFail Y F) (hS : ∀ p ∈ S, ∀ r ∈ F, p < r) :
    ¬ Adm Y (F ∪ S) := by
  obtain ⟨q0, hq0, -, hodd, hfail, -⟩ := hF
  intro hA
  have h := hA q0 (mem_union_left _ hq0)
  rw [ab_union_of_lt hS hq0] at h
  exact hfail (h hodd)

lemma topFail_union (_hF : FirstFail Y F) (hS : ∀ p ∈ S, ∀ r ∈ F, p < r) :
    ∀ q0 ∈ F, (∀ p ∈ F, q0 ≤ p) → Odd (ab F q0) → ¬ q0 ≤ Y ((ab F q0 + 1) / 2) →
      (∀ q ∈ F, q ≠ q0 → Odd (ab F q) → q ≤ Y ((ab F q + 1) / 2)) →
      topFail Y (F ∪ S) = q0 := by
  intro q0 hq0 hmin hodd hfail hrest
  have hq0mem : q0 ∈ FailSet Y (F ∪ S) := by
    refine mem_filter.2 ⟨mem_union_left _ hq0, ?_, ?_⟩
    · rw [ab_union_of_lt hS hq0]; exact hodd
    · rw [ab_union_of_lt hS hq0]; exact hfail
  refine le_antisymm ?_ (Finset.le_sup (f := id) hq0mem)
  refine Finset.sup_le ?_
  intro q hq
  rw [FailSet, mem_filter] at hq
  obtain ⟨hqU, hqodd, hqfail⟩ := hq
  rcases mem_union.1 hqU with hqF | hqS
  · rw [ab_union_of_lt hS hqF] at hqodd hqfail
    by_cases hne : q = q0
    · simp [hne]
    · exact absurd (hrest q hqF hne hqodd) hqfail
  · exact le_of_lt (hS q hqS q0 hq0)

lemma ff_union (hF : FirstFail Y F) (hS : ∀ p ∈ S, ∀ r ∈ F, p < r) : ff Y (F ∪ S) = F := by
  obtain ⟨q0, hq0, hmin, hodd, hfail, hrest⟩ := hF
  have htop : topFail Y (F ∪ S) = q0 :=
    topFail_union ⟨q0, hq0, hmin, hodd, hfail, hrest⟩ hS q0 hq0 hmin hodd hfail hrest
  ext p
  rw [ff, mem_filter, htop, mem_union]
  constructor
  · rintro ⟨hp | hp, hge⟩
    · exact hp
    · exact absurd (hS p hp q0 hq0) (by omega)
  · intro hp; exact ⟨Or.inl hp, hmin p hp⟩

end DirB

/-! ### The first-failure decomposition -/

/-- The fibre of `ff` over a first failed prefix `F`, inside the non-admissible subsets of `B`,
is exactly `{F ∪ S : S ⊆ below B F}`. -/
lemma sum_fiber_eq (Y : ℕ → ℕ) (B F : Finset ℕ) (f : ℕ → ℝ) (hF : FirstFail Y F)
    (hFB : F ⊆ B) :
    ∑ E ∈ (B.powerset.filter (fun E => ¬ Adm Y E)).filter (fun E => ff Y E = F),
        ((-1 : ℝ) ^ E.card * ∏ p ∈ E, f p)
      = (∏ p ∈ F, f p) * ∏ p ∈ below B F, (1 - f p) := by
  classical
  have hbelow : ∀ S ∈ (below B F).powerset, ∀ p ∈ S, ∀ r ∈ F, p < r := by
    intro S hS p hp r hr
    have := (mem_powerset.1 hS) hp
    exact (mem_filter.1 this).2 r hr
  -- reindex the fibre by `S ↦ F ∪ S`
  have key : ∑ E ∈ (B.powerset.filter (fun E => ¬ Adm Y E)).filter (fun E => ff Y E = F),
        ((-1 : ℝ) ^ E.card * ∏ p ∈ E, f p)
      = ∑ S ∈ (below B F).powerset, ((-1 : ℝ) ^ (F ∪ S).card * ∏ p ∈ F ∪ S, f p) := by
    refine (Finset.sum_nbij' (i := fun S => F ∪ S) (j := fun E => E \ F) ?_ ?_ ?_ ?_ ?_).symm
    · intro S hS
      refine mem_filter.2 ⟨mem_filter.2 ⟨mem_powerset.2 ?_, union_not_adm hF (hbelow S hS)⟩,
        ff_union hF (hbelow S hS)⟩
      exact union_subset hFB (((mem_powerset.1 hS)).trans (filter_subset _ _))
    · intro E hE
      obtain ⟨hE1, hE2⟩ := mem_filter.1 hE
      obtain ⟨hEB, hEadm⟩ := mem_filter.1 hE1
      have := sdiff_ff_mem hEadm (mem_powerset.1 hEB)
      rw [hE2] at this
      exact mem_powerset.2 this
    · intro S hS
      have hdisj : Disjoint F S := disjoint_of_below (hbelow S hS)
      simp [Finset.union_sdiff_cancel_left hdisj]
    · intro E hE
      obtain ⟨hE1, hE2⟩ := mem_filter.1 hE
      obtain ⟨hEB, hEadm⟩ := mem_filter.1 hE1
      rw [← hE2]
      exact ff_union_sdiff hEadm
    · intro S _; rfl
  rw [key]
  have hcardF : Even F.card := hF.even_card
  have : ∀ S ∈ (below B F).powerset,
      ((-1 : ℝ) ^ (F ∪ S).card * ∏ p ∈ F ∪ S, f p)
        = (∏ p ∈ F, f p) * ((-1 : ℝ) ^ S.card * ∏ p ∈ S, f p) := by
    intro S hS
    have hdisj : Disjoint F S := disjoint_of_below (hbelow S hS)
    rw [Finset.card_union_of_disjoint hdisj, Finset.prod_union hdisj, pow_add,
      hcardF.neg_one_pow]
    ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
  congr 1
  have := Finset.prod_sub (fun _ : ℕ => (1 : ℝ)) f (below B F)
  simp only [Finset.prod_const_one] at this
  rw [this]
  exact Finset.sum_congr rfl fun S _ => by ring

/-- **First-failure decomposition.**  The alternating weighted sum over the *discarded* subsets
of `B` splits, without any error term, over first failed even prefixes. -/
theorem sum_not_adm_eq (Y : ℕ → ℕ) (B : Finset ℕ) (f : ℕ → ℝ) :
    ∑ E ∈ B.powerset.filter (fun E => ¬ Adm Y E), ((-1 : ℝ) ^ E.card * ∏ p ∈ E, f p)
      = ∑ F ∈ B.powerset.filter (fun F => FirstFail Y F),
          (∏ p ∈ F, f p) * ∏ p ∈ below B F, (1 - f p) := by
  classical
  have hmaps : ∀ E ∈ B.powerset.filter (fun E => ¬ Adm Y E),
      ff Y E ∈ B.powerset.filter (fun F => FirstFail Y F) := by
    intro E hE
    obtain ⟨hEB, hEadm⟩ := mem_filter.1 hE
    exact mem_filter.2 ⟨mem_powerset.2 ((ff_subset hEadm).trans (mem_powerset.1 hEB)),
      ff_firstFail hEadm⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun F hF => ?_
  obtain ⟨hFB, hFF⟩ := mem_filter.1 hF
  exact sum_fiber_eq Y B F f hFF (mem_powerset.1 hFB)

/-! ### Property (2): the pointwise minorant -/

/-- **Property (2).**  For *every* subset `B` of the bad primes, the Brun weights sum to at most
the indicator of `B = ∅`.  No hypothesis on `Y` whatsoever. -/
theorem sum_lam_le_indicator (Y : ℕ → ℕ) (B : Finset ℕ) :
    ∑ E ∈ B.powerset, lam Y E ≤ if B = ∅ then 1 else 0 := by
  classical
  have hsplit : ∑ E ∈ B.powerset, ((-1 : ℝ) ^ E.card)
      = (∑ E ∈ B.powerset, lam Y E)
        + ∑ E ∈ B.powerset.filter (fun E => ¬ Adm Y E), ((-1 : ℝ) ^ E.card) := by
    rw [← Finset.sum_filter_add_sum_filter_not B.powerset (fun E => Adm Y E)]
    congr 1
    · exact (Finset.sum_congr rfl fun E hE => lam_eq_of_adm (mem_filter.1 hE).2).symm.trans
        (by
          rw [← Finset.sum_filter_add_sum_filter_not B.powerset (fun E => Adm Y E)
            (fun E => lam Y E)]
          have : ∑ E ∈ B.powerset.filter (fun E => ¬ Adm Y E), lam Y E = 0 :=
            Finset.sum_eq_zero fun E hE => lam_eq_zero_of_not_adm (mem_filter.1 hE).2
          rw [this, add_zero])
  have hfull : ∑ E ∈ B.powerset, ((-1 : ℝ) ^ E.card) = if B = ∅ then 1 else 0 := by
    have := Finset.sum_powerset_neg_one_pow_card (x := B)
    have h2 : ((∑ E ∈ B.powerset, ((-1 : ℤ) ^ E.card) : ℤ) : ℝ)
        = ∑ E ∈ B.powerset, ((-1 : ℝ) ^ E.card) := by push_cast; ring
    rw [← h2, this]
    split <;> norm_num
  have hrest : 0 ≤ ∑ E ∈ B.powerset.filter (fun E => ¬ Adm Y E), ((-1 : ℝ) ^ E.card) := by
    have := sum_not_adm_eq Y B (fun _ => (1 : ℝ))
    simp only [Finset.prod_const_one, mul_one] at this
    rw [this]
    refine Finset.sum_nonneg fun F _ => ?_
    rw [one_mul]
    exact Finset.prod_nonneg fun p _ => by norm_num
  rw [hfull] at hsplit
  linarith [hsplit, hrest]

/-! ### The exact model defect (entry point for the relative-error bound (3)) -/

/-- The Brun model sum differs from the true product `∏ (1 - g p)` by an explicit, termwise
**nonnegative** sum over first failed even prefixes.  This is the identity that the
relative-error estimate (3) bounds. -/
theorem defect_eq (Y : ℕ → ℕ) (U : Finset ℕ) (g : ℕ → ℝ) :
    (∏ p ∈ U, (1 - g p)) - ∑ E ∈ U.powerset, lam Y E * ∏ p ∈ E, g p
      = ∑ F ∈ U.powerset.filter (fun F => FirstFail Y F),
          (∏ p ∈ F, g p) * ∏ p ∈ below U F, (1 - g p) := by
  classical
  have hfull : ∏ p ∈ U, (1 - g p)
      = ∑ E ∈ U.powerset, ((-1 : ℝ) ^ E.card * ∏ p ∈ E, g p) := by
    have := Finset.prod_sub (fun _ : ℕ => (1 : ℝ)) g U
    simp only [Finset.prod_const_one] at this
    rw [this]
    exact Finset.sum_congr rfl fun E _ => by ring
  have hlam : ∑ E ∈ U.powerset, lam Y E * ∏ p ∈ E, g p
      = ∑ E ∈ U.powerset.filter (fun E => Adm Y E), ((-1 : ℝ) ^ E.card * ∏ p ∈ E, g p) := by
    rw [← Finset.sum_filter_add_sum_filter_not U.powerset (fun E => Adm Y E)
      (fun E => lam Y E * ∏ p ∈ E, g p)]
    have h0 : ∑ E ∈ U.powerset.filter (fun E => ¬ Adm Y E), (lam Y E * ∏ p ∈ E, g p) = 0 :=
      Finset.sum_eq_zero fun E hE => by
        rw [lam_eq_zero_of_not_adm (mem_filter.1 hE).2]; ring
    rw [h0, add_zero]
    exact Finset.sum_congr rfl fun E hE => by rw [lam_eq_of_adm (mem_filter.1 hE).2]
  rw [hfull, hlam, ← sum_not_adm_eq Y U g,
    ← Finset.sum_filter_add_sum_filter_not U.powerset (fun E => Adm Y E)
      (fun E => (-1 : ℝ) ^ E.card * ∏ p ∈ E, g p)]
  ring

/-! ### Property (1): the support bound

The rank map `ab E : E → range #E` is a bijection (it is strictly antitone on `E`), so a
pointwise bound `q ≤ W (ab E q)` turns into `∏_{q ∈ E} q ≤ ∏_{i < #E} W i`.  For an admissible
`E` the pointwise bound is `W i = y` at `i = 0` and `W i = Y ((i+1)/2)` for `i ≥ 1`: at an odd
`ab` this *is* admissibility, and at an even `ab = 2j` the element directly above sits at
`ab = 2j-1` and is `≤ Y j`, with `(2j+1)/2 = j`. -/

lemma ab_lt_card {E : Finset ℕ} {q : ℕ} (hq : q ∈ E) : ab E q < E.card := by
  unfold ab
  refine card_lt_card ⟨filter_subset _ _, ?_⟩
  intro hsub
  have := hsub hq
  rw [mem_filter] at this
  exact absurd this.2 (lt_irrefl q)

lemma ab_lt_ab {E : Finset ℕ} {q q' : ℕ} (hq' : q' ∈ E) (h : q < q') : ab E q' < ab E q := by
  unfold ab
  refine card_lt_card ⟨?_, ?_⟩
  · intro p hp
    rw [mem_filter] at hp ⊢
    exact ⟨hp.1, h.trans hp.2⟩
  · intro hsub
    have := hsub (mem_filter.2 ⟨hq', h⟩)
    rw [mem_filter] at this
    exact absurd this.2 (lt_irrefl q')

lemma ab_injOn (E : Finset ℕ) : Set.InjOn (ab E) E := by
  intro q hq q' hq' h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd h (ne_of_gt (ab_lt_ab hq' hlt))
  · exact absurd h.symm (ne_of_gt (ab_lt_ab hq hlt))

lemma image_ab (E : Finset ℕ) : E.image (ab E) = Finset.range E.card := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro i hi
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hi
    exact mem_range.2 (ab_lt_card hq)
  · rw [Finset.card_range, Finset.card_image_of_injOn (ab_injOn E)]

/-- Reindexing along the rank map. -/
lemma prod_comp_ab (E : Finset ℕ) (W : ℕ → ℕ) :
    ∏ q ∈ E, W (ab E q) = ∏ i ∈ Finset.range E.card, W i := by
  rw [← image_ab E, Finset.prod_image (fun a ha b hb h => ab_injOn E ha hb h)]

/-- The element of `E` directly above `q`. -/
lemma exists_ab_pred {E : Finset ℕ} {q : ℕ} (hq : q ∈ E) (h : ab E q ≠ 0) :
    ∃ q' ∈ E, q < q' ∧ ab E q' + 1 = ab E q := by
  have hne : (E.filter (fun p => q < p)).Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.pos_of_ne_zero h
  set q' := (E.filter (fun p => q < p)).min' hne with hq'def
  have hq'mem := (E.filter (fun p => q < p)).min'_mem hne
  rw [mem_filter] at hq'mem
  refine ⟨q', hq'mem.1, hq'mem.2, ?_⟩
  have hfil : E.filter (fun p => q' < p) = (E.filter (fun p => q < p)).erase q' := by
    ext p
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨hp, h2⟩
      exact ⟨h2.ne', hp, hq'mem.2.trans h2⟩
    · rintro ⟨hne2, hp, h2⟩
      refine ⟨hp, lt_of_le_of_ne ?_ (Ne.symm hne2)⟩
      exact Finset.min'_le _ p (mem_filter.2 ⟨hp, h2⟩)
  have hcard : (E.filter (fun p => q' < p)).card = (E.filter (fun p => q < p)).card - 1 := by
    rw [hfil, card_erase_of_mem (mem_filter.2 ⟨hq'mem.1, hq'mem.2⟩)]
  have hpos : 0 < (E.filter (fun p => q < p)).card := Nat.pos_of_ne_zero h
  show ab E q' + 1 = ab E q
  unfold ab
  omega

/-- The pointwise cutoff bound available to every element of an admissible set: an element at
rank `≥ 2` from the top is bounded by the cutoff of its **pair**. -/
lemma le_cutoff_of_adm {Y : ℕ → ℕ} {E : Finset ℕ} (hA : Adm Y E) {q : ℕ} (hq : q ∈ E)
    (h : ab E q ≠ 0) : q ≤ Y ((ab E q + 1) / 2) := by
  rcases Nat.even_or_odd (ab E q) with hev | hodd
  · obtain ⟨q', hq', hlt, hpred⟩ := exists_ab_pred hq h
    have hoddq' : Odd (ab E q') := by
      rw [Nat.even_iff] at hev; rw [Nat.odd_iff]; omega
    have := hA q' hq' hoddq'
    have heq : (ab E q' + 1) / 2 = (ab E q + 1) / 2 := by
      rw [Nat.even_iff] at hev; omega
    rw [heq] at this
    exact le_trans hlt.le this
  · exact hA q hq hodd

/-- **Support, combinatorial half.**  For an admissible `E` whose elements are all `≤ y`,
`∏ E ≤ y · Y 1 ^ 2 · Y 2 ^ 2 ⋯`, in the precise form `∏_{i < #E} W i`. -/
theorem prod_le_of_adm {Y : ℕ → ℕ} {E : Finset ℕ} (hA : Adm Y E) {y : ℕ}
    (hy : ∀ p ∈ E, p ≤ y) :
    ∏ p ∈ E, p ≤ ∏ i ∈ Finset.range E.card, (if i = 0 then y else Y ((i + 1) / 2)) := by
  rw [← prod_comp_ab E (fun i => if i = 0 then y else Y ((i + 1) / 2))]
  refine Finset.prod_le_prod' ?_
  intro q hq
  by_cases h : ab E q = 0
  · simp [h, hy q hq]
  · simp only [h, if_neg]
    exact le_cutoff_of_adm hA hq h

/-! ### Property (1): the explicit shrinking cutoffs and the level `y ^ s`

`Y j = y` for `j ≤ J = ⌊s/4⌋`, and `Y j = ⌊y ^ (α ^ (j - J))⌋` afterwards, with
`α = 1 - 1/(20k)`.  The first `2J+1` ranks cost at most one `log y` each and each later pair
costs at most `2 α ^ ℓ`, so the total exponent is at most `2J + 40k - 1 ≤ s` once `s ≥ 80k`. -/

/-- The shrinking factor `α = 1 - 1/(20k)`. -/
noncomputable def alph (k : ℕ) : ℝ := 1 - 1 / (20 * k)

/-- The number of full-length initial cutoffs, `J = ⌊s/4⌋`. -/
noncomputable def Jidx (s : ℝ) : ℕ := ⌊s / 4⌋₊

/-- The Brun cutoffs of the assessment. -/
noncomputable def brunCut (k : ℕ) (s : ℝ) (y : ℕ) : ℕ → ℕ :=
  fun j => if j ≤ Jidx s then y else ⌊(y : ℝ) ^ (alph k ^ (j - Jidx s))⌋₊

/-- The exponent (in units of `log y`) charged to the cutoff at position `j`. -/
noncomputable def expo (k : ℕ) (s : ℝ) : ℕ → ℝ :=
  fun j => if j ≤ Jidx s then 1 else alph k ^ (j - Jidx s)

/-- The exponent charged to rank `i` from the top. -/
noncomputable def expoI (k : ℕ) (s : ℝ) : ℕ → ℝ :=
  fun i => if i = 0 then 1 else expo k s ((i + 1) / 2)

lemma alph_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ alph k := by
  unfold alph
  have : (1 : ℝ) ≤ 20 * k := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  rw [sub_nonneg, div_le_one (by linarith)]
  linarith

lemma alph_lt_one {k : ℕ} (hk : 1 ≤ k) : alph k < 1 := by
  unfold alph
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have : 0 < 1 / (20 * (k : ℝ)) := by positivity
  linarith

lemma expo_nonneg {k : ℕ} (hk : 1 ≤ k) (s : ℝ) (j : ℕ) : 0 ≤ expo k s j := by
  unfold expo; split
  · norm_num
  · exact pow_nonneg (alph_nonneg hk) _

lemma expo_le_one {k : ℕ} (hk : 1 ≤ k) (s : ℝ) (j : ℕ) : expo k s j ≤ 1 := by
  unfold expo; split
  · exact le_refl 1
  · exact pow_le_one₀ (alph_nonneg hk) (alph_lt_one hk).le

lemma expoI_nonneg {k : ℕ} (hk : 1 ≤ k) (s : ℝ) (i : ℕ) : 0 ≤ expoI k s i := by
  unfold expoI; split
  · norm_num
  · exact expo_nonneg hk s _

lemma brunCut_le_rpow {k : ℕ} (hk : 1 ≤ k) (s : ℝ) {y : ℕ} (hy : 1 ≤ y) (j : ℕ) :
    ((brunCut k s y j : ℕ) : ℝ) ≤ (y : ℝ) ^ (expo k s j) := by
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  unfold brunCut expo
  split
  · rw [Real.rpow_one]
  · exact Nat.floor_le (Real.rpow_nonneg (by linarith) _)

/-- Turning a family of pointwise bounds `W i ≤ y ^ e i` into a bound on the product. -/
lemma prod_le_rpow_sum {y : ℕ} (hy : 1 ≤ y) (W : ℕ → ℕ) (e : ℕ → ℝ)
    (hW : ∀ i, (W i : ℝ) ≤ (y : ℝ) ^ (e i)) (r : ℕ) :
    ((∏ i ∈ Finset.range r, W i : ℕ) : ℝ) ≤ (y : ℝ) ^ (∑ i ∈ Finset.range r, e i) := by
  have hy0 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, Nat.cast_mul, Real.rpow_add hy0]
    refine mul_le_mul ih (hW n) (Nat.cast_nonneg _) (Real.rpow_nonneg hy0.le _)

/-- The rank exponents pair up: rank `2j-1` and rank `2j` both charge `expo j`. -/
lemma sum_expoI_odd (k : ℕ) (s : ℝ) (M : ℕ) :
    ∑ i ∈ Finset.range (2 * M + 1), expoI k s i
      = 1 + 2 * ∑ j ∈ Finset.Icc 1 M, expo k s j := by
  induction M with
  | zero => simp [expoI]
  | succ m ih =>
    have h1 : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by ring
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have e1 : expoI k s (2 * m + 1) = expo k s (m + 1) := by
      unfold expoI
      rw [if_neg (by omega)]
      congr 1
      omega
    have e2 : expoI k s (2 * m + 1 + 1) = expo k s (m + 1) := by
      unfold expoI
      rw [if_neg (by omega)]
      congr 1
      omega
    rw [e1, e2]
    ring

lemma geom_partial_le {a : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, a ^ i ≤ (1 - a)⁻¹ := by
  have hne : a ≠ 1 := ne_of_lt h1
  have hd : (0 : ℝ) < 1 - a := by linarith
  rw [geom_sum_eq hne]
  have hrw : (a ^ n - 1) / (a - 1) = (1 - a ^ n) / (1 - a) := by
    rw [← neg_sub a 1, ← neg_sub (a ^ n) 1, neg_div_neg_eq]
  rw [hrw, inv_eq_one_div]
  have hpn : 0 ≤ a ^ n := pow_nonneg h0 n
  gcongr
  linarith

/-- The cutoff exponents sum to at most `J + 20k - 1`: `J` full-length cutoffs and a geometric
tail `α/(1-α) = 20k - 1`. -/
lemma sum_expo_le {k : ℕ} (hk : 1 ≤ k) (s : ℝ) (M : ℕ) :
    ∑ j ∈ Finset.Icc 1 M, expo k s j ≤ (Jidx s : ℝ) + (20 * k - 1) := by
  set J := Jidx s with hJ
  set a := alph k with ha
  have h0 : 0 ≤ a := alph_nonneg hk
  have h1 : a < 1 := alph_lt_one hk
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hinv : a / (1 - a) = 20 * (k : ℝ) - 1 := by
    have h20 : (0 : ℝ) < 20 * (k : ℝ) := by linarith
    rw [ha]
    unfold alph
    field_simp
    ring
  -- extend `M` so that `J ≤ M`
  have hmono : ∑ j ∈ Finset.Icc 1 M, expo k s j ≤ ∑ j ∈ Finset.Icc 1 (max M J), expo k s j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => expo_nonneg hk s j)
    exact Finset.Icc_subset_Icc_right (le_max_left _ _)
  refine hmono.trans ?_
  set N := max M J with hN
  have hJN : J ≤ N := le_max_right _ _
  have hsplit : ∑ j ∈ Finset.Icc 1 N, expo k s j
      = (∑ j ∈ Finset.Ico 1 (J + 1), expo k s j) + ∑ j ∈ Finset.Ico (J + 1) (N + 1), expo k s j := by
    rw [Finset.sum_Ico_consecutive _ (by omega) (by omega)]
    congr 1
  have hfirst : ∑ j ∈ Finset.Ico 1 (J + 1), expo k s j = (J : ℝ) := by
    have : ∀ j ∈ Finset.Ico 1 (J + 1), expo k s j = 1 := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      unfold expo
      rw [if_pos (by omega)]
    rw [Finset.sum_congr rfl this]
    simp
  have hsecond : ∑ j ∈ Finset.Ico (J + 1) (N + 1), expo k s j ≤ a / (1 - a) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ i ∈ Finset.range (N + 1 - (J + 1)), expo k s (J + 1 + i) = a * a ^ i := by
      intro i _
      unfold expo
      rw [if_neg (by omega)]
      have : J + 1 + i - J = i + 1 := by omega
      rw [this, ← ha, pow_succ]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hd : (0 : ℝ) < 1 - a := by linarith
    calc a * ∑ i ∈ Finset.range (N + 1 - (J + 1)), a ^ i
        ≤ a * (1 - a)⁻¹ := by
          exact mul_le_mul_of_nonneg_left (geom_partial_le h0 h1 _) h0
      _ = a / (1 - a) := by rw [div_eq_mul_inv]
  rw [hinv] at hsecond
  rw [hsplit, hfirst]
  linarith

/-- **Property (1), support half.**  Every subset supported by the Brun weights has product at
most `y ^ s`, for `s ≥ 80k`.  No hypothesis beyond `1 ≤ k`, `1 ≤ y` and the elements being
`≤ y`. -/
theorem prod_le_rpow_of_adm {k : ℕ} (hk : 1 ≤ k) {s : ℝ} (hs : 80 * k ≤ s) {y : ℕ} (hy : 1 ≤ y)
    {E : Finset ℕ} (hA : Adm (brunCut k s y) E) (hyE : ∀ p ∈ E, p ≤ y) :
    ((∏ p ∈ E, p : ℕ) : ℝ) ≤ (y : ℝ) ^ s := by
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  set r := E.card with hr
  -- combinatorial half
  have hcomb : ((∏ p ∈ E, p : ℕ) : ℝ)
      ≤ ((∏ i ∈ Finset.range r, (if i = 0 then y else brunCut k s y ((i + 1) / 2)) : ℕ) : ℝ) := by
    exact_mod_cast prod_le_of_adm hA hyE
  -- pointwise exponent bound
  have hW : ∀ i, ((if i = 0 then y else brunCut k s y ((i + 1) / 2) : ℕ) : ℝ)
      ≤ (y : ℝ) ^ (expoI k s i) := by
    intro i
    unfold expoI
    by_cases h : i = 0
    · simp [h, Real.rpow_one]
    · rw [if_neg h, if_neg h]
      exact brunCut_le_rpow hk s hy _
  have hprod := prod_le_rpow_sum hy _ (expoI k s) hW r
  -- the exponent sum
  have hsub : ∑ i ∈ Finset.range r, expoI k s i ≤ ∑ i ∈ Finset.range (2 * r + 1), expoI k s i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => expoI_nonneg hk s i)
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hsum : ∑ i ∈ Finset.range (2 * r + 1), expoI k s i
      ≤ 1 + 2 * ((Jidx s : ℝ) + (20 * k - 1)) := by
    rw [sum_expoI_odd]
    have := sum_expo_le hk s r
    linarith
  have hJ : (Jidx s : ℝ) ≤ s / 4 := by
    have hs0 : (0 : ℝ) ≤ s := by
      have : (0 : ℝ) ≤ 80 * (k : ℝ) := by positivity
      linarith
    exact Nat.floor_le (by positivity)
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hfinal : ∑ i ∈ Finset.range r, expoI k s i ≤ s := by
    have h40 : 40 * (k : ℝ) ≤ s / 2 := by linarith
    linarith [hsub, hsum, hJ]
  calc ((∏ p ∈ E, p : ℕ) : ℝ)
      ≤ ((∏ i ∈ Finset.range r, (if i = 0 then y else brunCut k s y ((i + 1) / 2)) : ℕ) : ℝ) := hcomb
    _ ≤ (y : ℝ) ^ (∑ i ∈ Finset.range r, expoI k s i) := hprod
    _ ≤ (y : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le hy1 hfinal

/-- **Target property (1)**, both halves: the Brun coefficients are bounded by `1` in absolute
value and supported on divisors `≤ y ^ s`, for `s ≥ 80k`. -/
theorem brun_lower_one {k : ℕ} (hk : 1 ≤ k) {s : ℝ} (hs : 80 * k ≤ s) {y : ℕ} (hy : 1 ≤ y)
    {U : Finset ℕ} (hU : ∀ p ∈ U, p ≤ y) {E : Finset ℕ} (hEU : E ⊆ U) :
    |lam (brunCut k s y) E| ≤ 1 ∧
      (lam (brunCut k s y) E ≠ 0 → ((∏ p ∈ E, p : ℕ) : ℝ) ≤ (y : ℝ) ^ s) := by
  refine ⟨lam_abs_le_one _ _, fun hne => ?_⟩
  have hA : Adm (brunCut k s y) E := by
    by_contra h; exact hne (lam_eq_zero_of_not_adm h)
  exact prod_le_rpow_of_adm hk hs hy hA (fun p hp => hU p (hEU hp))

/-! ### Property (3): the relative error

The exact defect of `defect_eq` is grouped by the length `#F = 2m` of the first failed prefix.
A prefix of length `2m` fails only if its least element exceeds the cutoff `Y m`, which is
impossible for `m ≤ J`; so `m = J + ℓ` with `ℓ ≥ 1`, and all of `F` lies above
`t_ℓ = y ^ (α ^ ℓ)`.  Two estimates then finish it:

* the *elementary symmetric* bound `e_n(W) ≤ exp(x·∑_W g)/x^n` for every `x > 0` (a one-line
  consequence of `Finset.prod_add` and `1 + u ≤ exp u`), optimised at `x = n/T`; this replaces
  the factorial/Stirling step of the assessment entirely;
* the dimension hypothesis, which bounds both `∏_{p > t_ℓ}(1-g p)⁻¹` and `∑_{p > t_ℓ} g p`
  by `exp(A + Bℓ)` resp. `A + Bℓ`, with `A = log K ≤ J/10` and `B = -k log α ≤ 1/19`.

Since `A + Bℓ ≤ (J+ℓ)/10 = n/20`, each block is at most `V·(e^{1+1/20}/20)^n ≤ V·4^{-n}`. -/

/-- The elementary-symmetric bound.  No factorials: `x ^ n · e_n(W) ≤ ∏ (1 + x g) ≤ exp(x ∑ g)`. -/
lemma esymm_le_exp_div (W : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ p ∈ W, 0 ≤ g p) (n : ℕ) {x : ℝ}
    (hx : 0 < x) :
    ∑ E ∈ Finset.powersetCard n W, ∏ p ∈ E, g p
      ≤ Real.exp (x * ∑ p ∈ W, g p) / x ^ n := by
  have hxn : (0 : ℝ) < x ^ n := pow_pos hx n
  rw [le_div_iff₀ hxn]
  have hstep : (∑ E ∈ Finset.powersetCard n W, ∏ p ∈ E, g p) * x ^ n
      = ∑ E ∈ Finset.powersetCard n W, ∏ p ∈ E, (x * g p) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun E hE => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.1 hE).2]
    ring
  rw [hstep]
  have hsub : ∑ E ∈ Finset.powersetCard n W, ∏ p ∈ E, (x * g p)
      ≤ ∑ E ∈ W.powerset, ∏ p ∈ E, (x * g p) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun E hE => Finset.mem_powerset.2 (Finset.mem_powersetCard.1 hE).1) ?_
    intro E hE _
    exact Finset.prod_nonneg fun p hp =>
      mul_nonneg hx.le (hg p ((Finset.mem_powerset.1 hE) hp))
  refine hsub.trans ?_
  have hadd : ∑ E ∈ W.powerset, ∏ p ∈ E, (x * g p) = ∏ p ∈ W, (x * g p + 1) := by
    rw [Finset.prod_add]
    exact Finset.sum_congr rfl fun E _ => by simp
  rw [hadd]
  calc ∏ p ∈ W, (x * g p + 1) ≤ ∏ p ∈ W, Real.exp (x * g p) := by
        refine Finset.prod_le_prod (fun p hp => by have := hg p hp; positivity) ?_
        intro p _
        exact Real.add_one_le_exp _
    _ = Real.exp (x * ∑ p ∈ W, g p) := by
        rw [← Real.exp_sum, Finset.mul_sum]

/-- The optimised form: `e_n(W) ≤ (e·T/n)^n` whenever `∑_W g ≤ T` and `0 < T`. -/
lemma esymm_le_pow (W : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ p ∈ W, 0 ≤ g p) {n : ℕ} (hn : 0 < n)
    {T : ℝ} (hT : 0 < T) (hsum : ∑ p ∈ W, g p ≤ T) :
    ∑ E ∈ Finset.powersetCard n W, ∏ p ∈ E, g p ≤ (Real.exp 1 * T / n) ^ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) / T := by positivity
  refine (esymm_le_exp_div W g hg n hx).trans ?_
  have h1 : ((n : ℝ) / T) * ∑ p ∈ W, g p ≤ (n : ℝ) := by
    calc ((n : ℝ) / T) * ∑ p ∈ W, g p ≤ ((n : ℝ) / T) * T :=
          mul_le_mul_of_nonneg_left hsum hx.le
      _ = (n : ℝ) := by field_simp
  have h2 : Real.exp (((n : ℝ) / T) * ∑ p ∈ W, g p) ≤ Real.exp (n : ℝ) := Real.exp_le_exp.2 h1
  have hTne : T ≠ 0 := ne_of_gt hT
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have key : Real.exp (((n : ℝ) / T) * ∑ p ∈ W, g p) / ((n : ℝ) / T) ^ n
      ≤ Real.exp (n : ℝ) / ((n : ℝ) / T) ^ n := by
    have hpp := pow_pos hx n
    gcongr
  refine key.trans_eq ?_
  have e1 : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [e1, div_pow, mul_div_assoc, mul_pow, div_pow]
  field_simp

/-- The `ℓ`-th cutoff as a real number, `t_ℓ = y ^ (α ^ ℓ)`. -/
noncomputable def tcut (k : ℕ) (y : ℕ) (l : ℕ) : ℝ := (y : ℝ) ^ (alph k ^ l)

/-- The tail-product dimension hypothesis of the assessment. -/
def Dimension (U : Finset ℕ) (g : ℕ → ℝ) (y : ℕ) (K : ℝ) (k : ℕ) : Prop :=
  ∀ t : ℝ, 1 ≤ t → t ≤ (y : ℝ) →
    ∏ p ∈ U.filter (fun p : ℕ => t < (p : ℝ)), (1 - g p)⁻¹
      ≤ K * (Real.log y / Real.log (max 2 t)) ^ k

/-- `A = log K`. -/
noncomputable def Aconst (K : ℝ) : ℝ := Real.log K

/-- `B = -k log α`, the per-step loss of the shrinking cutoffs. -/
noncomputable def Bconst (k : ℕ) : ℝ := -(k : ℝ) * Real.log (alph k)

lemma alph_pos {k : ℕ} (hk : 1 ≤ k) : 0 < alph k := by
  unfold alph
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1 : 1 / (20 * (k : ℝ)) ≤ 1 / 20 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

lemma Bconst_pos {k : ℕ} (hk : 1 ≤ k) : 0 < Bconst k := by
  unfold Bconst
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog : Real.log (alph k) < 0 := Real.log_neg (alph_pos hk) (alph_lt_one hk)
  nlinarith

lemma Bconst_le {k : ℕ} (hk : 1 ≤ k) : Bconst k ≤ 1 / 19 := by
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hp := alph_pos hk
  have hinvpos : 0 < (alph k)⁻¹ := by positivity
  have hlog : Real.log ((alph k)⁻¹) ≤ (alph k)⁻¹ - 1 := Real.log_le_sub_one_of_pos hinvpos
  rw [Real.log_inv] at hlog
  have halph : alph k = 1 - 1 / (20 * (k : ℝ)) := rfl
  have h20 : (0 : ℝ) < 20 * (k : ℝ) := by linarith
  have hden : (0 : ℝ) < 20 * (k : ℝ) - 1 := by linarith
  have hval : (alph k)⁻¹ - 1 = 1 / (20 * (k : ℝ) - 1) := by
    rw [halph, show (1 : ℝ) - 1 / (20 * (k : ℝ)) = (20 * (k : ℝ) - 1) / (20 * (k : ℝ)) by
      field_simp, inv_div]
    field_simp
    ring
  rw [hval] at hlog
  unfold Bconst
  have hkey : -Real.log (alph k) ≤ 1 / (20 * (k : ℝ) - 1) := by linarith
  have hden : (0 : ℝ) < 20 * (k : ℝ) - 1 := by linarith
  have : -(k : ℝ) * Real.log (alph k) = (k : ℝ) * (-Real.log (alph k)) := by ring
  rw [this]
  have h2 : (k : ℝ) * (-Real.log (alph k)) ≤ (k : ℝ) * (1 / (20 * (k : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left hkey (by linarith)
  refine h2.trans ?_
  rw [mul_one_div, div_le_div_iff₀ hden (by norm_num)]
  linarith

/-- Consequence of the dimension hypothesis: the tail product above `t_ℓ`. -/
lemma dim_prod_le {U : Finset ℕ} {g : ℕ → ℝ} {y : ℕ} {K : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hK : 1 ≤ K) (hy : Real.exp 2 ≤ (y : ℝ)) (hdim : Dimension U g y K k) (l : ℕ) :
    ∏ p ∈ U.filter (fun p : ℕ => tcut k y l < (p : ℝ)), (1 - g p)⁻¹
      ≤ Real.exp (Aconst K + Bconst k * l) := by
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hlogy : (2 : ℝ) ≤ Real.log y := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) hy
  have hap : 0 < alph k := alph_pos hk
  have hal : alph k < 1 := alph_lt_one hk
  have hpow_pos : 0 < alph k ^ l := pow_pos hap l
  have hpow_le : alph k ^ l ≤ 1 := pow_le_one₀ hap.le hal.le
  set t := tcut k y l with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hy1 hpow_pos.le
  have hty : t ≤ (y : ℝ) := by
    calc t ≤ (y : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 hpow_le
      _ = (y : ℝ) := Real.rpow_one _
  have hlogt : Real.log t = alph k ^ l * Real.log y := Real.log_rpow hy0 _
  -- the key ratio bound
  have hkey : Real.log y / Real.log (max 2 t) ≤ (alph k ^ l)⁻¹ := by
    have hden : alph k ^ l * Real.log y ≤ Real.log (max 2 t) := by
      rcases le_or_gt 2 t with h2 | h2
      · rw [max_eq_right h2, hlogt]
      · rw [max_eq_left h2.le]
        have : Real.log t < Real.log 2 := Real.log_lt_log (by linarith) h2
        rw [hlogt] at this
        linarith
    have hpos : 0 < alph k ^ l * Real.log y := by positivity
    rw [div_le_iff₀ (by linarith)]
    rw [inv_mul_eq_div, le_div_iff₀ hpow_pos]
    nlinarith
  have hratio_nonneg : 0 ≤ Real.log y / Real.log (max 2 t) := by
    have h1 : 0 < Real.log (max 2 t) := by
      have : (1 : ℝ) < max 2 t := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      exact Real.log_pos this
    positivity
  refine (hdim t ht1 hty).trans ?_
  have hstep : (Real.log y / Real.log (max 2 t)) ^ k ≤ ((alph k ^ l)⁻¹) ^ k :=
    pow_le_pow_left₀ hratio_nonneg hkey k
  have hKpos : (0 : ℝ) < K := by linarith
  have h1 : K * (Real.log y / Real.log (max 2 t)) ^ k ≤ K * ((alph k ^ l)⁻¹) ^ k :=
    mul_le_mul_of_nonneg_left hstep (by linarith)
  refine h1.trans_eq ?_
  rw [Real.exp_add, Aconst, Real.exp_log hKpos]
  congr 1
  rw [inv_pow, ← pow_mul]
  have he : alph k ^ (l * k) = Real.exp (((l * k : ℕ) : ℝ) * Real.log (alph k)) := by
    rw [Real.exp_nat_mul, Real.exp_log hap]
  rw [he, ← Real.exp_neg]
  congr 1
  push_cast
  rw [Bconst]
  ring

/-- Consequence of the dimension hypothesis: the tail *sum* of local densities above `t_ℓ`,
via `1 - u ≤ exp (-u)`. -/
lemma dim_sum_le {U : Finset ℕ} {g : ℕ → ℝ} {y : ℕ} {K : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hK : 1 ≤ K) (hy : Real.exp 2 ≤ (y : ℝ)) (hg1 : ∀ p ∈ U, g p < 1)
    (hdim : Dimension U g y K k) (l : ℕ) :
    ∑ p ∈ U.filter (fun p : ℕ => tcut k y l < (p : ℝ)), g p ≤ Aconst K + Bconst k * l := by
  have h1 : Real.exp (∑ p ∈ U.filter (fun p : ℕ => tcut k y l < (p : ℝ)), g p)
      ≤ ∏ p ∈ U.filter (fun p : ℕ => tcut k y l < (p : ℝ)), (1 - g p)⁻¹ := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) ?_
    intro p hp
    have hp' : p ∈ U := (Finset.mem_filter.1 hp).1
    have hpos : 0 < 1 - g p := by have := hg1 p hp'; linarith
    have h1x : 1 - g p ≤ Real.exp (-(g p)) := by
      have := Real.add_one_le_exp (-(g p)); linarith
    have hE : Real.exp (-(g p)) * Real.exp (g p) = 1 := by
      rw [← Real.exp_add]; simp
    have hmul : (1 - g p) * Real.exp (g p) ≤ 1 := by
      nlinarith [Real.exp_pos (g p)]
    rw [inv_eq_one_div, le_div_iff₀ hpos]
    linarith
  exact Real.exp_le_exp.1 (h1.trans (dim_prod_le hk hK hy hdim l))

/-! ### Numeric anchors (kernel `decide`)

The controls of `papers/prime-model-sieve-assessment.md`: `U = {2,3,5,7}` with the even-position
cutoffs `Y 1 = 3`, `Y 2 = 2` and local densities `g p = 1/p`.  These pin the *semantics* of
`Adm`/`lam` against the hand computation; they are controls, never a substitute for the uniform
theorems above. -/

/-- The rational avatar of `lam`, so the anchors are decidable. -/
def lamQ (Y : ℕ → ℕ) (E : Finset ℕ) : ℚ := if Adm Y E then (-1) ^ E.card else 0

lemma lam_eq_lamQ (Y : ℕ → ℕ) (E : Finset ℕ) : lam Y E = (lamQ Y E : ℝ) := by
  unfold lam lamQ; split <;> push_cast <;> ring

/-- The anchor cutoffs: `Y 1 = 3`, `Y j = 2` otherwise. -/
def Yanchor : ℕ → ℕ := fun j => if j = 1 then 3 else 2

/-- Anchor: every supported subset of `{2,3,5,7}` has product at most `42`. -/
theorem anchor_support :
    ∀ E ∈ ({2, 3, 5, 7} : Finset ℕ).powerset, Adm Yanchor E → (∏ p ∈ E, p) ≤ 42 := by decide

/-- Anchor: the bound `42` is attained (so the support bound is sharp here). -/
theorem anchor_support_sharp :
    Adm Yanchor ({2, 3, 7} : Finset ℕ) ∧ (∏ p ∈ ({2, 3, 7} : Finset ℕ), p) = 42 := by decide

/-- Anchor: the true product `V = 8/35`. -/
theorem anchor_V : ∏ p ∈ ({2, 3, 5, 7} : Finset ℕ), (1 - 1 / (p : ℚ)) = 8 / 35 := by norm_num

/-- The integral avatar of `lam`; `Rat` division does not reduce in the kernel, so the numeric
anchor for the model sum is run through this integer-valued weight. -/
def lamZ (Y : ℕ → ℕ) (E : Finset ℕ) : ℤ := if Adm Y E then (-1) ^ E.card else 0

lemma lamQ_eq_lamZ (Y : ℕ → ℕ) (E : Finset ℕ) : lamQ Y E = (lamZ Y E : ℚ) := by
  unfold lamQ lamZ; split <;> push_cast <;> ring

/-- Clearing denominators in a squarefree model sum: if `(∏ E) * c E = M` for every subset,
the sum of `w E * ∏_{p ∈ E} p⁻¹` is `(∑ w E * c E) / M`. -/
lemma sum_inv_prod_eq (U : Finset ℕ) (w : Finset ℕ → ℚ) (M : ℕ) (hM : M ≠ 0)
    (c : Finset ℕ → ℕ) (hc : ∀ E ∈ U.powerset, (∏ p ∈ E, p) * c E = M) :
    ∑ E ∈ U.powerset, w E * ∏ p ∈ E, (1 / (p : ℚ))
      = (∑ E ∈ U.powerset, w E * (c E : ℚ)) / (M : ℚ) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun E hE => ?_
  have hcast : ((∏ p ∈ E, p : ℕ) : ℚ) * (c E : ℚ) = (M : ℚ) := by exact_mod_cast hc E hE
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hP : ((∏ p ∈ E, p : ℕ) : ℚ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hcast; exact hM' hcast.symm
  have hcE : (c E : ℚ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hcast; exact hM' hcast.symm
  have key : ∏ p ∈ E, (1 / (p : ℚ)) = ((∏ p ∈ E, p : ℕ) : ℚ)⁻¹ := by
    rw [Nat.cast_prod]
    simp [one_div, Finset.prod_inv_distrib]
  have h2 : ((∏ p ∈ E, p : ℕ) : ℚ)⁻¹ = (c E : ℚ) / (M : ℚ) := by
    rw [← hcast]; field_simp
  rw [key, h2, mul_div_assoc]

/-- Anchor: the cleared-denominator model sum over `{2,3,5,7}` is `46 = 210 · 23/105`. -/
theorem anchor_model_sum_int :
    ∑ E ∈ ({2, 3, 5, 7} : Finset ℕ).powerset, lamZ Yanchor E * (210 / (∏ p ∈ E, p) : ℕ) = 46 := by
  decide

/-- Anchor: the Brun lower model sum is `23/105`, i.e. the model defect is `1/105` and the
relative defect `1/24` against `V = 8/35`. -/
theorem anchor_model_sum :
    ∑ E ∈ ({2, 3, 5, 7} : Finset ℕ).powerset, lamQ Yanchor E * ∏ p ∈ E, (1 / (p : ℚ))
      = 23 / 105 := by
  have hc : ∀ E ∈ ({2, 3, 5, 7} : Finset ℕ).powerset,
      (∏ p ∈ E, p) * (210 / (∏ p ∈ E, p)) = 210 := by decide
  rw [sum_inv_prod_eq _ _ 210 (by norm_num) _ hc]
  have hterm : ∀ E : Finset ℕ, lamQ Yanchor E * ((210 / (∏ p ∈ E, p) : ℕ) : ℚ)
      = ((lamZ Yanchor E * ((210 / (∏ p ∈ E, p) : ℕ) : ℤ) : ℤ) : ℚ) := by
    intro E; rw [lamQ_eq_lamZ, Int.cast_mul, Int.cast_natCast]
  rw [Finset.sum_congr rfl (fun E _ => hterm E), ← Int.cast_sum, anchor_model_sum_int]
  norm_num

end NormalNumbers.PrimeModel.Brun
