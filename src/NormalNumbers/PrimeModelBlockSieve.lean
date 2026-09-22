import Mathlib

/-!
# Lemma B, part 1: the block-Bonferroni pair and the telescoping minorant

Lap 1 of `KICKOFF-2026-09-22-multicutoff-lean.md`; spec `papers/ROUND2-multicutoff-fable.md` §3
(Astra §4).  This file is **pure combinatorics**: no primes, no arithmetic.

* `bonfPartial b r = ∑_{i ≤ r} (−1)^i C(b,i)`; the Bonferroni pair identity
  `bonfPartial (b+1) r = (−1)^r C(b, r)` (`bonfPartial_succ`), whence for even `r`
  - `bonfIndic b ≤ bonfPartial b r` (`U ≥ I`), and
  - `bonfPartial b r − C(b, r+1) ≤ bonfIndic b` (`U − D ≤ I`),
  where `bonfIndic b = [b = 0]`.
* `prod_sub_prod_le` — the telescoping minorant
  `∏ U − ∏ I ≤ ∑_i (U i − I i) ∏_{j ≠ i} U j`, valid for `0 ≤ I ≤ U`.  This is the step that
  replaces the (invalid) "product of lower sieves": multiplying two lower minorants can produce
  `(−1)(−1) = +1 > [B = ∅]`.
* `prod_le_prod_of_defect` — the packaged form `∏ U − ∑_i D i ∏_{j≠i} U j ≤ ∏ I`.
-/

open Finset

namespace NormalNumbers.PrimeModel.BlockSieve

/-! ### The Bonferroni pair -/

/-- `U_r(b) = ∑_{i ≤ r} (−1)^i C(b,i)`, the `r`-th Bonferroni partial sum. -/
def bonfPartial (b r : ℕ) : ℤ := ∑ i ∈ Finset.range (r + 1), (-1) ^ i * (b.choose i : ℤ)

/-- `I(b) = [b = 0]`, the exact indicator the sieve is minorising. -/
def bonfIndic (b : ℕ) : ℤ := if b = 0 then 1 else 0

@[simp] theorem bonfPartial_zero (r : ℕ) : bonfPartial 0 r = 1 := by
  unfold bonfPartial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hi)]
  · intro h; simp at h

/-- **Bonferroni pair identity**: `∑_{i ≤ r} (−1)^i C(b+1,i) = (−1)^r C(b,r)`. -/
theorem bonfPartial_succ (b r : ℕ) : bonfPartial (b + 1) r = (-1) ^ r * (b.choose r : ℤ) := by
  induction r with
  | zero => simp [bonfPartial]
  | succ r ih =>
      unfold bonfPartial at ih ⊢
      rw [Finset.sum_range_succ, ih]
      have hp : ((b + 1).choose (r + 1) : ℤ) = (b.choose r : ℤ) + (b.choose (r + 1) : ℤ) := by
        rw [Nat.choose_succ_succ]; push_cast; ring
      rw [hp]
      ring

/-- `U ≥ I`: the even-order Bonferroni partial sum is an upper bound for the indicator. -/
theorem bonfIndic_le_bonfPartial (b : ℕ) {r : ℕ} (hr : Even r) :
    bonfIndic b ≤ bonfPartial b r := by
  cases b with
  | zero => simp [bonfIndic]
  | succ b =>
      rw [bonfPartial_succ, hr.neg_one_pow, one_mul, bonfIndic, if_neg (by omega)]
      positivity

/-- `0 ≤ I`. -/
@[simp] theorem bonfIndic_nonneg (b : ℕ) : 0 ≤ bonfIndic b := by
  unfold bonfIndic; split <;> norm_num

/-- `U − D ≤ I` with the defect `D = C(b, r+1)`. -/
theorem bonfPartial_sub_le (b : ℕ) {r : ℕ} (hr : Even r) :
    bonfPartial b r - (b.choose (r + 1) : ℤ) ≤ bonfIndic b := by
  cases b with
  | zero => simp [bonfIndic, Nat.choose_eq_zero_of_lt (Nat.succ_pos r)]
  | succ b =>
      rw [bonfPartial_succ, hr.neg_one_pow, one_mul, bonfIndic, if_neg (by omega)]
      have hp : ((b + 1).choose (r + 1) : ℤ) = (b.choose r : ℤ) + (b.choose (r + 1) : ℤ) := by
        rw [Nat.choose_succ_succ]; push_cast; ring
      rw [hp]
      have : (0:ℤ) ≤ (b.choose (r + 1) : ℤ) := by positivity
      linarith

/-! ### The telescoping minorant -/

variable {ι : Type*} [DecidableEq ι]
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Telescoping**: `∏ U − ∏ I ≤ ∑_i (U i − I i) ∏_{j ≠ i} U j` when `0 ≤ I i ≤ U i`.
This replaces the invalid "product of lower sieves". -/
theorem prod_sub_prod_le (s : Finset ι) (U I : ι → R)
    (hI : ∀ i ∈ s, 0 ≤ I i) (hIU : ∀ i ∈ s, I i ≤ U i) :
    (∏ i ∈ s, U i) - (∏ i ∈ s, I i) ≤ ∑ i ∈ s, (U i - I i) * ∏ j ∈ s.erase i, U j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hIa : 0 ≤ I a := hI a (mem_insert_self a s)
      have hIUa : I a ≤ U a := hIU a (mem_insert_self a s)
      have hI' : ∀ i ∈ s, 0 ≤ I i := fun i hi => hI i (mem_insert_of_mem hi)
      have hIU' : ∀ i ∈ s, I i ≤ U i := fun i hi => hIU i (mem_insert_of_mem hi)
      have hUnn : ∀ i ∈ s, 0 ≤ U i := fun i hi => (hI' i hi).trans (hIU' i hi)
      have hYnn : 0 ≤ ∑ i ∈ s, (U i - I i) * ∏ j ∈ s.erase i, U j := by
        refine Finset.sum_nonneg fun i hi => ?_
        have h1 : 0 ≤ U i - I i := by linarith [hIU' i hi]
        have h2 : 0 ≤ ∏ j ∈ s.erase i, U j :=
          Finset.prod_nonneg fun j hj => hUnn j (Finset.mem_of_mem_erase hj)
        exact mul_nonneg h1 h2
      have key := ih hI' hIU'
      -- rewrite both sides over `insert a s`
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have herase_a : (insert a s).erase a = s := Finset.erase_insert ha
      have hterms : ∀ i ∈ s, (U i - I i) * ∏ j ∈ (insert a s).erase i, U j
          = U a * ((U i - I i) * ∏ j ∈ s.erase i, U j) := by
        intro i hi
        have hne : i ≠ a := fun h => ha (h ▸ hi)
        have : (insert a s).erase i = insert a (s.erase i) := by
          ext x
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨hx, hx2 | hx2⟩ <;> tauto
          · rintro (rfl | hx) <;> [exact ⟨hne.symm, Or.inl rfl⟩; exact ⟨hx.1, Or.inr hx.2⟩]
        rw [this, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
        ring
      rw [Finset.sum_congr rfl hterms, ← Finset.mul_sum, herase_a]
      have hsplit : U a * ∏ i ∈ s, U i - I a * ∏ i ∈ s, I i
          = (U a - I a) * ∏ i ∈ s, U i + I a * ((∏ i ∈ s, U i) - ∏ i ∈ s, I i) := by ring
      rw [hsplit]
      have h1 : I a * ((∏ i ∈ s, U i) - ∏ i ∈ s, I i)
          ≤ U a * ∑ i ∈ s, (U i - I i) * ∏ j ∈ s.erase i, U j := by
        calc I a * ((∏ i ∈ s, U i) - ∏ i ∈ s, I i)
            ≤ I a * ∑ i ∈ s, (U i - I i) * ∏ j ∈ s.erase i, U j :=
              mul_le_mul_of_nonneg_left key hIa
          _ ≤ U a * ∑ i ∈ s, (U i - I i) * ∏ j ∈ s.erase i, U j :=
              mul_le_mul_of_nonneg_right hIUa hYnn
      linarith

/-- The packaged minorant: with defects `D i ≥ U i − I i`, `∏ U − ∑ D_i ∏_{j≠i} U_j ≤ ∏ I`. -/
theorem prod_le_prod_of_defect (s : Finset ι) (U I D : ι → R)
    (hI : ∀ i ∈ s, 0 ≤ I i) (hIU : ∀ i ∈ s, I i ≤ U i)
    (hD : ∀ i ∈ s, U i - I i ≤ D i) :
    (∏ i ∈ s, U i) - ∑ i ∈ s, D i * ∏ j ∈ s.erase i, U j ≤ ∏ i ∈ s, I i := by
  classical
  have hUnn : ∀ i ∈ s, 0 ≤ U i := fun i hi => (hI i hi).trans (hIU i hi)
  have hmono : ∑ i ∈ s, (U i - I i) * ∏ j ∈ s.erase i, U j
      ≤ ∑ i ∈ s, D i * ∏ j ∈ s.erase i, U j := by
    refine Finset.sum_le_sum fun i hi => ?_
    exact mul_le_mul_of_nonneg_right (hD i hi)
      (Finset.prod_nonneg fun j hj => hUnn j (Finset.mem_of_mem_erase hj))
  have := prod_sub_prod_le s U I hI hIU
  linarith


/-! ### The polynomial form: subset sums of a 0/1 weight -/

variable {α : Type*} [DecidableEq α]

/-- The number of `p ∈ B` that are "hit" (`x p = 1`). -/
def hitCount (x : α → ℤ) (B : Finset α) : ℕ := (B.filter (fun p => x p = 1)).card

/-- For a `0/1`-valued weight, the elementary symmetric sum of degree `i` over `B` counts the
`i`-subsets of the hit set: `∑_{E ⊆ B, |E| = i} ∏_{p ∈ E} x p = C(b, i)`. -/
theorem sum_powersetCard_prod (x : α → ℤ) (hx : ∀ p, x p = 0 ∨ x p = 1) (B : Finset α) (i : ℕ) :
    ∑ E ∈ B.powersetCard i, ∏ p ∈ E, x p = ((hitCount x B).choose i : ℤ) := by
  classical
  set S : Finset α := B.filter (fun p => x p = 1) with hS
  have hterm : ∀ E ∈ B.powersetCard i, (∏ p ∈ E, x p) = if E ⊆ S then 1 else 0 := by
    intro E hE
    rw [Finset.mem_powersetCard] at hE
    by_cases hsub : E ⊆ S
    · rw [if_pos hsub]
      refine Finset.prod_eq_one fun p hp => ?_
      have := hsub hp
      rw [hS, Finset.mem_filter] at this
      exact this.2
    · rw [if_neg hsub]
      obtain ⟨p, hpE, hpS⟩ := Finset.not_subset.1 hsub
      refine Finset.prod_eq_zero hpE ?_
      rcases hx p with h | h
      · exact h
      · exact absurd (by rw [hS, Finset.mem_filter]; exact ⟨hE.1 hpE, h⟩) hpS
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  have hfil : (B.powersetCard i).filter (fun E => E ⊆ S) = S.powersetCard i := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hcard⟩, hsub⟩; exact ⟨hsub, hcard⟩
    · rintro ⟨hsub, hcard⟩
      exact ⟨⟨hsub.trans (Finset.filter_subset _ _), hcard⟩, hsub⟩
  rw [hfil, Finset.card_powersetCard]
  rfl

/-- The `r`-th Bonferroni partial sum in polynomial form. -/
def bonfPoly (x : α → ℤ) (B : Finset α) (r : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (r + 1), (-1) ^ i * ∑ E ∈ B.powersetCard i, ∏ p ∈ E, x p

/-- The defect in polynomial form. -/
def defectPoly (x : α → ℤ) (B : Finset α) (r : ℕ) : ℤ :=
  ∑ E ∈ B.powersetCard (r + 1), ∏ p ∈ E, x p

theorem bonfPoly_eq (x : α → ℤ) (hx : ∀ p, x p = 0 ∨ x p = 1) (B : Finset α) (r : ℕ) :
    bonfPoly x B r = bonfPartial (hitCount x B) r := by
  unfold bonfPoly bonfPartial
  exact Finset.sum_congr rfl fun i _ => by rw [sum_powersetCard_prod x hx B i]

theorem defectPoly_eq (x : α → ℤ) (hx : ∀ p, x p = 0 ∨ x p = 1) (B : Finset α) (r : ℕ) :
    defectPoly x B r = ((hitCount x B).choose (r + 1) : ℤ) :=
  sum_powersetCard_prod x hx B (r + 1)

/-- **Lemma B, property 2 (pointwise)**: the graded block minorant never exceeds the exact
indicator that no block is hit. -/
theorem blockMinorant_le (s : Finset ι) (B : ι → Finset α) (r : ι → ℕ)
    (hr : ∀ i ∈ s, Even (r i)) (x : α → ℤ) (hx : ∀ p, x p = 0 ∨ x p = 1) :
    (∏ i ∈ s, bonfPoly x (B i) (r i))
        - ∑ i ∈ s, defectPoly x (B i) (r i) * ∏ j ∈ s.erase i, bonfPoly x (B j) (r j)
      ≤ ∏ i ∈ s, bonfIndic (hitCount x (B i)) := by
  classical
  have hU : ∀ i, bonfPoly x (B i) (r i) = bonfPartial (hitCount x (B i)) (r i) :=
    fun i => bonfPoly_eq x hx (B i) (r i)
  have hD : ∀ i, defectPoly x (B i) (r i) = ((hitCount x (B i)).choose (r i + 1) : ℤ) :=
    fun i => defectPoly_eq x hx (B i) (r i)
  simp only [hU, hD]
  refine prod_le_prod_of_defect s _ _ _ (fun i _ => bonfIndic_nonneg _)
    (fun i hi => bonfIndic_le_bonfPartial _ (hr i hi)) (fun i hi => ?_)
  have := bonfPartial_sub_le (hitCount x (B i)) (hr i hi)
  linarith


/-! ### Expansion over disjoint blocks: the coefficient rule -/

/-- Splitting a powerset sum across a disjoint union of two finsets. -/
theorem sum_powerset_union_disjoint {S T : Finset α} (h : Disjoint S T)
    (g : Finset α → Finset α → R) :
    ∑ E ∈ (S ∪ T).powerset, g (E ∩ S) (E ∩ T)
      = ∑ A ∈ S.powerset, ∑ F ∈ T.powerset, g A F := by
  classical
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun E => (E ∩ S, E ∩ T)) (fun q => q.1 ∪ q.2) ?_ ?_ ?_ ?_ ?_
  · intro E hE
    simp only [Finset.mem_product, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro q hq
    simp only [Finset.mem_product, Finset.mem_powerset] at hq
    simp only [Finset.mem_powerset]
    exact Finset.union_subset (hq.1.trans Finset.subset_union_left)
      (hq.2.trans Finset.subset_union_right)
  · intro E hE
    simp only [Finset.mem_powerset] at hE
    ext p
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      rcases Finset.mem_union.1 (hE hp) with hq | hq
      · exact Or.inl ⟨hp, hq⟩
      · exact Or.inr ⟨hp, hq⟩
  · intro q hq
    simp only [Finset.mem_product, Finset.mem_powerset] at hq
    have h1 : (q.1 ∪ q.2) ∩ S = q.1 := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hp1 | hp2, hpS⟩
        · exact hp1
        · exact absurd hpS (Finset.disjoint_right.1 h (hq.2 hp2))
      · intro hp; exact ⟨Or.inl hp, hq.1 hp⟩
    have h2 : (q.1 ∪ q.2) ∩ T = q.2 := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hp1 | hp2, hpT⟩
        · exact absurd hpT (Finset.disjoint_left.1 h (hq.1 hp1))
        · exact hp2
      · intro hp; exact ⟨Or.inr hp, hq.2 hp⟩
    rw [Prod.ext_iff]
    exact ⟨h1, h2⟩
  · intro E _; rfl

/-- **The coefficient rule.**  With pairwise disjoint blocks, a product of block-local signed
subset sums is itself a signed subset sum over the union, whose coefficient at `E` is the
product of the block coefficients at the traces `E ∩ B i`.  In particular, if every block
coefficient lies in `{−1, 0, 1}` then so does the resulting coefficient. -/
theorem prod_sum_powerset_disjoint (x : α → R) :
    ∀ (s : Finset ι) (B : ι → Finset α),
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j)) →
      ∀ c : ι → Finset α → R,
      (∏ i ∈ s, ∑ E ∈ (B i).powerset, c i E * ∏ p ∈ E, x p)
        = ∑ E ∈ (s.biUnion B).powerset, (∏ i ∈ s, c i (E ∩ B i)) * ∏ p ∈ E, x p := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => intro B _ c; simp
  | insert a s ha ih =>
      intro B hdisj c
      have hdisj' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j) :=
        fun i hi j hj hij => hdisj i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij
      have hdW : Disjoint (B a) (s.biUnion B) := by
        rw [Finset.disjoint_biUnion_right]
        intro i hi
        exact hdisj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi))
      set W : Finset α := s.biUnion B with hW
      set g : Finset α → Finset α → R :=
        fun A F => (∏ i ∈ insert a s, c i ((A ∪ F) ∩ B i)) * ∏ p ∈ A ∪ F, x p with hg
      rw [Finset.prod_insert ha, ih B hdisj' c, Finset.biUnion_insert, ← hW]
      have hR : (∑ E ∈ (B a ∪ W).powerset, (∏ i ∈ insert a s, c i (E ∩ B i)) * ∏ p ∈ E, x p)
          = ∑ A ∈ (B a).powerset, ∑ F ∈ W.powerset, g A F := by
        rw [← sum_powerset_union_disjoint hdW g]
        refine Finset.sum_congr rfl fun E hE => ?_
        rw [Finset.mem_powerset] at hE
        have hEsplit : E ∩ B a ∪ E ∩ W = E := by
          ext p
          simp only [Finset.mem_union, Finset.mem_inter]
          constructor
          · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
          · intro hp
            rcases Finset.mem_union.1 (hE hp) with hq | hq
            · exact Or.inl ⟨hp, hq⟩
            · exact Or.inr ⟨hp, hq⟩
        rw [hg]
        simp only [hEsplit]
      rw [hR, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun A hA => Finset.sum_congr rfl fun F hF => ?_
      rw [Finset.mem_powerset] at hA hF
      have hAF : Disjoint A F := Finset.disjoint_of_subset_left hA
        (Finset.disjoint_of_subset_right hF hdW)
      have hAa : (A ∪ F) ∩ B a = A := by
        ext p
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hp1 | hp2, hpS⟩
          · exact hp1
          · exact absurd hpS (Finset.disjoint_right.1 hdW (hF hp2))
        · intro hp; exact ⟨Or.inl hp, hA hp⟩
      have hAi : ∀ i ∈ s, (A ∪ F) ∩ B i = F ∩ B i := by
        intro i hi
        ext p
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hp1 | hp2, hpB⟩
          · exact absurd hpB (Finset.disjoint_left.1
              (hdisj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
                (fun h => ha (h ▸ hi))) (hA hp1))
          · exact ⟨hp2, hpB⟩
        · intro hp; exact ⟨Or.inr hp.1, hp.2⟩
      rw [hg]
      simp only
      rw [Finset.prod_insert ha, hAa,
        Finset.prod_congr rfl (fun i hi => by rw [hAi i hi] :
          ∀ i ∈ s, c i ((A ∪ F) ∩ B i) = c i (F ∩ B i)),
        Finset.prod_union hAF]
      ring

end NormalNumbers.PrimeModel.BlockSieve
