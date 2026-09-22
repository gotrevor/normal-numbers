import NormalNumbers.PrimeModelBlockLevel

/-!
# Lemma B assembled: the explicit graded sieve weights

Lap 4c of `KICKOFF-2026-09-22-multicutoff-lean.md`.  Laps 1–3 proved the three properties of the
graded block minorant separately; this file builds the **explicit weight function**

    λ(E) = ∏_i c_i(E ∩ B_i)  −  ∑_{i₀} c'_{i₀}(E ∩ B_{i₀}) ∏_{i ≠ i₀} c_i(E ∩ B_i)

(`blockLam`), where `c_i(F) = (−1)^{|F|} [|F| ≤ r_i]` and `c'_i(F) = [|F| = r_i + 1]`, and proves
that it satisfies exactly the interface `PrimeModelBrunCountGraded.graded_sifted_count_lower`
asks for:

* `blockLam_expand` — `∑_{E ⊆ U} λ(E) ∏_{p∈E} x_p = ∏_i U_i − ∑_i D_i ∏_{j≠i} U_j`;
* `blockLam_minorant` — `∑_{E ⊆ B} λ(E) ≤ [B = ∅]` for every `B ⊆ U`;
* `blockLam_abs_le_one` — `|λ(E)| ≤ 1` (disjoint supports);
* `blockLam_support` — `λ(E) ≠ 0 → |E ∩ B_i| ≤ r_i + 1` for every `i`.
-/

open Finset

namespace NormalNumbers.PrimeModel.BlockSieve

variable {ι : Type*} [DecidableEq ι] {α : Type*} [DecidableEq α]

/-- The Bonferroni coefficient of a trace: `(−1)^{|F|}` while `|F| ≤ r`, else `0`. -/
def coefU (r : ℕ) (F : Finset α) : ℤ := if F.card ≤ r then (-1) ^ F.card else 0

/-- The defect coefficient of a trace: `1` exactly at `|F| = r + 1`. -/
def coefD (r : ℕ) (F : Finset α) : ℤ := if F.card = r + 1 then 1 else 0

@[simp] theorem coefU_abs_le (r : ℕ) (F : Finset α) : |coefU r F| ≤ 1 := by
  unfold coefU
  split
  · rw [abs_pow, abs_neg, abs_one, one_pow]
  · norm_num

@[simp] theorem coefD_abs_le (r : ℕ) (F : Finset α) : |coefD r F| ≤ 1 := by
  unfold coefD; split <;> norm_num

/-! ### The powerset form of the block polynomials -/

theorem sum_powerset_coefU (x : α → ℤ) (B : Finset α) (r : ℕ) :
    ∑ E ∈ B.powerset, coefU r E * ∏ p ∈ E, x p = bonfPoly x B r := by
  classical
  have hzero : ∀ E ∈ B.powerset, ¬ (E.card ≤ r) → coefU r E * ∏ p ∈ E, x p = 0 := by
    intro E _ hE
    rw [coefU, if_neg hE, zero_mul]
  rw [← Finset.sum_filter_of_ne (fun E hE h => by
    by_contra hc
    exact h (hzero E hE hc))]
  have hset : B.powerset.filter (fun E => E.card ≤ r)
      = (Finset.range (r + 1)).biUnion (fun i => B.powersetCard i) := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hEB, hcard⟩
      exact ⟨E.card, by omega, hEB, rfl⟩
    · rintro ⟨i, hi, hEB, rfl⟩
      exact ⟨hEB, by omega⟩
  rw [hset, Finset.sum_biUnion]
  · unfold bonfPoly
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun E hE => ?_
    rw [Finset.mem_powersetCard] at hE
    rw [coefU, if_pos (by omega : E.card ≤ r), hE.2]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro E hEi hEj
    rw [Finset.mem_powersetCard] at hEi hEj
    exact hij (hEi.2 ▸ hEj.2 ▸ rfl)

theorem sum_powerset_coefD (x : α → ℤ) (B : Finset α) (r : ℕ) :
    ∑ E ∈ B.powerset, coefD r E * ∏ p ∈ E, x p = defectPoly x B r := by
  classical
  have hzero : ∀ E ∈ B.powerset, ¬ (E.card = r + 1) → coefD r E * ∏ p ∈ E, x p = 0 := by
    intro E _ hE
    rw [coefD, if_neg hE, zero_mul]
  rw [← Finset.sum_filter_of_ne (fun E hE h => by
    by_contra hc
    exact h (hzero E hE hc))]
  have hset : B.powerset.filter (fun E => E.card = r + 1) = B.powersetCard (r + 1) := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
  rw [hset]
  unfold defectPoly
  refine Finset.sum_congr rfl fun E hE => ?_
  rw [Finset.mem_powersetCard] at hE
  rw [coefD, if_pos hE.2, one_mul]

/-! ### The weight function -/

/-- The block coefficient family of the main term. -/
def lamMain (s : Finset ι) (B : ι → Finset α) (r : ι → ℕ) (E : Finset α) : ℤ :=
  ∏ i ∈ s, coefU (r i) (E ∩ B i)

/-- The block coefficient family of the `i₀`-th defect term. -/
def lamDef (s : Finset ι) (B : ι → Finset α) (r : ι → ℕ) (i₀ : ι) (E : Finset α) : ℤ :=
  coefD (r i₀) (E ∩ B i₀) * ∏ i ∈ s.erase i₀, coefU (r i) (E ∩ B i)

/-- **The graded sieve weight**. -/
def blockLam (s : Finset ι) (B : ι → Finset α) (r : ι → ℕ) (E : Finset α) : ℤ :=
  lamMain s B r E - ∑ i₀ ∈ s, lamDef s B r i₀ E

/-! ### Property 1: the expansion -/

theorem blockLam_expand (s : Finset ι) (B : ι → Finset α) (r : ι → ℕ)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j)) (x : α → ℤ) :
    ∑ E ∈ (s.biUnion B).powerset, blockLam s B r E * ∏ p ∈ E, x p
      = (∏ i ∈ s, bonfPoly x (B i) (r i))
        - ∑ i₀ ∈ s, defectPoly x (B i₀) (r i₀) * ∏ i ∈ s.erase i₀, bonfPoly x (B i) (r i) := by
  classical
  have hmain : ∑ E ∈ (s.biUnion B).powerset, lamMain s B r E * ∏ p ∈ E, x p
      = ∏ i ∈ s, bonfPoly x (B i) (r i) := by
    have h1 := prod_sum_powerset_disjoint x s B hdisj (fun i F => coefU (r i) F)
    rw [Finset.prod_congr rfl (fun i _ => sum_powerset_coefU x (B i) (r i))] at h1
    exact h1.symm
  have hdef : ∀ i₀ ∈ s, ∑ E ∈ (s.biUnion B).powerset, lamDef s B r i₀ E * ∏ p ∈ E, x p
      = defectPoly x (B i₀) (r i₀) * ∏ i ∈ s.erase i₀, bonfPoly x (B i) (r i) := by
    intro i₀ hi₀
    set c : ι → Finset α → ℤ :=
      fun i F => if i = i₀ then coefD (r i) F else coefU (r i) F with hc
    have h1 := prod_sum_powerset_disjoint x s B hdisj c
    have hLHS : (∏ i ∈ s, ∑ E ∈ (B i).powerset, c i E * ∏ p ∈ E, x p)
        = defectPoly x (B i₀) (r i₀) * ∏ i ∈ s.erase i₀, bonfPoly x (B i) (r i) := by
      rw [← Finset.mul_prod_erase s _ hi₀]
      congr 1
      · rw [hc]; simp only [if_pos rfl]; exact sum_powerset_coefD x (B i₀) (r i₀)
      · refine Finset.prod_congr rfl fun i hi => ?_
        have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
        rw [hc]; simp only [if_neg hne]; exact sum_powerset_coefU x (B i) (r i)
    have hcoef : ∀ E : Finset α, (∏ i ∈ s, c i (E ∩ B i)) = lamDef s B r i₀ E := by
      intro E
      rw [← Finset.mul_prod_erase s _ hi₀, lamDef, hc]
      simp only [if_pos rfl]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
      simp only [if_neg hne]
    calc ∑ E ∈ (s.biUnion B).powerset, lamDef s B r i₀ E * ∏ p ∈ E, x p
        = ∑ E ∈ (s.biUnion B).powerset, (∏ i ∈ s, c i (E ∩ B i)) * ∏ p ∈ E, x p :=
          Finset.sum_congr rfl fun E _ => by rw [hcoef E]
      _ = defectPoly x (B i₀) (r i₀) * ∏ i ∈ s.erase i₀, bonfPoly x (B i) (r i) := by
          rw [← h1, hLHS]
  have hsplit : ∀ E : Finset α, blockLam s B r E * ∏ p ∈ E, x p
      = lamMain s B r E * ∏ p ∈ E, x p
        - ∑ i₀ ∈ s, lamDef s B r i₀ E * ∏ p ∈ E, x p := by
    intro E
    rw [blockLam, sub_mul, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun E _ => hsplit E), Finset.sum_sub_distrib, hmain,
    Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl hdef


/-! ### Property 2: `|λ| ≤ 1` by disjoint supports -/

theorem lamMain_eq_zero_of {s : Finset ι} {B : ι → Finset α} {r : ι → ℕ} {E : Finset α}
    {i : ι} (hi : i ∈ s) (hcard : ¬ (E ∩ B i).card ≤ r i) : lamMain s B r E = 0 :=
  Finset.prod_eq_zero hi (by rw [coefU, if_neg hcard])

theorem lamDef_eq_zero_of {s : Finset ι} {B : ι → Finset α} {r : ι → ℕ} {E : Finset α}
    {i₀ i : ι} (hi : i ∈ s.erase i₀) (hcard : ¬ (E ∩ B i).card ≤ r i) :
    lamDef s B r i₀ E = 0 := by
  rw [lamDef, Finset.prod_eq_zero hi (by rw [coefU, if_neg hcard]), mul_zero]

theorem lamDef_eq_zero_of_card_ne {s : Finset ι} {B : ι → Finset α} {r : ι → ℕ} {E : Finset α}
    {i₀ : ι} (hcard : (E ∩ B i₀).card ≠ r i₀ + 1) : lamDef s B r i₀ E = 0 := by
  rw [lamDef, coefD, if_neg hcard, zero_mul]

theorem abs_lamMain_le_one (s : Finset ι) (B : ι → Finset α) (r : ι → ℕ) (E : Finset α) :
    |lamMain s B r E| ≤ 1 := by
  rw [lamMain, abs_prod]
  calc ∏ i ∈ s, |coefU (r i) (E ∩ B i)| ≤ ∏ _i ∈ s, (1:ℤ) :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => coefU_abs_le _ _)
    _ = 1 := by simp

theorem abs_lamDef_le_one (s : Finset ι) (B : ι → Finset α) (r : ι → ℕ) (i₀ : ι)
    (E : Finset α) : |lamDef s B r i₀ E| ≤ 1 := by
  rw [lamDef, abs_mul, abs_prod]
  have h1 : ∏ i ∈ s.erase i₀, |coefU (r i) (E ∩ B i)| ≤ 1 := by
    calc ∏ i ∈ s.erase i₀, |coefU (r i) (E ∩ B i)| ≤ ∏ _i ∈ s.erase i₀, (1:ℤ) :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => coefU_abs_le _ _)
      _ = 1 := by simp
  have h2 : (0:ℤ) ≤ ∏ i ∈ s.erase i₀, |coefU (r i) (E ∩ B i)| :=
    Finset.prod_nonneg fun i _ => abs_nonneg _
  calc |coefD (r i₀) (E ∩ B i₀)| * ∏ i ∈ s.erase i₀, |coefU (r i) (E ∩ B i)|
      ≤ 1 * 1 := mul_le_mul (coefD_abs_le _ _) h1 h2 (by norm_num)
    _ = 1 := by ring

/-- **`|λ(E)| ≤ 1`.**  The `1 + |s|` terms have disjoint supports: `λ_main` needs every trace
`≤ r_i`, and `λ_{i₀}` needs the trace at `i₀` to be exactly `r_{i₀} + 1` and every other trace
`≤ r_i`.  So at most one of them is nonzero at any `E`. -/
theorem blockLam_abs_le_one (s : Finset ι) (B : ι → Finset α) (r : ι → ℕ) (E : Finset α) :
    |blockLam s B r E| ≤ 1 := by
  classical
  set T : Finset ι := s.filter (fun i => ¬ (E ∩ B i).card ≤ r i) with hT
  rcases Finset.eq_empty_or_nonempty T with hTe | ⟨i₁, hi₁⟩
  · -- every trace is admissible: only the main term survives
    have hall : ∀ i ∈ s, (E ∩ B i).card ≤ r i := by
      intro i hi
      by_contra hc
      exact Finset.notMem_empty i (hTe ▸ Finset.mem_filter.2 ⟨hi, hc⟩)
    have hzero : ∀ i₀ ∈ s, lamDef s B r i₀ E = 0 := by
      intro i₀ hi₀
      exact lamDef_eq_zero_of_card_ne (by have := hall i₀ hi₀; omega)
    rw [blockLam, Finset.sum_congr rfl hzero, Finset.sum_const_zero, sub_zero]
    exact abs_lamMain_le_one s B r E
  · have hi₁s : i₁ ∈ s := (Finset.mem_filter.1 hi₁).1
    have hi₁c : ¬ (E ∩ B i₁).card ≤ r i₁ := (Finset.mem_filter.1 hi₁).2
    have hmain0 : lamMain s B r E = 0 := lamMain_eq_zero_of hi₁s hi₁c
    rcases Finset.eq_singleton_or_nontrivial hi₁ with hTs | hTn
    · -- exactly one excess block: only its defect term survives
      have honly : ∀ i₀ ∈ s, i₀ ≠ i₁ → lamDef s B r i₀ E = 0 := by
        intro i₀ hi₀ hne
        exact lamDef_eq_zero_of (Finset.mem_erase.2 ⟨fun h => hne h.symm, hi₁s⟩) hi₁c
      have hsum : ∑ i₀ ∈ s, lamDef s B r i₀ E = lamDef s B r i₁ E := by
        refine Finset.sum_eq_single_of_mem i₁ hi₁s ?_
        intro i₀ hi₀ hne
        exact honly i₀ hi₀ hne
      rw [blockLam, hmain0, hsum, zero_sub, abs_neg]
      exact abs_lamDef_le_one s B r i₁ E
    · -- two or more excess blocks: everything vanishes
      have hzero : ∀ i₀ ∈ s, lamDef s B r i₀ E = 0 := by
        intro i₀ _
        obtain ⟨i₂, hi₂, hne⟩ := hTn.exists_ne i₀
        have hi₂s : i₂ ∈ s := (Finset.mem_filter.1 hi₂).1
        have hi₂c : ¬ (E ∩ B i₂).card ≤ r i₂ := (Finset.mem_filter.1 hi₂).2
        exact lamDef_eq_zero_of (Finset.mem_erase.2 ⟨hne, hi₂s⟩) hi₂c
      rw [blockLam, hmain0, Finset.sum_congr rfl hzero, Finset.sum_const_zero, sub_zero]
      simp

/-! ### Property 3: the support -/

/-- **The support condition**: a nonzero coefficient has every trace `≤ r_i + 1`. -/
theorem blockLam_support (s : Finset ι) (B : ι → Finset α) (r : ι → ℕ) (E : Finset α)
    {i : ι} (hi : i ∈ s) (hne : blockLam s B r E ≠ 0) : (E ∩ B i).card ≤ r i + 1 := by
  classical
  by_contra hc
  push_neg at hc
  have hcard : ¬ (E ∩ B i).card ≤ r i := by omega
  have hmain0 : lamMain s B r E = 0 := lamMain_eq_zero_of hi hcard
  have hzero : ∀ i₀ ∈ s, lamDef s B r i₀ E = 0 := by
    intro i₀ _
    by_cases hii : i₀ = i
    · subst hii
      exact lamDef_eq_zero_of_card_ne (by omega)
    · exact lamDef_eq_zero_of (Finset.mem_erase.2 ⟨fun h => hii h.symm, hi⟩) hcard
  exact hne (by rw [blockLam, hmain0, Finset.sum_congr rfl hzero, Finset.sum_const_zero, sub_zero])


/-! ### Property 4: the minorant property -/

/-- The `0/1` indicator of a finite set. -/
def indic (S : Finset α) : α → ℤ := fun p => if p ∈ S then 1 else 0

theorem indic_zero_or_one (S : Finset α) (p : α) : indic S p = 0 ∨ indic S p = 1 := by
  unfold indic; split <;> simp

theorem prod_indic (S E : Finset α) : (∏ p ∈ E, indic S p) = if E ⊆ S then 1 else 0 := by
  classical
  by_cases h : E ⊆ S
  · rw [if_pos h]
    exact Finset.prod_eq_one fun p hp => by rw [indic, if_pos (h hp)]
  · rw [if_neg h]
    obtain ⟨p, hpE, hpS⟩ := Finset.not_subset.1 h
    exact Finset.prod_eq_zero hpE (by rw [indic, if_neg hpS])

theorem hitCount_indic (S B : Finset α) : hitCount (indic S) B = (B ∩ S).card := by
  classical
  unfold hitCount
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hpB, hp⟩
    refine ⟨hpB, ?_⟩
    by_contra hc
    rw [indic, if_neg hc] at hp
    exact zero_ne_one hp
  · rintro ⟨hpB, hpS⟩
    exact ⟨hpB, by rw [indic, if_pos hpS]⟩

/-- **Lemma B property 2 for the explicit weights**: `∑_{E ⊆ S} λ(E) ≤ [S = ∅]` for every
subset `S` of the sieve primes.  Evaluate the expansion at the indicator of `S`. -/
theorem blockLam_minorant (s : Finset ι) (B : ι → Finset α) (r : ι → ℕ)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j)) (hr : ∀ i ∈ s, Even (r i))
    {S : Finset α} (hS : S ⊆ s.biUnion B) :
    ∑ E ∈ S.powerset, blockLam s B r E ≤ if S = ∅ then 1 else 0 := by
  classical
  set x : α → ℤ := indic S with hx
  -- the expansion, evaluated at the indicator, is the subset sum over `S`
  have hleft : ∑ E ∈ (s.biUnion B).powerset, blockLam s B r E * ∏ p ∈ E, x p
      = ∑ E ∈ S.powerset, blockLam s B r E := by
    rw [Finset.sum_congr rfl (fun E _ => by rw [hx, prod_indic S E] :
      ∀ E ∈ (s.biUnion B).powerset, blockLam s B r E * ∏ p ∈ E, x p
        = blockLam s B r E * (if E ⊆ S then 1 else 0))]
    rw [← Finset.sum_filter_of_ne (fun E hE h => by
      by_contra hc
      rw [if_neg hc, mul_zero] at h
      exact h rfl)]
    have hset : (s.biUnion B).powerset.filter (fun E => E ⊆ S) = S.powerset := by
      ext E
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun h => h.2, fun h => ⟨h.trans hS, h⟩⟩
    rw [hset]
    exact Finset.sum_congr rfl fun E _ => by rw [if_pos (Finset.mem_powerset.1 ‹_›), mul_one]
  -- the pointwise minorant
  have hright := blockMinorant_le s B r hr x (fun p => by rw [hx]; exact indic_zero_or_one S p)
  have hind : (∏ i ∈ s, bonfIndic (hitCount x (B i))) = if S = ∅ then 1 else 0 := by
    by_cases hSe : S = ∅
    · rw [if_pos hSe]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hx, hitCount_indic, hSe]
      simp [bonfIndic]
    · rw [if_neg hSe]
      obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 hSe
      obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.1 (hS hp)
      refine Finset.prod_eq_zero hi ?_
      rw [hx, hitCount_indic, bonfIndic, if_neg]
      intro hc
      have hemp : B i ∩ S = ∅ := Finset.card_eq_zero.1 hc
      exact Finset.notMem_empty p (hemp ▸ Finset.mem_inter.2 ⟨hpi, hp⟩)
    
  rw [← hleft, ← hind]
  exact le_trans (le_of_eq (blockLam_expand s B r hdisj x)) hright

end NormalNumbers.PrimeModel.BlockSieve
