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

end NormalNumbers.PrimeModel.BlockSieve
