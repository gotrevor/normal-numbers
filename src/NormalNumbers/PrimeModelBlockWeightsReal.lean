import NormalNumbers.PrimeModelBlockWeights
import NormalNumbers.PrimeModelBlockSieveModel

/-!
# Lemma B, the model side of the explicit weights

Lap 4e of `KICKOFF-2026-09-22-multicutoff-lean.md`.  `PrimeModelBlockWeights.blockLam_expand`
is stated for an integer-valued weight `x : α → ℤ` (that is all the *arithmetic* side needs,
since it is evaluated at indicators).  The *model* side evaluates the same weight at the local
densities `g p = d_p / p`, which are real.  This file:

* `sum_powerset_coefU_real`, `sum_powerset_coefD_real` — the real powerset forms of the block
  Bonferroni polynomial and its defect, identified with `esymmAlt` and `esymmOn`;
* `blockLam_expand_real` — `∑_{E ⊆ U} λ(E) ∏_{p∈E} g p = ∏_i P_{r_i} − ∑_i e_{r_i+1} ∏_{j≠i} P_{r_j}`;
* `blockLam_model_lower` — **Lemma B, property 3 for the explicit weights**:

      ∑_{E ⊆ U} λ(E) ∏_{p∈E} g p  ≥  (1 − 0.3 T) ∏_{p ∈ U} (1 − g p).

Together with `PrimeModelBrunCountGraded.graded_sifted_count_lower` (which consumes
`blockLam_minorant`, `blockLam_abs_le_one`, `blockLam_support`) this is Lemma B as the paper
states it.
-/

open Finset

namespace NormalNumbers.PrimeModel.BlockSieve

variable {ι : Type*} [DecidableEq ι] {α : Type*} [DecidableEq α]

/-! ### The real powerset forms -/

theorem sum_powerset_coefU_real (g : α → ℝ) (B : Finset α) (r : ℕ) :
    ∑ E ∈ B.powerset, (coefU r E : ℝ) * ∏ p ∈ E, g p = esymmAlt g B r := by
  classical
  have hzero : ∀ E ∈ B.powerset, ¬ (E.card ≤ r) → (coefU r E : ℝ) * ∏ p ∈ E, g p = 0 := by
    intro E _ hE
    rw [coefU, if_neg hE]
    push_cast
    ring
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
  · unfold esymmAlt esymmOn
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun E hE => ?_
    rw [Finset.mem_powersetCard] at hE
    rw [coefU, if_pos (by omega : E.card ≤ r), hE.2]
    push_cast
    ring
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro E hEi hEj
    rw [Finset.mem_powersetCard] at hEi hEj
    exact hij (hEi.2 ▸ hEj.2 ▸ rfl)

theorem sum_powerset_coefD_real (g : α → ℝ) (B : Finset α) (r : ℕ) :
    ∑ E ∈ B.powerset, (coefD r E : ℝ) * ∏ p ∈ E, g p = esymmOn g B (r + 1) := by
  classical
  have hzero : ∀ E ∈ B.powerset, ¬ (E.card = r + 1) → (coefD r E : ℝ) * ∏ p ∈ E, g p = 0 := by
    intro E _ hE
    rw [coefD, if_neg hE]
    push_cast
    ring
  rw [← Finset.sum_filter_of_ne (fun E hE h => by
    by_contra hc
    exact h (hzero E hE hc))]
  have hset : B.powerset.filter (fun E => E.card = r + 1) = B.powersetCard (r + 1) := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
  rw [hset]
  unfold esymmOn
  refine Finset.sum_congr rfl fun E hE => ?_
  rw [Finset.mem_powersetCard] at hE
  rw [coefD, if_pos hE.2]
  push_cast
  ring

/-! ### The expansion over `ℝ` -/

theorem blockLam_expand_real (s : Finset ι) (B : ι → Finset α) (r : ι → ℕ)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j)) (g : α → ℝ) :
    ∑ E ∈ (s.biUnion B).powerset, (blockLam s B r E : ℝ) * ∏ p ∈ E, g p
      = (∏ i ∈ s, esymmAlt g (B i) (r i))
        - ∑ i₀ ∈ s, esymmOn g (B i₀) (r i₀ + 1)
            * ∏ i ∈ s.erase i₀, esymmAlt g (B i) (r i) := by
  classical
  have hmain : ∑ E ∈ (s.biUnion B).powerset, (lamMain s B r E : ℝ) * ∏ p ∈ E, g p
      = ∏ i ∈ s, esymmAlt g (B i) (r i) := by
    have h1 := prod_sum_powerset_disjoint (R := ℝ) g s B hdisj
      (fun i F => ((coefU (r i) F : ℤ) : ℝ))
    rw [Finset.prod_congr rfl (fun i _ => sum_powerset_coefU_real g (B i) (r i))] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun E _ => ?_
    congr 1
    rw [lamMain]
    push_cast
    rfl
  have hdef : ∀ i₀ ∈ s, ∑ E ∈ (s.biUnion B).powerset, (lamDef s B r i₀ E : ℝ) * ∏ p ∈ E, g p
      = esymmOn g (B i₀) (r i₀ + 1) * ∏ i ∈ s.erase i₀, esymmAlt g (B i) (r i) := by
    intro i₀ hi₀
    set c : ι → Finset α → ℝ :=
      fun i F => if i = i₀ then ((coefD (r i) F : ℤ) : ℝ) else ((coefU (r i) F : ℤ) : ℝ) with hc
    have h1 := prod_sum_powerset_disjoint (R := ℝ) g s B hdisj c
    have hLHS : (∏ i ∈ s, ∑ E ∈ (B i).powerset, c i E * ∏ p ∈ E, g p)
        = esymmOn g (B i₀) (r i₀ + 1) * ∏ i ∈ s.erase i₀, esymmAlt g (B i) (r i) := by
      rw [← Finset.mul_prod_erase s _ hi₀]
      congr 1
      · rw [hc]; simp only [if_pos rfl]; exact sum_powerset_coefD_real g (B i₀) (r i₀)
      · refine Finset.prod_congr rfl fun i hi => ?_
        have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
        rw [hc]; simp only [if_neg hne]; exact sum_powerset_coefU_real g (B i) (r i)
    have hcoef : ∀ E : Finset α, (∏ i ∈ s, c i (E ∩ B i)) = ((lamDef s B r i₀ E : ℤ) : ℝ) := by
      intro E
      rw [← Finset.mul_prod_erase s _ hi₀, lamDef, hc]
      simp only [if_pos rfl]
      push_cast
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
      simp only [if_neg hne]
    calc ∑ E ∈ (s.biUnion B).powerset, (lamDef s B r i₀ E : ℝ) * ∏ p ∈ E, g p
        = ∑ E ∈ (s.biUnion B).powerset, (∏ i ∈ s, c i (E ∩ B i)) * ∏ p ∈ E, g p :=
          Finset.sum_congr rfl fun E _ => by rw [hcoef E]
      _ = esymmOn g (B i₀) (r i₀ + 1) * ∏ i ∈ s.erase i₀, esymmAlt g (B i) (r i) := by
          rw [← h1, hLHS]
  have hsplit : ∀ E : Finset α, ((blockLam s B r E : ℤ) : ℝ) * ∏ p ∈ E, g p
      = (lamMain s B r E : ℝ) * ∏ p ∈ E, g p
        - ∑ i₀ ∈ s, (lamDef s B r i₀ E : ℝ) * ∏ p ∈ E, g p := by
    intro E
    rw [blockLam]
    push_cast
    rw [sub_mul, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun E _ => hsplit E), Finset.sum_sub_distrib, hmain,
    Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl hdef

/-! ### Lemma B, property 3 for the explicit weights -/

/-- **The model lower bound for the explicit graded weight.**  With pairwise disjoint blocks,
even truncation degrees, local densities `g ≤ 1/2`, and total relative defect
`∑_i e_{r_i+1}(g; B_i) / ∏_{B_i}(1−g) ≤ 0.215 T` (`T ≤ 1`), the signed subset sum of `blockLam`
against `g` is at least `(1 − 0.3 T)` times the model density of the whole sieve range. -/
theorem blockLam_model_lower (s : Finset ι) (B : ι → Finset α) (r : ι → ℕ)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j))
    (hr : ∀ i ∈ s, Even (r i)) (g : α → ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1 / 2) {T : ℝ}
    (hsum : ∑ i ∈ s, esymmOn g (B i) (r i + 1) / ∏ p ∈ B i, (1 - g p) ≤ 0.215 * T)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (1 - 0.3 * T) * ∏ p ∈ s.biUnion B, (1 - g p)
      ≤ ∑ E ∈ (s.biUnion B).powerset, (blockLam s B r E : ℝ) * ∏ p ∈ E, g p := by
  classical
  set V : ι → ℝ := fun i => ∏ p ∈ B i, (1 - g p) with hVdef
  set Ub : ι → ℝ := fun i => esymmAlt g (B i) (r i) with hUdef
  set Db : ι → ℝ := fun i => esymmOn g (B i) (r i + 1) / V i with hDdef
  have hg1' : ∀ p, g p ≤ 1 := fun p => le_trans (hg1 p) (by norm_num)
  have hVpos : ∀ i, 0 < V i := by
    intro i
    exact Finset.prod_pos fun p _ => by linarith [hg1 p]
  have hDb0 : ∀ i, 0 ≤ Db i := fun i =>
    div_nonneg (esymmOn_nonneg g hg0 _ _) (hVpos i).le
  have hbonf := esymmAlt_bonferroni g hg0 hg1'
  have hlow : ∀ i ∈ s, V i ≤ Ub i := fun i hi => (hbonf (B i) (r i)).1 (hr i hi)
  have hhigh : ∀ i ∈ s, Ub i ≤ V i * (1 + Db i) := by
    intro i hi
    have hodd : ¬ Even (r i + 1) := by
      simpa [Nat.even_add_one] using (hr i hi)
    have h := (hbonf (B i) (r i + 1)).2 hodd
    have hsign : (-1:ℝ) ^ (r i + 1) = -1 :=
      Odd.neg_one_pow (by simpa [Nat.odd_add_one] using (hr i hi))
    rw [esymmAlt_succ, hsign] at h
    have hVne : V i ≠ 0 := (hVpos i).ne'
    have : V i * (1 + Db i) = V i + esymmOn g (B i) (r i + 1) := by
      rw [hDdef]
      field_simp
    rw [this]
    simp only [hUdef, hVdef] at h ⊢
    linarith
  have hVDb : ∀ i, V i * Db i = esymmOn g (B i) (r i + 1) := by
    intro i
    rw [hDdef]
    exact mul_div_cancel₀ _ (hVpos i).ne'
  have hkey := model_defect_eta s V Ub Db (fun i _ => hVpos i) (fun i _ => hDb0 i)
    hlow hhigh (by simpa [hDdef, hVdef] using hsum) hT0 hT1
  have hprodV : ∏ i ∈ s, V i = ∏ p ∈ s.biUnion B, (1 - g p) := by
    rw [Finset.prod_biUnion]
    intro i hi j hj hij
    exact hdisj i hi j hj hij
  rw [blockLam_expand_real s B r hdisj g]
  rw [← hprodV]
  calc (1 - 0.3 * T) * ∏ i ∈ s, V i
      ≤ (∏ i ∈ s, Ub i) - ∑ i ∈ s, (V i * Db i) * ∏ j ∈ s.erase i, Ub j := hkey
    _ = (∏ i ∈ s, esymmAlt g (B i) (r i))
        - ∑ i₀ ∈ s, esymmOn g (B i₀) (r i₀ + 1)
            * ∏ i ∈ s.erase i₀, esymmAlt g (B i) (r i) := by
        simp only [hUdef, hVDb]

end NormalNumbers.PrimeModel.BlockSieve
