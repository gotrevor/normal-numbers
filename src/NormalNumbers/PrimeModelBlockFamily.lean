import NormalNumbers.PrimeModelBlockWeightsReal
import NormalNumbers.PrimeModelPrimeDimension

/-!
# The concrete graded block family

Lap 4g of `KICKOFF-2026-09-22-multicutoff-lean.md`.  `blockLam_model_lower_graded` takes an
abstract family of pairwise disjoint blocks of mass `≤ 8 d_j`.  This file builds the family the
paper uses (Fable §3, Astra §4):

    B_{j,l} = U^{(j)} ∩ ( y_j^{2^{−(l+1)}}, y_j^{2^{−l}} ],

verifies that the blocks are pairwise disjoint (levels inside a shift by the cutoff chain,
different shifts by hypothesis on the `U^{(j)}`), and that each has mass `≤ 8 d_j` for local
densities `g p ≤ d_j / p` — the `∑ 1/p ≤ 8` over a dyadic-logarithmic prime block is
`PrimeDensity.block_le_eight`.
-/

open Finset

namespace NormalNumbers.PrimeModel.BlockSieve

variable {κ : Type*} [DecidableEq κ]

/-- The cutoff chain of shift `j`: `cut y j l = y_j^{2^{−l}}`, so that
`cut y j (l+1) ^ 2 = cut y j l`. -/
noncomputable def cut (y : κ → ℝ) (j : κ) (l : ℕ) : ℝ := (y j) ^ ((1 : ℝ) / 2 ^ l)

theorem cut_sq {y : κ → ℝ} (j : κ) (hy : 0 ≤ y j) (l : ℕ) :
    (cut y j (l + 1)) ^ 2 = cut y j l := by
  rw [cut, cut, ← Real.rpow_natCast ((y j) ^ ((1:ℝ) / 2 ^ (l+1))) 2, ← Real.rpow_mul hy]
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

theorem cut_antitone {y : κ → ℝ} (j : κ) (hy : 1 ≤ y j) {l l' : ℕ} (h : l ≤ l') :
    cut y j l' ≤ cut y j l := by
  rw [cut, cut]
  refine Real.rpow_le_rpow_of_exponent_le hy ?_
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact pow_le_pow_right₀ (by norm_num) h

/-- The block at shift `j`, level `l`. -/
noncomputable def gradedBlock (U : κ → Finset ℕ) (y : κ → ℝ) : κ × ℕ → Finset ℕ :=
  fun q => (U q.1).filter (fun p => cut y q.1 (q.2 + 1) < (p : ℝ) ∧ (p : ℝ) ≤ cut y q.1 q.2)

theorem gradedBlock_subset (U : κ → Finset ℕ) (y : κ → ℝ) (q : κ × ℕ) :
    gradedBlock U y q ⊆ U q.1 := Finset.filter_subset _ _

/-- Pairwise disjointness: two levels inside one shift are separated by the cutoff chain, and
two shifts by the hypothesis that the `U^{(j)}` are disjoint. -/
theorem gradedBlock_disjoint (U : κ → Finset ℕ) (y : κ → ℝ) (hy : ∀ j, 1 ≤ y j)
    (hU : ∀ j j', j ≠ j' → Disjoint (U j) (U j')) (q q' : κ × ℕ) (hne : q ≠ q') :
    Disjoint (gradedBlock U y q) (gradedBlock U y q') := by
  classical
  by_cases hj : q.1 = q'.1
  · -- same shift, different levels
    have hl : q.2 ≠ q'.2 := by
      intro h
      exact hne (Prod.ext hj h)
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [gradedBlock, Finset.mem_filter] at hp hp'
    obtain ⟨-, hlo, hhi⟩ := hp
    obtain ⟨-, hlo', hhi'⟩ := hp'
    rw [← hj] at hlo' hhi'
    rcases lt_or_gt_of_ne hl with h | h
    · have : cut y q.1 q'.2 ≤ cut y q.1 (q.2 + 1) := cut_antitone q.1 (hy q.1) (by omega)
      linarith
    · have : cut y q.1 q.2 ≤ cut y q.1 (q'.2 + 1) := cut_antitone q.1 (hy q.1) (by omega)
      linarith
  · exact Finset.disjoint_of_subset_left (gradedBlock_subset U y q)
      (Finset.disjoint_of_subset_right (gradedBlock_subset U y q') (hU _ _ hj))

/-- **The mass bound** `∑_{p ∈ B_{j,l}} g p ≤ 8 d_j`: the block is a set of primes in a dyadic
interval `(v, v²]` with `v ≥ 2`, where `PrimeDensity.block_le_eight` gives `∑ 1/p ≤ 8`. -/
theorem gradedBlock_mass_le (U : κ → Finset ℕ) (y : κ → ℝ) (hy : ∀ j, 0 ≤ y j)
    (g : ℕ → ℝ) (hg0 : ∀ p, 0 ≤ g p) (D : κ → ℕ) (q : κ × ℕ)
    (hprime : ∀ p ∈ U q.1, Nat.Prime p)
    (hgle : ∀ p ∈ U q.1, g p ≤ (D q.1 : ℝ) / p)
    (hv : 2 ≤ cut y q.1 (q.2 + 1)) :
    ∑ p ∈ gradedBlock U y q, g p ≤ 8 * (D q.1 : ℝ) := by
  classical
  set v : ℝ := cut y q.1 (q.2 + 1) with hvdef
  set N : ℕ := (U q.1).sup id with hN
  have hDnn : (0:ℝ) ≤ (D q.1 : ℝ) := by positivity
  -- the block embeds in the set `block_le_eight` bounds
  have hsub : gradedBlock U y q
      ⊆ (Finset.Iic N).filter (fun p => Nat.Prime p ∧ v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2) := by
    intro p hp
    simp only [gradedBlock, Finset.mem_filter] at hp
    obtain ⟨hpU, hlo, hhi⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_Iic]
    refine ⟨Finset.le_sup (f := id) hpU, hprime p hpU, hlo, ?_⟩
    rw [hvdef, cut_sq q.1 (hy q.1)]
    exact hhi
  calc ∑ p ∈ gradedBlock U y q, g p
      ≤ ∑ p ∈ gradedBlock U y q, (D q.1 : ℝ) * ((1:ℝ) / p) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpU : p ∈ U q.1 := gradedBlock_subset U y q hp
        rw [mul_one_div]
        exact hgle p hpU
    _ = (D q.1 : ℝ) * ∑ p ∈ gradedBlock U y q, (1:ℝ) / p := by rw [Finset.mul_sum]
    _ ≤ (D q.1 : ℝ) * 8 := by
        refine mul_le_mul_of_nonneg_left ?_ hDnn
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
        · intro p _ _; positivity
        · exact NormalNumbers.PrimeModel.PrimeDensity.block_le_eight v hv N
    _ = 8 * (D q.1 : ℝ) := by ring

/-! ### Lemma B for the concrete family -/

/-- **Lemma B, fully instantiated.**  For the concrete graded family
`B_{j,l} = U^{(j)} ∩ (y_j^{2^{−(l+1)}}, y_j^{2^{−l}}]` with local densities `g p ≤ d_j / p`,
`g ≤ 1/2`, the signed subset sum of the graded sieve weight is at least `(1 − 0.3 T)` times the
model density of the whole sieve range, `T = ∑_j e^{−u_j}`. -/
theorem gradedBlock_model_lower
    (t : Finset κ) (L : ℕ) (d u : κ → ℕ) (hd : ∀ j, 1 ≤ d j)
    (U : κ → Finset ℕ) (y : κ → ℝ) (hy : ∀ j, 1 ≤ y j)
    (hU : ∀ j j', j ≠ j' → Disjoint (U j) (U j'))
    (hprime : ∀ j, ∀ p ∈ U j, Nat.Prime p)
    (g : ℕ → ℝ) (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1 / 2)
    (hgle : ∀ j, ∀ p ∈ U j, g p ≤ (d j : ℝ) / p)
    (hcut : ∀ j ∈ t, ∀ l < L, 2 ≤ cut y j (l + 1))
    (hT1 : ∑ j ∈ t, Real.exp (-(u j : ℝ)) ≤ 1) :
    (1 - 0.3 * ∑ j ∈ t, Real.exp (-(u j : ℝ)))
        * ∏ p ∈ (t ×ˢ Finset.range L).biUnion (gradedBlock U y), (1 - g p)
      ≤ ∑ E ∈ ((t ×ˢ Finset.range L).biUnion (gradedBlock U y)).powerset,
          (blockLam (t ×ˢ Finset.range L) (gradedBlock U y) (gradedDeg d u) E : ℝ)
            * ∏ p ∈ E, g p := by
  classical
  refine blockLam_model_lower_graded t L d u hd (gradedBlock U y) g hg0 hg1 ?_ ?_ hT1
  · intro q _ q' _ hne
    exact gradedBlock_disjoint U y hy hU q q' hne
  · intro q hq
    rw [Finset.mem_product, Finset.mem_range] at hq
    exact gradedBlock_mass_le U y (fun j => le_trans zero_le_one (hy j)) g hg0 d q
      (hprime q.1) (hgle q.1) (hcut q.1 hq.1 q.2 hq.2)

end NormalNumbers.PrimeModel.BlockSieve
