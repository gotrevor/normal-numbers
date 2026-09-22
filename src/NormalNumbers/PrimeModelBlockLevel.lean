import NormalNumbers.PrimeModelBlockSieveModel

/-!
# Lemma B, part 3: the support level

Lap 3 of `KICKOFF-2026-09-22-multicutoff-lean.md`; spec `papers/ROUND2-multicutoff-fable.md` §3
"Coefficients and support" / `papers/ROUND2-multicutoff-astra.md` §4.

A nonzero coefficient `λ(E) = ∏_i c_i(E ∩ B_i)` has `|E ∩ B_i| ≤ r_i + 1` for every block, so
`∏_{p ∈ E} p ≤ ∏_i w_i^{r_i + 1}` where `w_i` is the top of block `i`
(`prod_le_of_block_bounds`).  For the graded schedule `B_{j,l} ⊆ (y_j^{2^{-l-1}}, y_j^{2^{-l}}]`
with `r_{j,l} = 64 d_j + 2 u_j + 2l + 4`, the geometric sum

    ∑_{l ≥ 0} (64 d + 2u + 2l + 5) 2^{-l} = 2(64d + 2u + 5) + 4 = 128 d + 4u + 14

gives the level `log R = ∑_j (128 d_j + 4 u_j + 14) log y_j` (`level_sum_le`).

Note this is the kickoff's `128 d + 4u + 14` directly: the paper's `128 d + 4u + 12` plus a
separate `log y₁` for the one defect block is unnecessary once every block is allowed its
uniform `r_i + 1` trace bound.
-/

open Finset

namespace NormalNumbers.PrimeModel.BlockSieve

variable {ι : Type*} [DecidableEq ι]

/-! ### The product over an admissible support -/

/-- If `E` meets block `i` in at most `m i` primes, each of size at most `w i`, then
`∏_{p ∈ E} p ≤ ∏_i (w i)^(m i)`. -/
theorem prod_le_of_block_bounds (s : Finset ι) (B : ι → Finset ℕ) (w m : ι → ℕ)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j))
    (hw : ∀ i ∈ s, ∀ p ∈ B i, p ≤ w i) (hw1 : ∀ i ∈ s, 1 ≤ w i)
    {E : Finset ℕ} (hE : E ⊆ s.biUnion B)
    (hm : ∀ i ∈ s, (E ∩ B i).card ≤ m i) :
    ∏ p ∈ E, p ≤ ∏ i ∈ s, (w i) ^ (m i) := by
  classical
  have hsplit : E = s.biUnion (fun i => E ∩ B i) := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hp
      obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.1 (hE hp)
      exact ⟨i, hi, hp, hpi⟩
    · rintro ⟨i, _, hp, _⟩; exact hp
  have hdisj' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (E ∩ B i) (E ∩ B j) := by
    intro i hi j hj hij
    exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right (hdisj i hi j hj hij))
  have hprod : ∏ p ∈ E, p = ∏ i ∈ s, ∏ p ∈ E ∩ B i, p := by
    conv_lhs => rw [hsplit]
    exact Finset.prod_biUnion (f := fun p : ℕ => p) hdisj'
  calc ∏ p ∈ E, p = ∏ i ∈ s, ∏ p ∈ E ∩ B i, p := hprod
    _ ≤ ∏ i ∈ s, (w i) ^ (m i) := by
        refine Finset.prod_le_prod' fun i hi => ?_
        calc ∏ p ∈ E ∩ B i, p ≤ ∏ p ∈ E ∩ B i, w i :=
              Finset.prod_le_prod' fun p hp => hw i hi p (Finset.mem_inter.1 hp).2
          _ = (w i) ^ (E ∩ B i).card := by rw [Finset.prod_const]
          _ ≤ (w i) ^ (m i) := Nat.pow_le_pow_right (hw1 i hi) (hm i hi)

/-! ### The geometric sums of the graded schedule -/

/-- `∑_{l < L} 2^{-l} = 2 − 2·2^{-L}`. -/
theorem sum_half_pow (L : ℕ) :
    ∑ l ∈ Finset.range L, ((1:ℝ)/2) ^ l = 2 - 2 * ((1:ℝ)/2) ^ L := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih]; ring

/-- `∑_{l < L} l 2^{-l} = 2 − (2L+2)·2^{-L}`. -/
theorem sum_mul_half_pow (L : ℕ) :
    ∑ l ∈ Finset.range L, (l : ℝ) * ((1:ℝ)/2) ^ l
      = 2 - (2 * (L:ℝ) + 2) * ((1:ℝ)/2) ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- **The support level**: `∑_{l < L} (64d + 2u + 2l + 5) 2^{-l} ≤ 128 d + 4u + 14`. -/
theorem level_sum_le (d u L : ℕ) :
    ∑ l ∈ Finset.range L, ((64 * d + 2 * u + 2 * l + 5 : ℕ) : ℝ) * ((1:ℝ)/2) ^ l
      ≤ 128 * d + 4 * u + 14 := by
  have hterm : ∀ l ∈ Finset.range L,
      ((64 * d + 2 * u + 2 * l + 5 : ℕ) : ℝ) * ((1:ℝ)/2) ^ l
        = (64 * (d:ℝ) + 2 * u + 5) * ((1:ℝ)/2) ^ l + 2 * ((l:ℝ) * ((1:ℝ)/2) ^ l) := by
    intro l _
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_half_pow, sum_mul_half_pow]
  have hpow : (0:ℝ) ≤ ((1:ℝ)/2) ^ L := by positivity
  have hd : (0:ℝ) ≤ (d:ℝ) := by positivity
  have hu : (0:ℝ) ≤ (u:ℝ) := by positivity
  have hL : (0:ℝ) ≤ (L:ℝ) := by positivity
  nlinarith [hpow, hd, hu, hL]

end NormalNumbers.PrimeModel.BlockSieve
