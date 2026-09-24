import Mathlib

/-!
# The Erdős–Borwein Lambert series `∑_{n≥1} 1/(bⁿ − 1) = ∑_m d(m)/bᵐ`

Both sides are the sum of `b^{-(n+1)(k+1)}` over pairs `(n, k) : ℕ × ℕ`: summing over `k` first
gives the geometric series `1/(b^{n+1} − 1)`, summing over the fibre `(n+1)(k+1) = m` counts the
divisors of `m`.  The structure mirrors `primeSumAtBase_eq_primeLambertAtBase`.
-/

namespace NormalNumbers.CastingOut

open Finset

/-- The double-series term `b^{-(n+1)(k+1)}`, indexed by `(n, k)`. -/
noncomputable def divPowTerm (b : ℕ) (x : ℕ × ℕ) : ℝ :=
  1 / (b : ℝ) ^ ((x.1 + 1) * (x.2 + 1))

lemma divPowTerm_nonneg (b : ℕ) (x : ℕ × ℕ) : 0 ≤ divPowTerm b x := by
  unfold divPowTerm; positivity

lemma summable_divPowTerm {b : ℕ} (hb : 2 ≤ b) : Summable (divPowTerm b) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hr0 : (0 : ℝ) ≤ 1 / b := by positivity
  have hr1 : (1 : ℝ) / b < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hg := summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nonneg_of_le (divPowTerm_nonneg b) (fun x => ?_) (hg.mul_of_nonneg hg
    (fun _ => pow_nonneg hr0 _) (fun _ => pow_nonneg hr0 _))
  unfold divPowTerm
  rw [← pow_add, one_div_pow]
  refine one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) ?_)
  nlinarith

/-- Summing over `k` first: the inner geometric series. -/
lemma tsum_divPowTerm_snd {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    ∑' k : ℕ, divPowTerm b (n, k) = 1 / ((b : ℝ) ^ (n + 1) - 1) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold divPowTerm
  simp only
  have hbp : (1 : ℝ) < (b : ℝ) ^ (n + 1) := one_lt_pow₀ (by linarith) (Nat.succ_ne_zero n)
  set r : ℝ := 1 / (b : ℝ) ^ (n + 1) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one (by linarith)]; exact hbp
  have hfun : (fun k : ℕ => 1 / (b : ℝ) ^ ((n + 1) * (k + 1))) = fun k => r * r ^ k := by
    funext k
    rw [hr, pow_mul, pow_succ', ← one_div_mul_one_div, one_div_pow]
  rw [hfun, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, hr]
  have hne : (b : ℝ) ^ (n + 1) - 1 ≠ 0 := by linarith
  field_simp

/-- The map `(n, k) ↦ (n+1)(k+1)`. -/
def divPowIndex (x : ℕ × ℕ) : ℕ := (x.1 + 1) * (x.2 + 1)

/-- Summing over the fibre `(n+1)(k+1) = m` counts the divisors of `m`. -/
lemma tsum_divPowTerm_fiber {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    ∑' x : (divPowIndex ⁻¹' {m} : Set (ℕ × ℕ)), divPowTerm b x
      = (m.divisors.card : ℝ) / (b : ℝ) ^ m := by
  classical
  rw [_root_.tsum_subtype]
  set s : Finset (ℕ × ℕ) := Finset.range (m + 1) ×ˢ Finset.range (m + 1) with hs
  have hsupp : ∀ x ∉ s, (divPowIndex ⁻¹' {m}).indicator (divPowTerm b) x = 0 := by
    intro x hx
    rw [Set.indicator_apply_eq_zero]
    intro hxm
    simp only [Set.mem_preimage, Set.mem_singleton_iff, divPowIndex] at hxm
    exact absurd (by
      rw [hs, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      constructor <;> nlinarith) hx
  rw [tsum_eq_sum hsupp]
  have hfilter : ∀ x ∈ s, (divPowIndex ⁻¹' {m}).indicator (divPowTerm b) x
      = if divPowIndex x = m then 1 / (b : ℝ) ^ m else 0 := by
    intro x _
    rw [Set.indicator_apply]
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    by_cases hxm : divPowIndex x = m
    · rw [if_pos hxm, if_pos hxm]
      unfold divPowTerm divPowIndex at *
      rw [hxm]
    · rw [if_neg hxm, if_neg hxm]
  rw [Finset.sum_congr rfl hfilter, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_one_div (m.divisors.card : ℝ)]
  congr 1
  norm_cast
  refine Finset.card_bij' (fun x _ => x.1 + 1) (fun d _ => (d - 1, m / d - 1)) ?_ ?_ ?_ ?_
  · intro x hx
    have hxm : (x.1 + 1) * (x.2 + 1) = m := (Finset.mem_filter.mp hx).2
    rw [Nat.mem_divisors]
    exact ⟨⟨x.2 + 1, hxm.symm⟩, by rw [← hxm]; positivity⟩
  · intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨⟨k, rfl⟩, hm0⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
    have hdiv : d * k / d = k := Nat.mul_div_cancel_left k hd0
    simp only [Finset.mem_filter, hs, Finset.mem_product, Finset.mem_range, divPowIndex, hdiv]
    have hle : d ≤ d * k := Nat.le_mul_of_pos_right d hk0
    have hle2 : k ≤ d * k := Nat.le_mul_of_pos_left k hd0
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.sub_add_cancel hd0, Nat.sub_add_cancel hk0]
  · intro x hx
    have hxm : (x.1 + 1) * (x.2 + 1) = m := (Finset.mem_filter.mp hx).2
    have h1 : m / (x.1 + 1) = x.2 + 1 := by
      rw [← hxm, Nat.mul_div_cancel_left _ (Nat.succ_pos _)]
    simp [h1]
  · intro d hd
    rw [Nat.mem_divisors] at hd
    have hd0 : d ≠ 0 := by rintro rfl; exact hd.2 (Nat.eq_zero_of_zero_dvd hd.1)
    omega

/-- **The Erdős–Borwein Lambert identity.** -/
theorem tsum_one_div_pow_sub_one {b : ℕ} (hb : 2 ≤ b) :
    ∑' n : ℕ, 1 / ((b : ℝ) ^ (n + 1) - 1)
      = ∑' m : ℕ, ((m.divisors.card : ℝ)) / (b : ℝ) ^ m := by
  classical
  have hsum := summable_divPowTerm hb
  have h1 : ∑' n : ℕ, 1 / ((b : ℝ) ^ (n + 1) - 1) = ∑' x : ℕ × ℕ, divPowTerm b x := by
    rw [hsum.tsum_prod' (fun n => hsum.prod_factor n)]
    exact (tsum_congr fun n => tsum_divPowTerm_snd hb n).symm
  have h2 : ∑' x : ℕ × ℕ, divPowTerm b x
      = ∑' m : ℕ, ((m.divisors.card : ℝ)) / (b : ℝ) ^ m := by
    have h := (hsum.hasSum.tsum_fiberwise divPowIndex).tsum_eq
    rw [← h]
    exact tsum_congr (tsum_divPowTerm_fiber hb)
  rw [h1, h2]

end NormalNumbers.CastingOut
