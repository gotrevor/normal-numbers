/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4BalancedRigidity

/-!
# The variance lower bound behind (E): the deduction, proved

`G4BalancedRigidity`'s `Budget.RoughRowVarianceLower` is the single external ingredient of the
deformation verdict: the rough-prime row second moment must be **at least** a constant multiple of
the coefficient square sum.  This module proves the general deduction that produces such a lower
bound, leaving only the two arithmetic inputs it consumes.

The row is `R(n) = Σ_i c_i X_i(n)` with `i` ranging over the released pairs `(α, j)`, `j > K′`,
`c_{α,j} = A_{να} 4^{-j}`, and `X_i` the rough-prime fluctuation at the shifted argument.  Then

    avg_n R(n)²  ≥  v · Σ_i c_i²  −  ε · (Σ_i |c_i|)²                        (`sampleAvg_sq_lower`)

whenever each `X_i` has sample second moment `≥ v` (**per-term non-degeneracy**) and distinct
terms have sample correlation `≤ ε` in absolute value (**near-orthogonality**).  Both are
statements about `ω` along a CRT progression, not about the sampler's shape.

`rowVarianceLower_of_orthogonal` packages the reduction: with the schedule's coefficients the
ratio `(Σ|c|)²/Σc²` is `≈ 2^K`, so the hypothesis needed is `ε ≤ v/2^{K+1}` — near-orthogonality
at the scale the frozen small primes already supply.  That inequality, and the per-term
non-degeneracy `v`, are now the *only* unproved inputs anywhere in the verdict.
-/

open Finset

namespace NormalNumbers.G4.RowVariance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sample average of `f` over a finite set of sample points. -/
noncomputable def avg (P : Finset ℕ) (f : ℕ → ℝ) : ℝ := (∑ n ∈ P, f n) / P.card

lemma avg_double_sum (P : Finset ℕ) (F : ι → ι → ℕ → ℝ) :
    avg P (fun n => ∑ i, ∑ j, F i j n) = ∑ i, ∑ j, avg P (F i j) := by
  unfold avg
  rw [Finset.sum_comm]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_div]

/-- **The anti-concentration deduction.**  Per-term non-degeneracy plus near-orthogonality give a
lower bound on the second moment of a weighted row, with the correlation error priced by the
square of the `ℓ¹` norm of the weights. -/
theorem sampleAvg_sq_lower (P : Finset ℕ) (X : ι → ℕ → ℝ) (c : ι → ℝ) {v ε : ℝ} (hε : 0 ≤ ε)
    (hvar : ∀ i, v ≤ avg P (fun n => (X i n) ^ 2))
    (hcov : ∀ i j, i ≠ j → |avg P (fun n => X i n * X j n)| ≤ ε) :
    v * (∑ i, (c i) ^ 2) - ε * (∑ i, |c i|) ^ 2 ≤ avg P (fun n => (∑ i, c i * X i n) ^ 2) := by
  classical
  set A : ι → ι → ℝ := fun i j => avg P (fun n => X i n * X j n) with hA
  have hexp : avg P (fun n => (∑ i, c i * X i n) ^ 2) = ∑ i, ∑ j, (c i * c j) * A i j := by
    have hpt : ∀ n, (∑ i, c i * X i n) ^ 2
        = ∑ i, ∑ j, (c i * c j) * (X i n * X j n) := by
      intro n
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    calc avg P (fun n => (∑ i, c i * X i n) ^ 2)
        = avg P (fun n => ∑ i, ∑ j, (c i * c j) * (X i n * X j n)) := by
          unfold avg; rw [Finset.sum_congr rfl fun n _ => hpt n]
      _ = ∑ i, ∑ j, avg P (fun n => (c i * c j) * (X i n * X j n)) :=
          avg_double_sum P (fun i j n => (c i * c j) * (X i n * X j n))
      _ = ∑ i, ∑ j, (c i * c j) * A i j := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [hA]; unfold avg; rw [← Finset.mul_sum, mul_div_assoc]
  rw [hexp]
  -- per-`i` lower bound
  have hrow : ∀ i, (c i) ^ 2 * v - ε * (|c i| * ∑ j, |c j|) ≤ ∑ j, (c i * c j) * A i j := by
    intro i
    have hdiag : (c i) ^ 2 * v ≤ (c i * c i) * A i i := by
      have := hvar i
      have hAi : v ≤ A i i := by
        rw [hA]; simpa [sq] using this
      nlinarith [sq_nonneg (c i)]
    have hoff : ∀ j ∈ Finset.univ.erase i, -(ε * (|c i| * |c j|)) ≤ (c i * c j) * A i j := by
      intro j hj
      have hne : i ≠ j := fun he => (Finset.mem_erase.1 hj).1 he.symm
      have h1 : |(c i * c j) * A i j| ≤ |c i| * |c j| * ε := by
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hcov i j hne) (by positivity)
      have h2 := neg_abs_le ((c i * c j) * A i j)
      calc -(ε * (|c i| * |c j|)) = -(|c i| * |c j| * ε) := by ring
        _ ≤ -|(c i * c j) * A i j| := by linarith
        _ ≤ (c i * c j) * A i j := h2
    have hsum : ∑ j, (c i * c j) * A i j
        = (c i * c i) * A i i + ∑ j ∈ Finset.univ.erase i, (c i * c j) * A i j :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    have hneg : ∑ j ∈ Finset.univ.erase i, -(ε * (|c i| * |c j|))
        ≤ ∑ j ∈ Finset.univ.erase i, (c i * c j) * A i j := Finset.sum_le_sum hoff
    have hbig : -(ε * (|c i| * ∑ j, |c j|)) ≤ ∑ j ∈ Finset.univ.erase i, -(ε * (|c i| * |c j|)) := by
      have he : ∑ j ∈ Finset.univ.erase i, -(ε * (|c i| * |c j|))
          = -(ε * (|c i| * ∑ j ∈ Finset.univ.erase i, |c j|)) := by
        simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
      rw [he]
      have hsub : ∑ j ∈ Finset.univ.erase i, |c j| ≤ ∑ j, |c j| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun j _ _ => abs_nonneg _)
      have : 0 ≤ ε * |c i| := by positivity
      nlinarith
    rw [hsum]; linarith
  have htot : ∑ i, ((c i) ^ 2 * v - ε * (|c i| * ∑ j, |c j|))
      ≤ ∑ i, ∑ j, (c i * c j) * A i j := Finset.sum_le_sum fun i _ => hrow i
  have hlhs : ∑ i, ((c i) ^ 2 * v - ε * (|c i| * ∑ j, |c j|))
      = v * (∑ i, (c i) ^ 2) - ε * (∑ i, |c i|) ^ 2 := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [← Finset.sum_mul]; ring
    · have hre : ∀ i : ι, ε * (|c i| * ∑ j, |c j|) = (ε * ∑ j, |c j|) * |c i| := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => hre i), ← Finset.mul_sum, sq]; ring
  rw [hlhs] at htot
  exact htot

/-- **The reduction.**  If the correlation level `ε` is below `v / (2·ratio)` where `ratio` bounds
`(Σ|c|)²/Σc²`, the row second moment is at least `v/2` times the coefficient square sum — the
shape `Budget.RoughRowVarianceLower` asks for. -/
theorem rowVariance_half (P : Finset ℕ) (X : ι → ℕ → ℝ) (c : ι → ℝ) {v ε ratio : ℝ}
    (hε : 0 ≤ ε) (_hv : 0 ≤ v)
    (hvar : ∀ i, v ≤ avg P (fun n => (X i n) ^ 2))
    (hcov : ∀ i j, i ≠ j → |avg P (fun n => X i n * X j n)| ≤ ε)
    (hratio : (∑ i, |c i|) ^ 2 ≤ ratio * ∑ i, (c i) ^ 2)
    (hsmall : ε * ratio ≤ v / 2) (_hratio0 : 0 ≤ ratio) :
    (v / 2) * (∑ i, (c i) ^ 2) ≤ avg P (fun n => (∑ i, c i * X i n) ^ 2) := by
  have hsq : (0 : ℝ) ≤ ∑ i, (c i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hmain := sampleAvg_sq_lower P X c hε hvar hcov
  have herr : ε * (∑ i, |c i|) ^ 2 ≤ (v / 2) * ∑ i, (c i) ^ 2 := by
    calc ε * (∑ i, |c i|) ^ 2 ≤ ε * (ratio * ∑ i, (c i) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hratio hε
      _ = (ε * ratio) * ∑ i, (c i) ^ 2 := by ring
      _ ≤ (v / 2) * ∑ i, (c i) ^ 2 := mul_le_mul_of_nonneg_right hsmall hsq
  linarith



/-! ### Where the correlation comes from: only primes dividing the shift gap

Input (2) of the reduction — near-orthogonality `|avg X_i X_j| ≤ ε` at distinct shifts — is not a
uniform smallness assumption.  For the fluctuation `X_i(n) = Σ_p (1[p ∣ n + ρ_i] − a_p)` the
same-prime cross terms are completely determined by one divisibility test:

* if `p ∤ (ρ_i − ρ_j)` the two events are **disjoint** (`not_both_dvd`) and the centred product
  averages to exactly `−a_p b_p ≤ 0` (`avg_centred_mul_of_disjoint`) — a *negative* contribution,
  which helps rather than hurts;
* if `p ∣ (ρ_i − ρ_j)` the events coincide and the contribution is positive, of size `≈ 1/p`.

So the positive part of the correlation is carried by the rough primes dividing the shift gap
`ρ_i − ρ_j`, of which there are at most `log|ρ_i − ρ_j| / log T` — that counting, plus the
cross-prime (`p ≠ q`) CRT independence, is all that input (2) still needs. -/

lemma avg_const (P : Finset ℕ) (hP : P.Nonempty) (r : ℝ) : avg P (fun _ => r) = r := by
  unfold avg
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

lemma avg_add (P : Finset ℕ) (f g : ℕ → ℝ) :
    avg P (fun n => f n + g n) = avg P f + avg P g := by
  unfold avg; rw [← add_div, Finset.sum_add_distrib]

lemma avg_smul (P : Finset ℕ) (r : ℝ) (f : ℕ → ℝ) :
    avg P (fun n => r * f n) = r * avg P f := by
  unfold avg; rw [← Finset.mul_sum, mul_div_assoc]

lemma avg_sub (P : Finset ℕ) (f g : ℕ → ℝ) :
    avg P (fun n => f n - g n) = avg P f - avg P g := by
  have := avg_add P f (fun n => -g n)
  rw [show avg P (fun n => -g n) = -avg P g by
    have := avg_smul P (-1) g; simpa using this] at this
  simpa [sub_eq_add_neg] using this

/-- Two divisibility events at distinct shifts are disjoint unless `p` divides the shift gap. -/
lemma not_both_dvd {p : ℕ} {r r' : ℤ} (h : ¬ (p : ℤ) ∣ (r - r')) (n : ℤ) :
    ¬ ((p : ℤ) ∣ n + r ∧ (p : ℤ) ∣ n + r') := by
  rintro ⟨h1, h2⟩
  exact h (by simpa using dvd_sub h1 h2)

/-- **Centred indicators of disjoint events are negatively correlated, exactly.**  If the two
events never co-occur on the sample and each has exact sample frequency, the centred product
averages to `−a·b`. -/
theorem avg_centred_mul_of_disjoint (P : Finset ℕ) (hP : P.Nonempty)
    (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]
    (hdisj : ∀ n, ¬ (A n ∧ B n)) {a b : ℝ}
    (hA : avg P (fun n => if A n then (1 : ℝ) else 0) = a)
    (hB : avg P (fun n => if B n then (1 : ℝ) else 0) = b) :
    avg P (fun n => ((if A n then (1 : ℝ) else 0) - a) * ((if B n then (1 : ℝ) else 0) - b))
      = -(a * b) := by
  classical
  have hzero : ∀ n, (if A n then (1 : ℝ) else 0) * (if B n then (1 : ℝ) else 0) = 0 := by
    intro n
    by_cases hAn : A n
    · by_cases hBn : B n
      · exact absurd ⟨hAn, hBn⟩ (hdisj n)
      · rw [if_neg hBn, mul_zero]
    · rw [if_neg hAn, zero_mul]
  have hpt : ∀ n, ((if A n then (1 : ℝ) else 0) - a) * ((if B n then (1 : ℝ) else 0) - b)
      = -(b * (if A n then (1 : ℝ) else 0)) + (-(a * (if B n then (1 : ℝ) else 0)) + a * b) := by
    intro n
    have := hzero n
    nlinarith [this]
  rw [show (fun n => ((if A n then (1 : ℝ) else 0) - a) * ((if B n then (1 : ℝ) else 0) - b))
      = (fun n => -(b * (if A n then (1 : ℝ) else 0))
          + (-(a * (if B n then (1 : ℝ) else 0)) + a * b)) from funext hpt]
  rw [avg_add, avg_add]
  rw [show (fun n => -(b * (if A n then (1 : ℝ) else 0)))
      = (fun n => (-b) * (if A n then (1 : ℝ) else 0)) from funext fun n => by ring]
  rw [show (fun n => -(a * (if B n then (1 : ℝ) else 0)))
      = (fun n => (-a) * (if B n then (1 : ℝ) else 0)) from funext fun n => by ring]
  rw [avg_smul, avg_smul, avg_const P hP, hA, hB]
  ring

/-- The same-prime cross term at distinct shifts is **non-positive** unless `p` divides the shift
gap: the only positive correlation in input (2) comes from `p ∣ ρ_i − ρ_j`. -/
theorem avg_centred_dvd_nonpos (P : Finset ℕ) (hP : P.Nonempty) {p : ℕ} {r r' : ℤ}
    (hgap : ¬ (p : ℤ) ∣ (r - r')) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : avg P (fun n => if (p : ℤ) ∣ (n : ℤ) + r then (1 : ℝ) else 0) = a)
    (hB : avg P (fun n => if (p : ℤ) ∣ (n : ℤ) + r' then (1 : ℝ) else 0) = b) :
    avg P (fun n => ((if (p : ℤ) ∣ (n : ℤ) + r then (1 : ℝ) else 0) - a) *
      ((if (p : ℤ) ∣ (n : ℤ) + r' then (1 : ℝ) else 0) - b)) ≤ 0 := by
  classical
  rw [avg_centred_mul_of_disjoint P hP _ _ (fun n => not_both_dvd hgap (n : ℤ)) hA hB]
  nlinarith

end NormalNumbers.G4.RowVariance
