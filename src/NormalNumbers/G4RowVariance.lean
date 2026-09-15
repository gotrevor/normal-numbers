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



/-! ### Input (1) is an identity, not an estimate

The per-term non-degeneracy `v` of `rowVariance_half` looks like an analytic lower bound.  It is
not: for a sum of *centred indicators* that are pairwise independent on the sample, the second
moment is **exactly** `Σ_p a_p(1 − a_p)` (`avg_sq_centred_sum`).  The two facts doing the work are
elementary — an indicator is idempotent (`X² = X`, so the diagonal term is `a_p − a_p²`), and
pairwise independence kills every off-diagonal term outright.

At a single shift the pairwise input is exactly CRT: `1[p ∣ n+ρ]·1[q ∣ n+ρ] = 1[pq ∣ n+ρ]` and
`a_{pq} = a_p a_q` along a progression whose modulus is coprime to `pq`.  With `a_p = 1/p` over the
rough primes `T < p ≤ R` this gives `v = Σ_p (1/p)(1 − 1/p) ≍ log(log R / log T) > 0`.

So input (1) reduces to the same CRT frequency statement input (2) needs — the two inputs are one
input. -/

lemma avg_double_sum' (P : Finset ℕ) (S : Finset ι) (F : ι → ι → ℕ → ℝ) :
    avg P (fun n => ∑ i ∈ S, ∑ j ∈ S, F i j n) = ∑ i ∈ S, ∑ j ∈ S, avg P (F i j) := by
  unfold avg
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_div]

/-- **The second moment of a centred indicator sum is an identity.**  Pairwise independence on the
sample plus idempotence give `avg (Σ (X_i − a_i))² = Σ a_i(1 − a_i)` exactly. -/
theorem avg_sq_centred_sum (P : Finset ℕ) (hP : P.Nonempty) (S : Finset ι)
    (X : ι → ℕ → ℝ) (a : ι → ℝ)
    (hidem : ∀ i ∈ S, ∀ n, X i n * X i n = X i n)
    (hfreq : ∀ i ∈ S, avg P (X i) = a i)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → avg P (fun n => X i n * X j n) = a i * a j) :
    avg P (fun n => (∑ i ∈ S, (X i n - a i)) ^ 2) = ∑ i ∈ S, (a i - (a i) ^ 2) := by
  classical
  have hpt : ∀ n, (∑ i ∈ S, (X i n - a i)) ^ 2
      = ∑ i ∈ S, ∑ j ∈ S, (X i n - a i) * (X j n - a j) := by
    intro n
    rw [sq, Finset.sum_mul_sum]
  rw [show (fun n => (∑ i ∈ S, (X i n - a i)) ^ 2)
      = (fun n => ∑ i ∈ S, ∑ j ∈ S, (X i n - a i) * (X j n - a j)) from funext hpt,
    avg_double_sum' P S (fun i j n => (X i n - a i) * (X j n - a j))]
  -- each entry of the double sum
  have hentry : ∀ i ∈ S, ∀ j ∈ S,
      avg P (fun n => (X i n - a i) * (X j n - a j))
        = if i = j then a i - (a i) ^ 2 else 0 := by
    intro i hi j hj
    have hexp : (fun n => (X i n - a i) * (X j n - a j))
        = (fun n => X i n * X j n
            + ((-(a j)) * X i n + ((-(a i)) * X j n + a i * a j))) := by
      funext n; ring
    rw [hexp, avg_add, avg_add, avg_add, avg_smul, avg_smul, avg_const P hP,
      hfreq i hi, hfreq j hj]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have : avg P (fun n => X i n * X i n) = a i := by
        rw [show (fun n => X i n * X i n) = X i from funext fun n => hidem i hi n]
        exact hfreq i hi
      rw [this]; ring
    · rw [if_neg hij, hpair i hi j hj hij]; ring
  rw [Finset.sum_congr rfl fun i hi =>
    Finset.sum_congr rfl fun j hj => hentry i hi j hj]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_ite_eq S i (fun _ => a i - (a i) ^ 2), if_pos hi]

/-- The packaged non-degeneracy: with pairwise-independent centred indicators, the per-term second
moment is bounded below by `Σ a_i(1 − a_i)` — input (1) of `rowVariance_half`, discharged into the
same CRT frequency statement input (2) needs. -/
theorem avg_sq_centred_sum_ge (P : Finset ℕ) (hP : P.Nonempty) (S : Finset ι)
    (X : ι → ℕ → ℝ) (a : ι → ℝ) {v : ℝ}
    (hidem : ∀ i ∈ S, ∀ n, X i n * X i n = X i n)
    (hfreq : ∀ i ∈ S, avg P (X i) = a i)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → avg P (fun n => X i n * X j n) = a i * a j)
    (hv : v ≤ ∑ i ∈ S, (a i - (a i) ^ 2)) :
    v ≤ avg P (fun n => (∑ i ∈ S, (X i n - a i)) ^ 2) := by
  rw [avg_sq_centred_sum P hP S X a hidem hfreq hpair]; exact hv


/-! ### The remaining input, base case: frequencies on the sample are exact to `O(1/N)`

Laps 137–139 reduced all of (E) to one statement: exact CRT frequencies for rough primes and
their pairwise products along the sample.  Over a full interval that statement is not an estimate
either — mathlib's interval counts give it with an explicit `O(1)` error:

* `card_filter_modEq_sub_le` — `|#{x < N : x ≡ v [MOD m]} − N/m| ≤ 1`, from the exact ceiling
  formula `Nat.count_modEq_card_eq_ceil`;
* `avg_indicator_modEq_sub_le` — hence the sample frequency of a congruence class differs from
  `1/m` by at most `1/N`.

Applied with `m = p` this is `a_p = 1/p + O(1/N)`; with `m = pq` (legitimate exactly when
`p ≠ q`, by CRT) it is `a_{pq} = 1/(pq) + O(1/N)`, which is the pairwise independence
`avg_sq_centred_sum` consumes.  On the schedule the sample is a progression `n ≡ c [MOD Q]` rather
than an interval; re-indexing `n = c + Qk` turns `p ∣ n + ρ` into a congruence on `k` (using
`gcd(p, Q) = 1`) and returns to exactly this lemma with `N` the number of `k`'s. -/

theorem card_filter_modEq_sub_le {m : ℕ} (hm : 0 < m) (N v : ℕ) :
    |((((Finset.range N).filter (fun x => x ≡ v [MOD m])).card : ℝ)) - (N : ℝ) / m| ≤ 1 := by
  classical
  set r := v % m with hr
  have hcount : ((((Finset.range N).filter (fun x => x ≡ v [MOD m])).card : ℤ) : ℚ)
      = ((⌈((N : ℚ) - (r : ℕ)) / (m : ℚ)⌉ : ℤ) : ℚ) := by
    have h := Nat.count_modEq_card_eq_ceil N hm v
    rw [Nat.count_eq_card_filter_range] at h
    exact_mod_cast h
  have hm0 : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  set x : ℚ := ((N : ℚ) - (r : ℕ)) / (m : ℚ) with hx
  have hx1 : x ≤ (⌈x⌉ : ℚ) := Int.le_ceil _
  have hx2 : (⌈x⌉ : ℚ) < x + 1 := Int.ceil_lt_add_one _
  have hsplit : x = (N : ℚ) / m - (r : ℚ) / m := by rw [hx, sub_div]
  have hrm0 : (0 : ℚ) ≤ (r : ℚ) / m := by positivity
  have hrm1 : (r : ℚ) / m ≤ 1 := by
    rw [div_le_one hm0]
    exact_mod_cast (Nat.mod_lt _ hm).le
  have hQ : |((((Finset.range N).filter (fun x => x ≡ v [MOD m])).card : ℚ)) - (N : ℚ) / m| ≤ 1 := by
    have hc : ((((Finset.range N).filter (fun x => x ≡ v [MOD m])).card : ℚ)) = (⌈x⌉ : ℚ) := by
      rw [← hcount]; norm_cast
    rw [hc, abs_le]
    constructor <;> linarith [hx1, hx2, hsplit, hrm0, hrm1]
  have := hQ
  rw [abs_le] at this ⊢
  constructor
  · have h1 := this.1
    have : ((-1 : ℚ) : ℝ) ≤ (((((Finset.range N).filter (fun x => x ≡ v [MOD m])).card : ℚ))
        - (N : ℚ) / m : ℚ) := by exact_mod_cast h1
    push_cast at this
    linarith
  · have h2 := this.2
    have : ((((((Finset.range N).filter (fun x => x ≡ v [MOD m])).card : ℚ))
        - (N : ℚ) / m : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by exact_mod_cast h2
    push_cast at this
    linarith

/-- The sample frequency of a congruence class on `range N` is `1/m` up to `1/N`. -/
theorem avg_indicator_modEq_sub_le {m : ℕ} (hm : 0 < m) {N : ℕ} (hN : 0 < N) (v : ℕ) :
    |avg (Finset.range N) (fun n => if n ≡ v [MOD m] then (1 : ℝ) else 0) - 1 / m| ≤ 1 / N := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : avg (Finset.range N) (fun n => if n ≡ v [MOD m] then (1 : ℝ) else 0)
      = ((((Finset.range N).filter (fun x => x ≡ v [MOD m])).card : ℝ)) / N := by
    unfold avg
    simp [Finset.sum_boole, Finset.card_range]
  rw [hcard]
  have hsub : ((((Finset.range N).filter (fun x => x ≡ v [MOD m])).card : ℝ)) / N - 1 / m
      = (((((Finset.range N).filter (fun x => x ≡ v [MOD m])).card : ℝ)) - (N : ℝ) / m) / N := by
    field_simp
  rw [hsub, abs_div, abs_of_pos hN0, div_le_div_iff_of_pos_right hN0]
  exact card_filter_modEq_sub_le hm N v


/-! ### The identity with approximate frequencies

`avg_sq_centred_sum` assumed the sample frequencies were exact.  `avg_indicator_modEq_sub_le`
delivers them only to `O(1/N)`, so the identity is relaxed here to an inequality carrying explicit
slack `δ`.  The proof is the same expansion: the diagonal loses `δ` (idempotence still gives
`a_i − a_i²` up to the frequency error), and each off-diagonal entry, instead of vanishing, is
bounded below by `−3δ` once the `a_i` are genuine frequencies in `[0,1]`. -/

theorem avg_sq_centred_sum_approx (P : Finset ℕ) (hP : P.Nonempty) (S : Finset ι)
    (X : ι → ℕ → ℝ) (a : ι → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hidem : ∀ i ∈ S, ∀ n, X i n * X i n = X i n)
    (ha : ∀ i ∈ S, 0 ≤ a i ∧ a i ≤ 1)
    (hfreq : ∀ i ∈ S, |avg P (X i) - a i| ≤ δ)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → |avg P (fun n => X i n * X j n) - a i * a j| ≤ δ) :
    (∑ i ∈ S, (a i - (a i) ^ 2)) - 3 * δ * (S.card : ℝ) ^ 2
      ≤ avg P (fun n => (∑ i ∈ S, (X i n - a i)) ^ 2) := by
  classical
  have hpt : ∀ n, (∑ i ∈ S, (X i n - a i)) ^ 2
      = ∑ i ∈ S, ∑ j ∈ S, (X i n - a i) * (X j n - a j) := fun n => by
    rw [sq, Finset.sum_mul_sum]
  rw [show (fun n => (∑ i ∈ S, (X i n - a i)) ^ 2)
      = (fun n => ∑ i ∈ S, ∑ j ∈ S, (X i n - a i) * (X j n - a j)) from funext hpt,
    avg_double_sum' P S (fun i j n => (X i n - a i) * (X j n - a j))]
  have hentry : ∀ i ∈ S, ∀ j ∈ S,
      (if i = j then a i - (a i) ^ 2 - δ else -(3 * δ))
        ≤ avg P (fun n => (X i n - a i) * (X j n - a j)) := by
    intro i hi j hj
    have hexp : (fun n => (X i n - a i) * (X j n - a j))
        = (fun n => X i n * X j n
            + ((-(a j)) * X i n + ((-(a i)) * X j n + a i * a j))) := funext fun n => by ring
    rw [hexp, avg_add, avg_add, avg_add, avg_smul, avg_smul, avg_const P hP]
    obtain ⟨hai0, hai1⟩ := ha i hi
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl,
        show avg P (fun n => X i n * X i n) = avg P (X i) from by
          rw [show (fun n => X i n * X i n) = X i from funext fun n => hidem i hi n]]
      have h1 := hfreq i hi
      rw [abs_le] at h1
      nlinarith [h1.1, h1.2]
    · rw [if_neg hij]
      obtain ⟨haj0, haj1⟩ := ha j hj
      have h1 := hfreq i hi
      have h2 := hfreq j hj
      have h3 := hpair i hi j hj hij
      rw [abs_le] at h1 h2 h3
      nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  have hsum : ∑ i ∈ S, ∑ j ∈ S, (if i = j then a i - (a i) ^ 2 - δ else -(3 * δ))
      ≤ ∑ i ∈ S, ∑ j ∈ S, avg P (fun n => (X i n - a i) * (X j n - a j)) :=
    Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hentry i hi j hj
  refine le_trans ?_ hsum
  -- evaluate the left-hand double sum
  have hinner : ∀ i ∈ S, ∑ j ∈ S, (if i = j then a i - (a i) ^ 2 - δ else -(3 * δ))
      = (-(3 * δ)) * (S.card : ℝ) + ((a i - (a i) ^ 2 - δ) - (-(3 * δ))) := by
    intro i hi
    have hre : ∀ j : ι, (if i = j then a i - (a i) ^ 2 - δ else -(3 * δ))
        = (-(3 * δ)) + (if i = j then (a i - (a i) ^ 2 - δ) - (-(3 * δ)) else 0) := by
      intro j; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun j _ => hre j), Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_ite_eq S i (fun _ => (a i - (a i) ^ 2 - δ) - (-(3 * δ))), if_pos hi,
      nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcard : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
  have hsplit : ∑ i ∈ S, ((a i - (a i) ^ 2 - δ) - (-(3 * δ)))
      = (∑ i ∈ S, (a i - (a i) ^ 2)) + 2 * δ * (S.card : ℝ) := by
    have hre : ∀ i : ι, ((a i - (a i) ^ 2 - δ) - (-(3 * δ)))
        = (a i - (a i) ^ 2) + 2 * δ := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hre i), Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul]
    ring
  rw [hsplit]
  nlinarith [hcard, hδ]

end NormalNumbers.G4.RowVariance
