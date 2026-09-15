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

open NormalNumbers.G4.RowBalance

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

omit [Fintype ι] in
lemma avg_double_sum' (P : Finset ℕ) (S : Finset ι) (F : ι → ι → ℕ → ℝ) :
    avg P (fun n => ∑ i ∈ S, ∑ j ∈ S, F i j n) = ∑ i ∈ S, ∑ j ∈ S, avg P (F i j) := by
  unfold avg
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_div]

omit [Fintype ι] in
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

omit [Fintype ι] in
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

omit [Fintype ι] in
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


/-! ### The progression re-indexing: the schedule's sample is an interval in disguise

The schedule samples a progression `n ≡ c [MOD Q]`, not an interval.  Writing `n = c + Q k`, the
condition `p ∣ n + ρ` becomes a single congruence on `k` whenever `gcd(Q, p) = 1` — which the
frozen modulus supplies — so every frequency on the schedule's sample is a frequency on `range N`
and `avg_indicator_modEq_sub_le` applies verbatim.  That closes the last gap in (E). -/

/-- Averaging over a progression sample is averaging over the index range. -/
lemma avg_image_progression (c Q N : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ) :
    avg ((Finset.range N).image (fun k => c + Q * k)) f
      = avg (Finset.range N) (fun k => f (c + Q * k)) := by
  classical
  have hinj : Set.InjOn (fun k => c + Q * k) (Finset.range N) := by
    intro x _ y _ h
    simp only at h
    have : Q * x = Q * y := by omega
    exact Nat.eq_of_mul_eq_mul_left hQ this
  unfold avg
  rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h),
    Finset.card_image_of_injOn hinj]

/-- **The shifted divisibility condition on a progression is one congruence class in the index.** -/
theorem exists_class_of_coprime {p Q : ℕ} (hp : 0 < p) (hcop : Nat.Coprime Q p) (c : ℕ) (r : ℤ) :
    ∃ w : ℕ, ∀ k : ℕ, ((p : ℤ) ∣ ((c : ℤ) + Q * k + r) ↔ k ≡ w [MOD p]) := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have hQu : IsUnit ((Q : ℕ) : ZMod p) := (ZMod.isUnit_iff_coprime Q p).2 hcop
  obtain ⟨u, hu⟩ := hQu
  set z : ZMod p := (↑u⁻¹ : ZMod p) * (-((c : ZMod p) + (r : ZMod p))) with hz
  refine ⟨z.val, fun k => ?_⟩
  have hcast : (((c : ℤ) + Q * k + r : ℤ) : ZMod p)
      = (Q : ZMod p) * (k : ZMod p) + ((c : ZMod p) + (r : ZMod p)) := by
    push_cast; ring
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hcast]
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.cast_id]
  constructor
  · intro h
    have hk : (Q : ZMod p) * (k : ZMod p) = -((c : ZMod p) + (r : ZMod p)) := by linear_combination h
    rw [hz, ← hk, ← hu]
    rw [← mul_assoc]
    rw [show (↑u⁻¹ : ZMod p) * (↑u : ZMod p) = 1 from by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
    rw [one_mul]
  · intro h
    rw [h, hz, ← hu, ← mul_assoc]
    rw [show (↑u : ZMod p) * (↑u⁻¹ : ZMod p) = 1 from by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]]
    rw [one_mul]; ring

/-- **The frequency statement on the schedule's sample.**  On a progression `n ≡ c [MOD Q]` with
`gcd(Q, p) = 1`, the sample frequency of `p ∣ n + ρ` is `1/p` up to `1/N`. -/
theorem avg_indicator_dvd_progression {p Q : ℕ} (hp : 0 < p) (hQ : 0 < Q)
    (hcop : Nat.Coprime Q p) (c : ℕ) (r : ℤ) {N : ℕ} (hN : 0 < N) :
    |avg ((Finset.range N).image (fun k => c + Q * k))
        (fun n => if (p : ℤ) ∣ ((n : ℤ) + r) then (1 : ℝ) else 0) - 1 / p| ≤ 1 / N := by
  classical
  obtain ⟨w, hw⟩ := exists_class_of_coprime hp hcop c r
  rw [avg_image_progression c Q N hQ]
  have hre : (fun k => if (p : ℤ) ∣ (((c + Q * k : ℕ) : ℤ) + r) then (1 : ℝ) else 0)
      = (fun k => if k ≡ w [MOD p] then (1 : ℝ) else 0) := by
    funext k
    have : ((p : ℤ) ∣ (((c + Q * k : ℕ) : ℤ) + r)) ↔ k ≡ w [MOD p] := by
      rw [show (((c + Q * k : ℕ) : ℤ) + r) = ((c : ℤ) + Q * k + r) from by push_cast; ring]
      exact hw k
    by_cases h : k ≡ w [MOD p]
    · rw [if_pos (this.2 h), if_pos h]
    · rw [if_neg (fun hc => h (this.1 hc)), if_neg h]
  rw [hre]
  exact avg_indicator_modEq_sub_le hp hN w


/-! ### Assembly: the rough-prime variance on the schedule's sample

Everything above is now instantiated at the real object.  `S` is a finite set of rough primes,
pairwise coprime and coprime to the frozen modulus `Q`; the sample is the progression
`{c + Qk : k < N}`; the fluctuation at shift `r` is `X_p(n) = 1[p ∣ n + r] − 1/p`.  The two
hypotheses `avg_sq_centred_sum_approx` needs are supplied by `avg_indicator_dvd_progression`:
singly at modulus `p`, and pairwise at modulus `p·q` — legitimate because `p ∣ m ∧ q ∣ m ↔ pq ∣ m`
for coprime `p, q`. -/

theorem rough_variance_lower {Q c N : ℕ} (hQ : 0 < Q) (hN : 0 < N) (r : ℤ)
    (S : Finset ℕ) (hpos : ∀ p ∈ S, 0 < p)
    (hQcop : ∀ p ∈ S, Nat.Coprime Q p)
    (hcop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) :
    (∑ p ∈ S, ((1 : ℝ) / p - ((1 : ℝ) / p) ^ 2)) - 3 * (1 / (N : ℝ)) * (S.card : ℝ) ^ 2
      ≤ avg ((Finset.range N).image (fun k => c + Q * k))
          (fun n => (∑ p ∈ S, ((if (p : ℤ) ∣ ((n : ℤ) + r) then (1 : ℝ) else 0) - 1 / p)) ^ 2) := by
  classical
  set P := (Finset.range N).image (fun k => c + Q * k) with hPdef
  have hPne : P.Nonempty := by
    refine ⟨c + Q * 0, Finset.mem_image.2 ⟨0, Finset.mem_range.2 hN, rfl⟩⟩
  have hδ : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  refine avg_sq_centred_sum_approx P hPne S
    (fun p n => if (p : ℤ) ∣ ((n : ℤ) + r) then (1 : ℝ) else 0) (fun p => 1 / p) hδ
    (fun p _ n => by split_ifs <;> norm_num) (fun p hp => ?_) (fun p hp => ?_) (fun p hp q hq hne => ?_)
  · have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpos p hp
    constructor
    · positivity
    · rw [div_le_one (by linarith)]; linarith
  · exact avg_indicator_dvd_progression (hpos p hp) hQ (hQcop p hp) c r hN
  · -- the pair indicator is the indicator of divisibility by `p * q`
    have hpq : ∀ n : ℕ, ((if (p : ℤ) ∣ ((n : ℤ) + r) then (1 : ℝ) else 0)
        * (if (q : ℤ) ∣ ((n : ℤ) + r) then (1 : ℝ) else 0))
        = if ((p * q : ℕ) : ℤ) ∣ ((n : ℤ) + r) then (1 : ℝ) else 0 := by
      intro n
      have hiff : ((p : ℤ) ∣ ((n : ℤ) + r) ∧ (q : ℤ) ∣ ((n : ℤ) + r))
          ↔ ((p * q : ℕ) : ℤ) ∣ ((n : ℤ) + r) := by
        constructor
        · rintro ⟨h1, h2⟩
          have hcz : IsCoprime (p : ℤ) (q : ℤ) :=
            Nat.isCoprime_iff_coprime.2 (hcop p hp q hq hne)
          push_cast
          exact hcz.mul_dvd h1 h2
        · intro h
          push_cast at h
          exact ⟨dvd_trans (Dvd.intro _ rfl) h, dvd_trans (Dvd.intro_left _ rfl) h⟩
      by_cases h1 : (p : ℤ) ∣ ((n : ℤ) + r)
      · by_cases h2 : (q : ℤ) ∣ ((n : ℤ) + r)
        · rw [if_pos h1, if_pos h2, if_pos (hiff.1 ⟨h1, h2⟩)]; norm_num
        · rw [if_pos h1, if_neg h2, if_neg (fun hc => h2 (hiff.2 hc).2)]; norm_num
      · rw [if_neg h1, if_neg (fun hc => h1 (hiff.2 hc).1)]; norm_num
    rw [show (fun n : ℕ => (if (p : ℤ) ∣ ((n : ℤ) + r) then (1 : ℝ) else 0)
        * (if (q : ℤ) ∣ ((n : ℤ) + r) then (1 : ℝ) else 0))
        = (fun n : ℕ => if ((p * q : ℕ) : ℤ) ∣ ((n : ℤ) + r) then (1 : ℝ) else 0) from
      funext (fun n => hpq n)]
    have hmul : (1 : ℝ) / p * (1 / q) = 1 / ((p * q : ℕ) : ℝ) := by push_cast; ring
    rw [hmul]
    exact avg_indicator_dvd_progression (Nat.mul_pos (hpos p hp) (hpos q hq)) hQ
      ((hQcop p hp).mul_right (hQcop q hq)) c r hN


/-! ### Joint frequencies at *distinct* shifts

The cross-shift correlation `ε` of `rowVariance_half` needs the joint frequency of
`p ∣ n + r` and `q ∣ n + r'` for `p ≠ q` and *different* shifts.  That is no longer a single
divisibility, but by CRT it is still a single congruence class — mod `p·q` — so the same interval
count applies. -/

/-- Two congruence conditions at coprime moduli are one congruence class mod the product. -/
lemma exists_class_of_two {p q : ℕ} (hpq : Nat.Coprime p q) (w w' : ℕ) :
    ∃ w'' : ℕ, ∀ k : ℕ, ((k ≡ w [MOD p] ∧ k ≡ w' [MOD q]) ↔ k ≡ w'' [MOD (p * q)]) := by
  refine ⟨(Nat.chineseRemainder hpq w w' : ℕ), fun k => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact Nat.chineseRemainder_modEq_unique hpq h.1 h.2
  · have h1 : k ≡ (Nat.chineseRemainder hpq w w' : ℕ) [MOD p] :=
      h.of_dvd (Dvd.intro _ rfl)
    have h2 : k ≡ (Nat.chineseRemainder hpq w w' : ℕ) [MOD q] :=
      h.of_dvd (Dvd.intro_left _ rfl)
    exact ⟨h1.trans (Nat.chineseRemainder hpq w w').prop.1,
      h2.trans (Nat.chineseRemainder hpq w w').prop.2⟩

/-- **The joint frequency at distinct shifts.**  On the progression sample, the frequency of
`p ∣ n + r` and `q ∣ n + r'` together is `1/(pq)` up to `1/N`. -/
theorem avg_indicator_dvd_two_progression {p q Q : ℕ} (hp : 0 < p) (hq : 0 < q) (hQ : 0 < Q)
    (hpq : Nat.Coprime p q) (hQp : Nat.Coprime Q p) (hQq : Nat.Coprime Q q)
    (c : ℕ) (r r' : ℤ) {N : ℕ} (hN : 0 < N) :
    |avg ((Finset.range N).image (fun k => c + Q * k))
        (fun n => (if (p : ℤ) ∣ ((n : ℤ) + r) then (1 : ℝ) else 0)
          * (if (q : ℤ) ∣ ((n : ℤ) + r') then (1 : ℝ) else 0))
      - 1 / ((p * q : ℕ) : ℝ)| ≤ 1 / N := by
  classical
  obtain ⟨w, hw⟩ := exists_class_of_coprime hp hQp c r
  obtain ⟨w', hw'⟩ := exists_class_of_coprime hq hQq c r'
  obtain ⟨w'', hw''⟩ := exists_class_of_two hpq w w'
  rw [avg_image_progression c Q N hQ]
  have hre : (fun k : ℕ => (if (p : ℤ) ∣ (((c + Q * k : ℕ) : ℤ) + r) then (1 : ℝ) else 0)
      * (if (q : ℤ) ∣ (((c + Q * k : ℕ) : ℤ) + r') then (1 : ℝ) else 0))
      = (fun k : ℕ => if k ≡ w'' [MOD (p * q)] then (1 : ℝ) else 0) := by
    funext k
    have e1 : ((p : ℤ) ∣ (((c + Q * k : ℕ) : ℤ) + r)) ↔ k ≡ w [MOD p] := by
      rw [show (((c + Q * k : ℕ) : ℤ) + r) = ((c : ℤ) + Q * k + r) from by push_cast; ring]
      exact hw k
    have e2 : ((q : ℤ) ∣ (((c + Q * k : ℕ) : ℤ) + r')) ↔ k ≡ w' [MOD q] := by
      rw [show (((c + Q * k : ℕ) : ℤ) + r') = ((c : ℤ) + Q * k + r') from by push_cast; ring]
      exact hw' k
    by_cases h1 : k ≡ w [MOD p]
    · by_cases h2 : k ≡ w' [MOD q]
      · rw [if_pos (e1.2 h1), if_pos (e2.2 h2), if_pos ((hw'' k).1 ⟨h1, h2⟩)]; norm_num
      · rw [if_pos (e1.2 h1), if_neg (fun hc => h2 (e2.1 hc)),
          if_neg (fun hc => h2 ((hw'' k).2 hc).2)]; norm_num
    · rw [if_neg (fun hc => h1 (e1.1 hc)), if_neg (fun hc => h1 ((hw'' k).2 hc).1)]; norm_num
  rw [hre]
  exact avg_indicator_modEq_sub_le (Nat.mul_pos hp hq) hN w''



/-- Numeric core, diagonal case: `|c − uA − uB + u²| ≤ 4u + 3e`. -/
private lemma abs_diag_bound {u e A B c : ℝ} (hu : 0 < u)
    (hsq : u * u ≤ u) (hsq0 : 0 ≤ u * u)
    (hqA1 : u * A ≤ u * u + e) (hqA2 : u * u - e ≤ u * A)
    (hpB1 : u * B ≤ u * u + e) (hpB2 : u * u - e ≤ u * B)
    (hc1 : -e ≤ c) (hc2 : c ≤ u + e) :
    |c + (-u * A + (-u * B + u * u))| ≤ 4 * u + 3 * e := by
  rw [abs_le]
  constructor <;> nlinarith

/-- Numeric core, disjoint diagonal case: `|−uA − uB + u²| ≤ 3u² + 3e`. -/
private lemma abs_disj_bound {u e A B : ℝ} (hsq0 : 0 ≤ u * u)
    (hqA1 : u * A ≤ u * u + e) (hqA2 : u * u - e ≤ u * A)
    (hpB1 : u * B ≤ u * u + e) (hpB2 : u * u - e ≤ u * B) :
    |(0 : ℝ) + (-u * A + (-u * B + u * u))| ≤ 3 * (u * u) + 3 * e := by
  rw [abs_le]
  constructor <;> nlinarith

/-- Numeric core, off-diagonal case: `|C − vA − uB + uv| ≤ 3e`. -/
private lemma abs_offdiag_bound {u v e A B C : ℝ}
    (hC1 : u * v - e ≤ C) (hC2 : C ≤ u * v + e)
    (hqA1 : v * A ≤ u * v + e) (hqA2 : u * v - e ≤ v * A)
    (hpB1 : u * B ≤ u * v + e) (hpB2 : u * v - e ≤ u * B) :
    |C + (-v * A + (-u * B + u * v))| ≤ 3 * e := by
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The cross-shift correlation bound

Summing the three-case table: the `p = q` diagonal carries everything (`4/p` when `p` divides the
shift gap, `3/p²` when it does not — the disjoint case, which is where `not_both_dvd` pays off),
and every off-diagonal pair costs only the frequency error `3/N`. -/

theorem cross_shift_corr_le {Q c N : ℕ} (hQ : 0 < Q) (hN : 0 < N) (r r' : ℤ)
    (S : Finset ℕ) (hpos : ∀ p ∈ S, 0 < p)
    (hQcop : ∀ p ∈ S, Nat.Coprime Q p)
    (hcop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) :
    |avg ((Finset.range N).image (fun k => c + Q * k))
        (fun n => (∑ p ∈ S, ((if (p : ℤ) ∣ ((n : ℤ) + r) then (1 : ℝ) else 0) - 1 / p))
          * (∑ q ∈ S, ((if (q : ℤ) ∣ ((n : ℤ) + r') then (1 : ℝ) else 0) - 1 / q)))|
      ≤ (∑ p ∈ S, (if (p : ℤ) ∣ (r - r') then 4 * (1 / (p : ℝ)) else 3 * (1 / (p : ℝ)) ^ 2))
          + 3 * (S.card : ℝ) ^ 2 / N := by
  classical
  set P := (Finset.range N).image (fun k => c + Q * k) with hPdef
  have hPne : P.Nonempty := ⟨c + Q * 0, Finset.mem_image.2 ⟨0, Finset.mem_range.2 hN, rfl⟩⟩
  set I : ℕ → ℤ → ℕ → ℝ := fun p t n => if (p : ℤ) ∣ ((n : ℤ) + t) then (1 : ℝ) else 0 with hI
  have hpt : ∀ n, (∑ p ∈ S, (I p r n - 1 / p)) * (∑ q ∈ S, (I q r' n - 1 / q))
      = ∑ p ∈ S, ∑ q ∈ S, (I p r n - 1 / p) * (I q r' n - 1 / q) := fun n => by
    rw [Finset.sum_mul_sum]
  rw [show (fun n => (∑ p ∈ S, (I p r n - 1 / p)) * (∑ q ∈ S, (I q r' n - 1 / q)))
      = (fun n => ∑ p ∈ S, ∑ q ∈ S, (I p r n - 1 / p) * (I q r' n - 1 / q)) from funext hpt,
    avg_double_sum' P S (fun p q n => (I p r n - 1 / p) * (I q r' n - 1 / q))]
  have hterm : ∀ p ∈ S, ∀ q ∈ S,
      |avg P (fun n => (I p r n - 1 / p) * (I q r' n - 1 / q))|
        ≤ (if p = q then (if (p : ℤ) ∣ (r - r') then 4 * (1 / (p : ℝ))
              else 3 * (1 / (p : ℝ)) ^ 2) else 0) + 3 / N := by
    intro p hp q hq
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpos p hp
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpos q hq
    have hup : (0 : ℝ) < 1 / p := by positivity
    have huq : (0 : ℝ) < 1 / q := by positivity
    have hup1 : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have huq1 : (1 : ℝ) / q ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have he : (0 : ℝ) < 1 / (N : ℝ) := by
      have : (0 : ℝ) < N := by exact_mod_cast hN
      positivity
    have hue : (1 / (p : ℝ)) * (1 / (N : ℝ)) ≤ 1 / (N : ℝ) := by nlinarith
    have hve : (1 / (q : ℝ)) * (1 / (N : ℝ)) ≤ 1 / (N : ℝ) := by nlinarith
    have hA := avg_indicator_dvd_progression (hpos p hp) hQ (hQcop p hp) c r hN
    have hB := avg_indicator_dvd_progression (hpos q hq) hQ (hQcop q hq) c r' hN
    rw [abs_le] at hA hB
    have hAle : avg P (I p r) ≤ 1 / (p : ℝ) + 1 / N := by
      have := hA.2; simp only [hI, hPdef]; linarith [this]
    have hAge : 1 / (p : ℝ) - 1 / N ≤ avg P (I p r) := by
      have := hA.1; simp only [hI, hPdef]; linarith [this]
    have hBle : avg P (I q r') ≤ 1 / (q : ℝ) + 1 / N := by
      have := hB.2; simp only [hI, hPdef]; linarith [this]
    have hBge : 1 / (q : ℝ) - 1 / N ≤ avg P (I q r') := by
      have := hB.1; simp only [hI, hPdef]; linarith [this]
    have hexp : avg P (fun n => (I p r n - 1 / p) * (I q r' n - 1 / q))
        = avg P (fun n => I p r n * I q r' n)
          + ((-(1 / (q : ℝ))) * avg P (I p r)
            + ((-(1 / (p : ℝ))) * avg P (I q r') + (1 / (p : ℝ)) * (1 / (q : ℝ)))) := by
      rw [show (fun n => (I p r n - 1 / p) * (I q r' n - 1 / q))
          = (fun n => I p r n * I q r' n
              + ((-(1 / (q : ℝ))) * I p r n
                + ((-(1 / (p : ℝ))) * I q r' n + (1 / (p : ℝ)) * (1 / (q : ℝ)))))
        from funext fun n => by ring]
      rw [avg_add, avg_add, avg_add, avg_smul, avg_smul, avg_const P hPne]
    rw [hexp]
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl]
      -- products, with the diagonal square as a single atom
      have hqA1 : (1 / (p : ℝ)) * avg P (I p r)
          ≤ (1 / (p : ℝ)) * (1 / (p : ℝ)) + 1 / (N : ℝ) := by
        calc (1 / (p : ℝ)) * avg P (I p r)
            ≤ (1 / (p : ℝ)) * (1 / (p : ℝ) + 1 / (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hAle hup.le
          _ = (1 / (p : ℝ)) * (1 / (p : ℝ)) + (1 / (p : ℝ)) * (1 / (N : ℝ)) := by ring
          _ ≤ (1 / (p : ℝ)) * (1 / (p : ℝ)) + 1 / (N : ℝ) := by linarith
      have hqA2 : (1 / (p : ℝ)) * (1 / (p : ℝ)) - 1 / (N : ℝ)
          ≤ (1 / (p : ℝ)) * avg P (I p r) := by
        calc (1 / (p : ℝ)) * (1 / (p : ℝ)) - 1 / (N : ℝ)
            ≤ (1 / (p : ℝ)) * (1 / (p : ℝ)) - (1 / (p : ℝ)) * (1 / (N : ℝ)) := by linarith
          _ = (1 / (p : ℝ)) * (1 / (p : ℝ) - 1 / (N : ℝ)) := by ring
          _ ≤ (1 / (p : ℝ)) * avg P (I p r) := mul_le_mul_of_nonneg_left hAge hup.le
      have hpB1 : (1 / (p : ℝ)) * avg P (I p r')
          ≤ (1 / (p : ℝ)) * (1 / (p : ℝ)) + 1 / (N : ℝ) := by
        calc (1 / (p : ℝ)) * avg P (I p r')
            ≤ (1 / (p : ℝ)) * (1 / (p : ℝ) + 1 / (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hBle hup.le
          _ = (1 / (p : ℝ)) * (1 / (p : ℝ)) + (1 / (p : ℝ)) * (1 / (N : ℝ)) := by ring
          _ ≤ (1 / (p : ℝ)) * (1 / (p : ℝ)) + 1 / (N : ℝ) := by linarith
      have hpB2 : (1 / (p : ℝ)) * (1 / (p : ℝ)) - 1 / (N : ℝ)
          ≤ (1 / (p : ℝ)) * avg P (I p r') := by
        calc (1 / (p : ℝ)) * (1 / (p : ℝ)) - 1 / (N : ℝ)
            ≤ (1 / (p : ℝ)) * (1 / (p : ℝ)) - (1 / (p : ℝ)) * (1 / (N : ℝ)) := by linarith
          _ = (1 / (p : ℝ)) * (1 / (p : ℝ) - 1 / (N : ℝ)) := by ring
          _ ≤ (1 / (p : ℝ)) * avg P (I p r') := mul_le_mul_of_nonneg_left hBge hup.le
      have hsqe : (1 / (p : ℝ)) * (1 / (p : ℝ)) = (1 / (p : ℝ)) ^ 2 := by ring
      have hsq : (1 / (p : ℝ)) ^ 2 ≤ 1 / (p : ℝ) := by nlinarith
      have hsq0 : (0 : ℝ) ≤ (1 / (p : ℝ)) ^ 2 := by positivity
      by_cases hdvd : (p : ℤ) ∣ (r - r')
      · rw [if_pos hdvd]
        have hsame : ∀ n : ℕ, I p r n * I p r' n = I p r n := by
          intro n
          have hiff : ((p : ℤ) ∣ ((n : ℤ) + r)) ↔ ((p : ℤ) ∣ ((n : ℤ) + r')) := by
            constructor
            · intro h
              rw [show ((n : ℤ) + r') = ((n : ℤ) + r) - (r - r') from by ring]
              exact dvd_sub h hdvd
            · intro h
              rw [show ((n : ℤ) + r) = ((n : ℤ) + r') + (r - r') from by ring]
              exact dvd_add h hdvd
          simp only [hI]
          by_cases h1 : (p : ℤ) ∣ ((n : ℤ) + r)
          · rw [if_pos h1, if_pos (hiff.1 h1)]; norm_num
          · rw [if_neg h1]; norm_num
        rw [show (fun n => I p r n * I p r' n) = I p r from funext hsame]
        have hsq' : (1 / (p : ℝ)) * (1 / (p : ℝ)) ≤ 1 / (p : ℝ) := by rw [hsqe]; exact hsq
        have hsq0' : (0 : ℝ) ≤ (1 / (p : ℝ)) * (1 / (p : ℝ)) := by rw [hsqe]; exact hsq0
        have := abs_diag_bound (u := 1 / (p : ℝ)) (e := 1 / (N : ℝ))
          (A := avg P (I p r)) (B := avg P (I p r')) (c := avg P (I p r))
          hup hsq' hsq0' hqA1 hqA2 hpB1 hpB2 (by linarith) (by linarith)
        calc |avg P (I p r) + (-(1 / (p : ℝ)) * avg P (I p r)
              + (-(1 / (p : ℝ)) * avg P (I p r') + 1 / (p : ℝ) * (1 / (p : ℝ))))|
            ≤ 4 * (1 / (p : ℝ)) + 3 * (1 / (N : ℝ)) := this
          _ = 4 * (1 / (p : ℝ)) + 3 / (N : ℝ) := by ring
      · rw [if_neg hdvd]
        have hzero : ∀ n : ℕ, I p r n * I p r' n = 0 := by
          intro n
          have hd := not_both_dvd (p := p) (r := r) (r' := r') hdvd (n : ℤ)
          simp only [hI]
          by_cases h1 : (p : ℤ) ∣ ((n : ℤ) + r)
          · rw [if_pos h1, if_neg (fun hc => hd ⟨h1, hc⟩)]; norm_num
          · rw [if_neg h1]; norm_num
        rw [show (fun n => I p r n * I p r' n) = (fun _ => (0 : ℝ)) from funext hzero,
          avg_const P hPne]
        have hsq0' : (0 : ℝ) ≤ (1 / (p : ℝ)) * (1 / (p : ℝ)) := by rw [hsqe]; exact hsq0
        have := abs_disj_bound (u := 1 / (p : ℝ)) (e := 1 / (N : ℝ))
          (A := avg P (I p r)) (B := avg P (I p r')) hsq0' hqA1 hqA2 hpB1 hpB2
        calc |(0 : ℝ) + (-(1 / (p : ℝ)) * avg P (I p r)
              + (-(1 / (p : ℝ)) * avg P (I p r') + 1 / (p : ℝ) * (1 / (p : ℝ))))|
            ≤ 3 * ((1 / (p : ℝ)) * (1 / (p : ℝ))) + 3 * (1 / (N : ℝ)) := this
          _ = 3 * (1 / (p : ℝ)) ^ 2 + 3 / (N : ℝ) := by rw [hsqe]; ring
    · rw [if_neg hpq, zero_add]
      have hC := avg_indicator_dvd_two_progression (hpos p hp) (hpos q hq) hQ
        (hcop p hp q hq hpq) (hQcop p hp) (hQcop q hq) c r r' hN
      rw [abs_le] at hC
      have hCle : avg P (fun n => I p r n * I q r' n)
          ≤ (1 / (p : ℝ)) * (1 / (q : ℝ)) + 1 / N := by
        have := hC.2
        have hpqinv : (1 : ℝ) / ((p * q : ℕ) : ℝ) = (1 / (p : ℝ)) * (1 / (q : ℝ)) := by
          push_cast; ring
        rw [hpqinv] at this
        simp only [hI, hPdef]; linarith [this]
      have hCge : (1 / (p : ℝ)) * (1 / (q : ℝ)) - 1 / N
          ≤ avg P (fun n => I p r n * I q r' n) := by
        have := hC.1
        have hpqinv : (1 : ℝ) / ((p * q : ℕ) : ℝ) = (1 / (p : ℝ)) * (1 / (q : ℝ)) := by
          push_cast; ring
        rw [hpqinv] at this
        simp only [hI, hPdef]; linarith [this]
      have hqA1 : (1 / (q : ℝ)) * avg P (I p r)
          ≤ (1 / (p : ℝ)) * (1 / (q : ℝ)) + 1 / (N : ℝ) := by
        calc (1 / (q : ℝ)) * avg P (I p r)
            ≤ (1 / (q : ℝ)) * (1 / (p : ℝ) + 1 / (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hAle huq.le
          _ = (1 / (p : ℝ)) * (1 / (q : ℝ)) + (1 / (q : ℝ)) * (1 / (N : ℝ)) := by ring
          _ ≤ (1 / (p : ℝ)) * (1 / (q : ℝ)) + 1 / (N : ℝ) := by linarith
      have hqA2 : (1 / (p : ℝ)) * (1 / (q : ℝ)) - 1 / (N : ℝ)
          ≤ (1 / (q : ℝ)) * avg P (I p r) := by
        calc (1 / (p : ℝ)) * (1 / (q : ℝ)) - 1 / (N : ℝ)
            ≤ (1 / (p : ℝ)) * (1 / (q : ℝ)) - (1 / (q : ℝ)) * (1 / (N : ℝ)) := by linarith
          _ = (1 / (q : ℝ)) * (1 / (p : ℝ) - 1 / (N : ℝ)) := by ring
          _ ≤ (1 / (q : ℝ)) * avg P (I p r) := mul_le_mul_of_nonneg_left hAge huq.le
      have hpB1 : (1 / (p : ℝ)) * avg P (I q r')
          ≤ (1 / (p : ℝ)) * (1 / (q : ℝ)) + 1 / (N : ℝ) := by
        calc (1 / (p : ℝ)) * avg P (I q r')
            ≤ (1 / (p : ℝ)) * (1 / (q : ℝ) + 1 / (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hBle hup.le
          _ = (1 / (p : ℝ)) * (1 / (q : ℝ)) + (1 / (p : ℝ)) * (1 / (N : ℝ)) := by ring
          _ ≤ (1 / (p : ℝ)) * (1 / (q : ℝ)) + 1 / (N : ℝ) := by linarith
      have hpB2 : (1 / (p : ℝ)) * (1 / (q : ℝ)) - 1 / (N : ℝ)
          ≤ (1 / (p : ℝ)) * avg P (I q r') := by
        calc (1 / (p : ℝ)) * (1 / (q : ℝ)) - 1 / (N : ℝ)
            ≤ (1 / (p : ℝ)) * (1 / (q : ℝ)) - (1 / (p : ℝ)) * (1 / (N : ℝ)) := by linarith
          _ = (1 / (p : ℝ)) * (1 / (q : ℝ) - 1 / (N : ℝ)) := by ring
          _ ≤ (1 / (p : ℝ)) * avg P (I q r') := mul_le_mul_of_nonneg_left hBge hup.le
      have := abs_offdiag_bound (u := 1 / (p : ℝ)) (v := 1 / (q : ℝ)) (e := 1 / (N : ℝ))
        (A := avg P (I p r)) (B := avg P (I q r'))
        (C := avg P (fun n => I p r n * I q r' n))
        (by linarith) (by linarith) hqA1 hqA2 hpB1 hpB2
      calc |avg P (fun n => I p r n * I q r' n) + (-(1 / (q : ℝ)) * avg P (I p r)
            + (-(1 / (p : ℝ)) * avg P (I q r') + 1 / (p : ℝ) * (1 / (q : ℝ))))|
          ≤ 3 * (1 / (N : ℝ)) := this
        _ = 3 / (N : ℝ) := by ring
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun p hp =>
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun q hq => hterm p hp q hq)) ?_
  have hinner : ∀ p ∈ S, ∑ q ∈ S, ((if p = q then (if (p : ℤ) ∣ (r - r') then 4 * (1 / (p : ℝ))
        else 3 * (1 / (p : ℝ)) ^ 2) else 0) + 3 / N)
      = (if (p : ℤ) ∣ (r - r') then 4 * (1 / (p : ℝ)) else 3 * (1 / (p : ℝ)) ^ 2)
        + (S.card : ℝ) * (3 / N) := by
    intro p hp
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.sum_ite_eq S p (fun _ => (if (p : ℤ) ∣ (r - r') then 4 * (1 / (p : ℝ))
        else 3 * (1 / (p : ℝ)) ^ 2)), if_pos hp]
  rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    show (S.card : ℝ) * ((S.card : ℝ) * (3 / N)) = 3 * (S.card : ℝ) ^ 2 / N from by ring]

/-! ### Assembly: the released-layer weights, and (E)

The row's released pairs are `(α, j)`: `α` ranges over the row support of `A_ν` (`m = 2^K` of
them, `|A_{να}| = 1`) and `j` over the released window `K′ < j ≤ K′ + L`.  The weight is
`c_{α,j} = A_{να} 4^{-j}`, so the two norms the reduction needs are exact geometric sums:

    Σ |c| = m · 4^{-K′}(1 − 4^{-L})/3,        Σ c² = m · 16^{-K′}(1 − 16^{-L})/15,

whence `(Σ|c|)²/Σc² = (5m/3)·(1 − 4^{-L})/(1 + 4^{-L}) ≤ 5m/3`.  Feeding that into
`rowVariance_half` at `ratio = 5m/3` produces exactly the shape of
`Budget.RoughRowVarianceLower`, with constant `c = (v/2)(1 − 16^{-L})`. -/

/-- A geometric sum with an offset exponent. -/
lemma geom_offset (r : ℝ) (hr : r ≠ 1) (a L : ℕ) :
    ∑ j ∈ Finset.range L, r ^ (a + j) = r ^ a * ((r ^ L - 1) / (r - 1)) := by
  have h : ∑ j ∈ Finset.range L, r ^ (a + j) = r ^ a * ∑ j ∈ Finset.range L, r ^ j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [pow_add]
  rw [h, geom_sum_eq hr]

/-- The `ℓ¹` norm of the released weights. -/
lemma sum_abs_released {m L K' : ℕ} (c : Fin m × Fin L → ℝ)
    (hc : ∀ i, |c i| = (1 / 4 : ℝ) ^ (K' + 1 + (i.2 : ℕ))) :
    ∑ i, |c i| = (m : ℝ) * ((1 / 4 : ℝ) ^ K' * (1 - (1 / 4 : ℝ) ^ L) / 3) := by
  have hinner : ∀ _a : Fin m, ∑ j : Fin L, |c (_a, j)|
      = (1 / 4 : ℝ) ^ K' * (1 - (1 / 4 : ℝ) ^ L) / 3 := by
    intro a
    have : ∑ j : Fin L, |c (a, j)| = ∑ j ∈ Finset.range L, (1 / 4 : ℝ) ^ (K' + 1 + j) := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => (1 / 4 : ℝ) ^ (K' + 1 + j)) L]
      exact Finset.sum_congr rfl fun j _ => hc (a, j)
    rw [this, geom_offset _ (by norm_num) (K' + 1) L, pow_succ]
    ring
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun a _ => hinner a), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- The `ℓ²` norm of the released weights. -/
lemma sum_sq_released {m L K' : ℕ} (c : Fin m × Fin L → ℝ)
    (hc : ∀ i, |c i| = (1 / 4 : ℝ) ^ (K' + 1 + (i.2 : ℕ))) :
    ∑ i, (c i) ^ 2 = (m : ℝ) * ((1 / 16 : ℝ) ^ K' * (1 - (1 / 16 : ℝ) ^ L) / 15) := by
  have hsq : ∀ i : Fin m × Fin L, (c i) ^ 2 = (1 / 16 : ℝ) ^ (K' + 1 + (i.2 : ℕ)) := by
    intro i
    have h1 : (c i) ^ 2 = |c i| ^ 2 := (sq_abs _).symm
    rw [h1, hc i, ← pow_mul, show (1 / 4 : ℝ) = (1 / 16 : ℝ) ^ (1 / 2 : ℝ) from by
      rw [show (1 / 16 : ℝ) = (1 / 4 : ℝ) ^ (2 : ℕ) from by norm_num,
        ← Real.rpow_natCast ((1 : ℝ) / 4) 2, ← Real.rpow_mul (by norm_num)]
      norm_num]
    rw [← Real.rpow_natCast (((1 : ℝ) / 16) ^ (1 / 2 : ℝ)) ((K' + 1 + (i.2 : ℕ)) * 2),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((1 : ℝ) / 16) (K' + 1 + (i.2 : ℕ))]
    congr 1
    push_cast
    ring
  have hinner : ∀ _a : Fin m, ∑ j : Fin L, (c (_a, j)) ^ 2
      = (1 / 16 : ℝ) ^ K' * (1 - (1 / 16 : ℝ) ^ L) / 15 := by
    intro a
    have : ∑ j : Fin L, (c (a, j)) ^ 2 = ∑ j ∈ Finset.range L, (1 / 16 : ℝ) ^ (K' + 1 + j) := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => (1 / 16 : ℝ) ^ (K' + 1 + j)) L]
      exact Finset.sum_congr rfl fun j _ => hsq (a, j)
    rw [this, geom_offset _ (by norm_num) (K' + 1) L, pow_succ]
    ring
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun a _ => hinner a), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- The ratio the reduction prices the correlation against: `(Σ|c|)² ≤ (5m/3) Σ c²`.
The truncation factors improve it — `(1 − x)²/(1 − x²) = (1 − x)/(1 + x) ≤ 1` — so the clean
constant `5m/3` holds for every window length. -/
lemma ratio_released {m L K' : ℕ} (c : Fin m × Fin L → ℝ)
    (hc : ∀ i, |c i| = (1 / 4 : ℝ) ^ (K' + 1 + (i.2 : ℕ))) :
    (∑ i, |c i|) ^ 2 ≤ (5 * (m : ℝ) / 3) * ∑ i, (c i) ^ 2 := by
  rw [sum_abs_released c hc, sum_sq_released c hc]
  set x : ℝ := (1 / 4 : ℝ) ^ L with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h16 : (1 / 16 : ℝ) ^ L = x ^ 2 := by
    rw [hx, ← pow_mul, mul_comm, pow_mul]; norm_num
  have h16K : (1 / 16 : ℝ) ^ K' = ((1 / 4 : ℝ) ^ K') ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  set y : ℝ := (1 / 4 : ℝ) ^ K' with hy
  have hy0 : 0 ≤ y := by positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [h16, h16K]
  -- goal: (m * (y*(1-x)/3))^2 ≤ (5m/3) * (m * (y^2*(1-x^2)/15))
  have key : ((m : ℝ) * (y * (1 - x) / 3)) ^ 2
      = (5 * (m : ℝ) / 3) * ((m : ℝ) * (y ^ 2 * (1 - x) ^ 2 / 15)) := by ring
  rw [key]
  have hfac : (1 - x) ^ 2 ≤ 1 - x ^ 2 := by nlinarith
  have hcoef : (0 : ℝ) ≤ 5 * (m : ℝ) / 3 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hcoef
  refine mul_le_mul_of_nonneg_left ?_ hm0
  have : y ^ 2 * (1 - x) ^ 2 ≤ y ^ 2 * (1 - x ^ 2) :=
    mul_le_mul_of_nonneg_left hfac (by positivity)
  linarith

/-- **The released row's second moment, bounded below.**  This is `rowVariance_half` at the
schedule's own weights: `ratio = 5m/3` with `m` the row support, so the near-orthogonality the
hypothesis asks for is `ε ≤ 3v/(20m)` — at `m = 2^K`, the `ε ≲ v 2^{-K}` of the design. -/
theorem released_row_lower {m L K' : ℕ} (P : Finset ℕ) (X : Fin m × Fin L → ℕ → ℝ)
    (c : Fin m × Fin L → ℝ) (hc : ∀ i, |c i| = (1 / 4 : ℝ) ^ (K' + 1 + (i.2 : ℕ)))
    {v ε : ℝ} (hε : 0 ≤ ε) (hv : 0 ≤ v)
    (hvar : ∀ i, v ≤ avg P (fun n => (X i n) ^ 2))
    (hcov : ∀ i j, i ≠ j → |avg P (fun n => X i n * X j n)| ≤ ε)
    (hsmall : ε * (5 * (m : ℝ) / 3) ≤ v / 2) :
    (v / 2) * ((m : ℝ) * ((1 / 16 : ℝ) ^ K' * (1 - (1 / 16 : ℝ) ^ L) / 15))
      ≤ avg P (fun n => (∑ i, c i * X i n) ^ 2) := by
  have h := rowVariance_half P X c hε hv hvar hcov (ratio_released c hc) hsmall
    (by positivity)
  rwa [sum_sq_released c hc] at h

/-- **(E), discharged into its interface.**  A family of released-row lower bounds of the shape
`released_row_lower` produces `Budget.RoughRowVarianceLower` verbatim, at row support `m = 2^K`
and constant `(v/2)(1 − 16^{-L})`.  Nothing external remains between the two arithmetic inputs
(`rough_variance_lower`, `cross_shift_corr_le`) and the verdict. -/
theorem roughRowVarianceLower_of_released {K L : ℕ} {sm : ℕ → ℝ} {v : ℝ}
    (h : ∀ K', (v / 2) * (((2 : ℝ) ^ K) * ((1 / 16 : ℝ) ^ K' * (1 - (1 / 16 : ℝ) ^ L) / 15))
      ≤ sm K') :
    Budget.RoughRowVarianceLower sm ((v / 2) * (1 - (1 / 16 : ℝ) ^ L)) K := by
  intro K'
  have := h K'
  calc (v / 2) * (1 - (1 / 16 : ℝ) ^ L) * ((2 : ℝ) ^ K * ((1 / 16 : ℝ) ^ K' / 15))
      = (v / 2) * ((2 : ℝ) ^ K * ((1 / 16 : ℝ) ^ K' * (1 - (1 / 16 : ℝ) ^ L) / 15)) := by ring
    _ ≤ sm K' := this

/-! ### (E) in arithmetic terms: the two inputs feed the reduction directly

`released_row_lower` asks for per-term non-degeneracy `v` and near-orthogonality `ε` of the
row's terms.  At the real object the terms are the rough-prime fluctuations `fluct S ρ_i`, and
those two hypotheses are exactly `rough_variance_lower` and `cross_shift_corr_le`.  The only
genuinely arithmetic content left is the **gap-divisor count** `g`: how much of `Σ_{p ∣ Δ} 4/p`
can survive when `Δ = ρ_i − ρ_j` ranges over the row's shift gaps.  Since every `p ∈ S` is rough
(`p > T`), `g ≤ 4 (log|Δ|/log T)/T`, which beats `v 2^{-K}` for the schedule's parameters. -/

/-- The rough-prime fluctuation at shift `r`: `Σ_{p ∈ S} (1[p ∣ n + r] − 1/p)`. -/
noncomputable def fluct (S : Finset ℕ) (r : ℤ) (n : ℕ) : ℝ :=
  ∑ p ∈ S, ((if (p : ℤ) ∣ ((n : ℤ) + r) then (1 : ℝ) else 0) - 1 / p)

/-- Splitting the three-case table of `cross_shift_corr_le` into the gap-divisor part and a
uniform `Σ 3/p²` remainder. -/
lemma table_le_split (S : Finset ℕ) (Δ : ℤ) :
    (∑ p ∈ S, (if (p : ℤ) ∣ Δ then 4 * (1 / (p : ℝ)) else 3 * (1 / (p : ℝ)) ^ 2))
      ≤ (∑ p ∈ S.filter (fun p : ℕ => (p : ℤ) ∣ Δ), 4 * (1 / (p : ℝ)))
        + ∑ p ∈ S, 3 * (1 / (p : ℝ)) ^ 2 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℤ) ∣ Δ)]
  have h1 : ∑ p ∈ S.filter (fun p : ℕ => (p : ℤ) ∣ Δ),
      (if (p : ℤ) ∣ Δ then 4 * (1 / (p : ℝ)) else 3 * (1 / (p : ℝ)) ^ 2)
      = ∑ p ∈ S.filter (fun p : ℕ => (p : ℤ) ∣ Δ), 4 * (1 / (p : ℝ)) :=
    Finset.sum_congr rfl fun p hp => by
      rw [if_pos (Finset.mem_filter.1 hp).2]
  have h2 : ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℤ) ∣ Δ),
      (if (p : ℤ) ∣ Δ then 4 * (1 / (p : ℝ)) else 3 * (1 / (p : ℝ)) ^ 2)
      = ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℤ) ∣ Δ), 3 * (1 / (p : ℝ)) ^ 2 :=
    Finset.sum_congr rfl fun p hp => by
      rw [if_neg (Finset.mem_filter.1 hp).2]
  rw [h1, h2]
  have h3 : ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℤ) ∣ Δ), 3 * (1 / (p : ℝ)) ^ 2
      ≤ ∑ p ∈ S, 3 * (1 / (p : ℝ)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => by positivity)
  linarith

/-- **(E), discharged.**  Given the schedule's sample (a CRT progression), a set `S` of rough
primes, released-layer weights of the standard shape, and a gap-divisor budget `g` beating
`v · 2^{-K}`, the row second moment satisfies `Budget.RoughRowVarianceLower` — the one hypothesis
`budget_forces_two_layers` consumes.  No unproved statement remains between the arithmetic of
`ω` along the progression and the deformation verdict. -/
theorem roughRowVarianceLower_arith {K L Q c0 N : ℕ} (hQ : 0 < Q) (hN : 0 < N)
    (S : Finset ℕ) (hpos : ∀ p ∈ S, 0 < p)
    (hQcop : ∀ p ∈ S, Nat.Coprime Q p)
    (hcop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (ρ : ℕ → Fin (2 ^ K) × Fin L → ℤ) (w : ℕ → Fin (2 ^ K) × Fin L → ℝ)
    (hw : ∀ K' i, |w K' i| = (1 / 4 : ℝ) ^ (K' + 1 + (i.2 : ℕ)))
    {v g ε : ℝ} (hvnn : 0 ≤ v) (hεnn : 0 ≤ ε)
    (hv : v ≤ (∑ p ∈ S, ((1 : ℝ) / p - ((1 : ℝ) / p) ^ 2)) - 3 * (1 / (N : ℝ)) * (S.card : ℝ) ^ 2)
    (hgap : ∀ K' : ℕ, ∀ i j, i ≠ j →
      (∑ p ∈ S.filter (fun p : ℕ => (p : ℤ) ∣ (ρ K' i - ρ K' j)), 4 * (1 / (p : ℝ))) ≤ g)
    (hε : g + (∑ p ∈ S, 3 * (1 / (p : ℝ)) ^ 2) + 3 * (S.card : ℝ) ^ 2 / N ≤ ε)
    (hsmall : ε * (5 * ((2 : ℝ) ^ K) / 3) ≤ v / 2) :
    Budget.RoughRowVarianceLower
      (fun K' => avg ((Finset.range N).image (fun k => c0 + Q * k))
        (fun n => (∑ i, w K' i * fluct S (ρ K' i) n) ^ 2))
      ((v / 2) * (1 - (1 / 16 : ℝ) ^ L)) K := by
  classical
  refine roughRowVarianceLower_of_released (L := L) (fun K' => ?_)
  have hcard : ((Fintype.card (Fin (2 ^ K)) : ℕ) : ℝ) = (2 : ℝ) ^ K := by
    rw [Fintype.card_fin]; push_cast; ring
  have hmain := released_row_lower (m := 2 ^ K) (L := L) (K' := K')
    ((Finset.range N).image (fun k => c0 + Q * k))
    (fun i => fluct S (ρ K' i)) (w K') (hw K') hεnn hvnn ?_ ?_ ?_
  · rw [show ((2 ^ K : ℕ) : ℝ) = (2 : ℝ) ^ K from by push_cast; ring] at hmain
    exact hmain
  · -- per-term non-degeneracy
    intro i
    refine le_trans hv ?_
    exact rough_variance_lower hQ hN (ρ K' i) S hpos hQcop hcop
  · -- near-orthogonality
    intro i j hij
    refine le_trans (cross_shift_corr_le hQ hN (ρ K' i) (ρ K' j) S hpos hQcop hcop) ?_
    have hsplit := table_le_split S (ρ K' i - ρ K' j)
    have := hgap K' i j hij
    linarith
  · -- the near-orthogonality scale
    rw [show ((2 ^ K : ℕ) : ℝ) = (2 : ℝ) ^ K from by push_cast; ring]
    exact hsmall

end NormalNumbers.G4.RowVariance
