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

/-! ### The gap-divisor budget `g`, from roughness

The last arithmetic input of `roughRowVarianceLower_arith` is `g ≥ Σ_{p ∈ S, p ∣ Δ} 4/p`.
Because the primes of `S` are **rough** (`p ≥ T`) and pairwise coprime, their product divides
`Δ`, so at most `log|Δ|/log T` of them can divide `Δ` at all, and each contributes `≤ 4/T`.
The statement below avoids logarithms: `k` is any exponent with `|Δ| < T^{k+1}`. -/

/-- At most `k` pairwise-coprime numbers `≥ T` divide a nonzero `Δ` with `|Δ| < T^{k+1}`. -/
lemma card_rough_divisors_le {T : ℕ} (hT : 2 ≤ T) (F : Finset ℕ) {Δ : ℤ} (hΔ : Δ ≠ 0)
    (hge : ∀ p ∈ F, T ≤ p)
    (hcop : ∀ p ∈ F, ∀ q ∈ F, p ≠ q → Nat.Coprime p q)
    (hdvd : ∀ p ∈ F, (p : ℤ) ∣ Δ) {k : ℕ} (hk : Δ.natAbs < T ^ (k + 1)) :
    F.card ≤ k := by
  classical
  have hprodZ : (∏ p ∈ F, (p : ℤ)) ∣ Δ := by
    refine Finset.prod_dvd_of_coprime ?_ hdvd
    intro p hp q hq hne
    exact Nat.isCoprime_iff_coprime.2 (hcop p hp q hq (by exact_mod_cast hne))
  have hprodN : (∏ p ∈ F, p) ∣ Δ.natAbs := by
    have : ((∏ p ∈ F, p : ℕ) : ℤ) ∣ Δ := by push_cast; exact hprodZ
    exact Int.natCast_dvd_natCast.1 (Int.dvd_natAbs.2 this)
  have hpos : 0 < Δ.natAbs := Int.natAbs_pos.2 hΔ
  have h1 : T ^ F.card ≤ ∏ p ∈ F, p := Finset.pow_card_le_prod F _ _ hge
  have h2 : (∏ p ∈ F, p) ≤ Δ.natAbs := Nat.le_of_dvd hpos hprodN
  have h3 : T ^ F.card < T ^ (k + 1) := lt_of_le_of_lt (le_trans h1 h2) hk
  have := (Nat.pow_lt_pow_iff_right (by omega : 1 < T)).1 h3
  omega

/-- **The gap-divisor budget.**  With rough, pairwise-coprime primes, the shift-gap correlation
`Σ_{p ∣ Δ} 4/p` is at most `4k/T`. -/
theorem gap_divisor_sum_le {T : ℕ} (hT : 2 ≤ T) (S : Finset ℕ) {Δ : ℤ} (hΔ : Δ ≠ 0)
    (hge : ∀ p ∈ S, T ≤ p)
    (hcop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {k : ℕ} (hk : Δ.natAbs < T ^ (k + 1)) :
    (∑ p ∈ S.filter (fun p : ℕ => (p : ℤ) ∣ Δ), 4 * (1 / (p : ℝ))) ≤ 4 * k / T := by
  classical
  set F := S.filter (fun p : ℕ => (p : ℤ) ∣ Δ) with hF
  have hsub : F ⊆ S := Finset.filter_subset _ _
  have hcard : F.card ≤ k :=
    card_rough_divisors_le hT F hΔ (fun p hp => hge p (hsub hp))
      (fun p hp q hq hne => hcop p (hsub hp) q (hsub hq) hne)
      (fun p hp => (Finset.mem_filter.1 hp).2) hk
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hterm : ∀ p ∈ F, 4 * (1 / (p : ℝ)) ≤ 4 / T := by
    intro p hp
    have : (T : ℝ) ≤ (p : ℝ) := by exact_mod_cast hge p (hsub hp)
    rw [show (4 : ℝ) * (1 / (p : ℝ)) = 4 / p from by ring]
    exact div_le_div_of_nonneg_left (by norm_num) hT0 this
  calc (∑ p ∈ F, 4 * (1 / (p : ℝ))) ≤ ∑ _p ∈ F, (4 : ℝ) / T := Finset.sum_le_sum hterm
    _ = (F.card : ℝ) * (4 / T) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) * (4 / T) := by
        have : (F.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = 4 * k / T := by ring

/-! ### The dyadic instantiation: (E) at explicit scales

All four inputs of `roughRowVarianceLower_arith` are now arithmetic facts about a *dyadic* set of
rough primes `S ⊆ [T, 2T]`.  Writing `m = |S|` and `A = 2^K` for the row support:

    v ≥ m/(4T)  (per-term),      ε ≤ 4k/T + 3m/T² + 3m²/N  (correlation),

and the reduction's `ε·(5A/3) ≤ v/2` holds as soon as

    T ≥ 1440 A,      m ≥ 1920 A k,      N ≥ 1440 A m T.

Each term of `ε` is then below `m/(480 A T)`, so `ε·(5A/3) ≤ m/(96T) ≤ v/2`.  These are exactly
the schedule's "rough primes are plentiful, the sample is long, the gaps are short" conditions,
with the constants made explicit. -/

/-- Per-term non-degeneracy on a dyadic rough range. -/
lemma dyadic_variance_ge {T : ℕ} (hT : 4 ≤ T) (S : Finset ℕ)
    (hge : ∀ p ∈ S, T ≤ p) (hle : ∀ p ∈ S, p ≤ 2 * T) :
    (S.card : ℝ) / (4 * T) ≤ ∑ p ∈ S, ((1 : ℝ) / p - ((1 : ℝ) / p) ^ 2) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hterm : ∀ p ∈ S, (1 : ℝ) / (4 * T) ≤ (1 : ℝ) / p - ((1 : ℝ) / p) ^ 2 := by
    intro p hp
    have hp4 : (4 : ℝ) ≤ (p : ℝ) := by
      have := hge p hp; have : (4 : ℕ) ≤ p := le_trans hT this
      exact_mod_cast this
    have hple : (p : ℝ) ≤ 2 * T := by exact_mod_cast hle p hp
    have hp0 : (0 : ℝ) < p := by linarith
    have h1 : (1 : ℝ) / p - ((1 : ℝ) / p) ^ 2 = (1 / p) * (1 - 1 / p) := by ring
    have h2 : (1 : ℝ) / p ≥ 1 / (2 * T) := by
      apply one_div_le_one_div_of_le (by linarith) hple
    have h3 : (1 : ℝ) / p ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le (by norm_num) hp4
    have h4 : (0 : ℝ) < 1 / (2 * T) := by positivity
    rw [h1]
    have : (1 / (2 * (T : ℝ))) * (3 / 4) ≤ (1 / p) * (1 - 1 / p) := by
      apply mul_le_mul h2 (by linarith) (by norm_num) (by positivity)
    calc (1 : ℝ) / (4 * T) ≤ (1 / (2 * (T : ℝ))) * (3 / 4) := by
          rw [div_le_iff₀ (by positivity)]
          field_simp
          linarith
      _ ≤ (1 / p) * (1 - 1 / p) := this
  calc (S.card : ℝ) / (4 * T) = (S.card : ℝ) * (1 / (4 * T)) := by ring
    _ = ∑ _p ∈ S, (1 : ℝ) / (4 * T) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum hterm

/-- The `Σ 3/p²` remainder on a dyadic rough range. -/
lemma dyadic_sq_sum_le {T : ℕ} (hT : 4 ≤ T) (S : Finset ℕ) (hge : ∀ p ∈ S, T ≤ p) :
    (∑ p ∈ S, 3 * (1 / (p : ℝ)) ^ 2) ≤ 3 * (S.card : ℝ) / (T : ℝ) ^ 2 := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hterm : ∀ p ∈ S, 3 * (1 / (p : ℝ)) ^ 2 ≤ 3 / (T : ℝ) ^ 2 := by
    intro p hp
    have hpT : (T : ℝ) ≤ (p : ℝ) := by exact_mod_cast hge p hp
    have h : (1 : ℝ) / p ≤ 1 / T := one_div_le_one_div_of_le hT0 hpT
    have h0 : (0 : ℝ) ≤ 1 / p := by positivity
    have : ((1 : ℝ) / p) ^ 2 ≤ (1 / (T : ℝ)) ^ 2 := by nlinarith
    calc 3 * ((1 : ℝ) / p) ^ 2 ≤ 3 * (1 / (T : ℝ)) ^ 2 := by linarith
      _ = 3 / (T : ℝ) ^ 2 := by rw [div_pow]; ring
  calc (∑ p ∈ S, 3 * (1 / (p : ℝ)) ^ 2) ≤ ∑ _p ∈ S, (3 : ℝ) / (T : ℝ) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (3 / (T : ℝ) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = 3 * (S.card : ℝ) / (T : ℝ) ^ 2 := by ring

/-- **The scale inequality.**  At `T ≥ 1440 A`, `m ≥ 1920 A k`, `N ≥ 1440 A m T` the correlation
level is below `v/(2·ratio)`: the hypothesis `released_row_lower` needs. -/
lemma dyadic_scales {A t M n kk : ℝ} (hA : 1 ≤ A) (ht : 0 < t) (hn : 0 < n) (hM : 0 ≤ M)
    (hk : 0 ≤ kk) (hT : 1440 * A ≤ t) (hm : 1920 * A * kk ≤ M) (hN : 1440 * A * M * t ≤ n) :
    (4 * kk / t + 3 * M / t ^ 2 + 3 * M ^ 2 / n) * (5 * A / 3)
      ≤ (M / (4 * t) - 3 * M ^ 2 / n) / 2 := by
  have hAt : (0 : ℝ) < 480 * A * t := by positivity
  have hb1 : 4 * kk / t ≤ M / (480 * A * t) := by
    rw [div_le_div_iff₀ ht hAt]
    nlinarith [mul_nonneg hk (le_of_lt ht)]
  have hb2 : 3 * M / t ^ 2 ≤ M / (480 * A * t) := by
    rw [div_le_div_iff₀ (by positivity) hAt]
    nlinarith [mul_nonneg hM (le_of_lt ht)]
  have hb3 : 3 * M ^ 2 / n ≤ M / (480 * A * t) := by
    rw [div_le_div_iff₀ hn hAt]
    nlinarith [sq_nonneg M, mul_nonneg hM (le_of_lt ht)]
  have hXv : M / (480 * A * t) ≤ M / (480 * t) := by
    rw [div_le_div_iff₀ hAt (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hM ht.le) (sub_nonneg.2 hA)]
  have hfin : (M / (480 * A * t)) * (5 * A) = M / (96 * t) := by
    field_simp
    ring
  have hle : (4 * kk / t + 3 * M / t ^ 2 + 3 * M ^ 2 / n) * (5 * A / 3)
      ≤ (3 * (M / (480 * A * t))) * (5 * A / 3) := by
    have h5 : (0 : ℝ) ≤ 5 * A / 3 := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) h5
  have heq : (3 * (M / (480 * A * t))) * (5 * A / 3) = M / (96 * t) := by
    rw [show (3 * (M / (480 * A * t))) * (5 * A / 3) = (M / (480 * A * t)) * (5 * A) from by ring,
      hfin]
  rw [heq] at hle
  have hv : M / (96 * t) ≤ (M / (4 * t) - 3 * M ^ 2 / n) / 2 := by
    have h1 : 3 * M ^ 2 / n ≤ M / (480 * t) := le_trans hb3 hXv
    have h2 : M / (96 * t) ≤ (M / (4 * t) - M / (480 * t)) / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
      have e1 : M / (4 * t) - M / (480 * t) = 119 * M / (480 * t) := by
        field_simp; ring
      rw [e1, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg hM (le_of_lt ht)]
    linarith
  linarith

/-- **(E) at explicit scales.**  The whole chain, instantiated: a dyadic set `S ⊆ [T, 2T]` of
pairwise-coprime rough primes coprime to the frozen modulus `Q`, shift gaps bounded by `T^{k+1}`,
and the three scale conditions `T ≥ 1440·2^K`, `|S| ≥ 1920·2^K·k`, `N ≥ 1440·2^K·|S|·T`.  Then the
row second moments of the released layers satisfy `Budget.RoughRowVarianceLower` — no hypothesis
left over.  Chaining with `Budget.budget_forces_two_layers` and `Sched.balanced_union_le` closes
(E) in the deformation verdict. -/
theorem roughRowVarianceLower_dyadic {K L T Q c0 N k : ℕ} (hT : 4 ≤ T) (hQ : 0 < Q) (hN : 0 < N)
    (S : Finset ℕ) (hge : ∀ p ∈ S, T ≤ p) (hle : ∀ p ∈ S, p ≤ 2 * T)
    (hQcop : ∀ p ∈ S, Nat.Coprime Q p)
    (hcop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (ρ : ℕ → Fin (2 ^ K) × Fin L → ℤ) (w : ℕ → Fin (2 ^ K) × Fin L → ℝ)
    (hw : ∀ K' i, |w K' i| = (1 / 4 : ℝ) ^ (K' + 1 + (i.2 : ℕ)))
    (hΔ : ∀ (K' : ℕ) (i j), i ≠ j →
      ρ K' i - ρ K' j ≠ 0 ∧ (ρ K' i - ρ K' j).natAbs < T ^ (k + 1))
    (hTA : (1440 : ℝ) * 2 ^ K ≤ (T : ℝ))
    (hmA : (1920 : ℝ) * 2 ^ K * (k : ℝ) ≤ (S.card : ℝ))
    (hNA : (1440 : ℝ) * 2 ^ K * (S.card : ℝ) * (T : ℝ) ≤ (N : ℝ)) :
    Budget.RoughRowVarianceLower
      (fun K' => avg ((Finset.range N).image (fun x => c0 + Q * x))
        (fun n => (∑ i, w K' i * fluct S (ρ K' i) n) ^ 2))
      ((((S.card : ℝ) / (4 * T) - 3 * (S.card : ℝ) ^ 2 / N) / 2) * (1 - (1 / 16 : ℝ) ^ L)) K := by
  classical
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hA1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
  have hsmall := dyadic_scales (A := (2 : ℝ) ^ K) (t := (T : ℝ)) (M := (S.card : ℝ))
    (n := (N : ℝ)) (kk := (k : ℝ)) hA1 hT0 hN0 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hTA hmA hNA
  have hεnn : (0 : ℝ) ≤ 4 * (k : ℝ) / T + 3 * (S.card : ℝ) / (T : ℝ) ^ 2
      + 3 * (S.card : ℝ) ^ 2 / N := by positivity
  have hvnn : (0 : ℝ) ≤ (S.card : ℝ) / (4 * T) - 3 * (S.card : ℝ) ^ 2 / N := by
    have h5 : (0 : ℝ) ≤ 5 * (2 : ℝ) ^ K / 3 := by positivity
    nlinarith [mul_nonneg hεnn h5]
  refine roughRowVarianceLower_arith (g := 4 * (k : ℝ) / T) hQ hN S
      (fun p hp => lt_of_lt_of_le (by omega) (hge p hp)) hQcop hcop ρ w hw hvnn hεnn ?_ ?_ ?_
      hsmall
  · have h1 := dyadic_variance_ge hT S hge hle
    have h2 : 3 * (1 / (N : ℝ)) * (S.card : ℝ) ^ 2 = 3 * (S.card : ℝ) ^ 2 / N := by ring
    rw [h2]
    linarith
  · intro K' i j hij
    exact gap_divisor_sum_le (by omega) S (hΔ K' i j hij).1
      (fun p hp => hge p hp) hcop (hΔ K' i j hij).2
  · have := dyadic_sq_sum_le hT S hge
    have h3 : 3 * (S.card : ℝ) ^ 2 / N = 3 * (S.card : ℝ) ^ 2 / N := rfl
    linarith

/-- The variance constant of `roughRowVarianceLower_dyadic` is strictly positive whenever the
rough set is nonempty — the strictness `budget_forces_two_layers` needs. -/
lemma dyadic_v_pos {A t M n : ℝ} (hA : 1 ≤ A) (ht : 0 < t) (hn : 0 < n) (hM : 0 < M)
    (hN : 1440 * A * M * t ≤ n) : 0 < M / (4 * t) - 3 * M ^ 2 / n := by
  have hb3 : 3 * M ^ 2 / n ≤ M / (480 * t) := by
    rw [div_le_div_iff₀ hn (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hM.le hM.le) ht.le,
      mul_nonneg (mul_nonneg (mul_nonneg hM.le hM.le) ht.le) (sub_nonneg.2 hA)]
  have h1 : M / (480 * t) < M / (4 * t) := by
    apply div_lt_div_of_pos_left hM (by positivity)
    linarith
  linarith

/-- **The verdict, with (E) proved.**  A sampler whose released-row second moment fits the
capture budget must cancel at least two layers.  Compared with `Budget.budget_forces_two_layers`,
the variance hypothesis is no longer assumed: it is `roughRowVarianceLower_dyadic`. -/
theorem two_layers_of_dyadic {K L T Q c0 N k : ℕ} (hT : 4 ≤ T) (hQ : 0 < Q) (hN : 0 < N)
    (hK : 8 ≤ K) (hL : 0 < L)
    (S : Finset ℕ) (hSne : 0 < S.card) (hge : ∀ p ∈ S, T ≤ p) (hle : ∀ p ∈ S, p ≤ 2 * T)
    (hQcop : ∀ p ∈ S, Nat.Coprime Q p)
    (hcop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (ρ : ℕ → Fin (2 ^ K) × Fin L → ℤ) (w : ℕ → Fin (2 ^ K) × Fin L → ℝ)
    (hw : ∀ K' i, |w K' i| = (1 / 4 : ℝ) ^ (K' + 1 + (i.2 : ℕ)))
    (hΔ : ∀ (K' : ℕ) (i j), i ≠ j →
      ρ K' i - ρ K' j ≠ 0 ∧ (ρ K' i - ρ K' j).natAbs < T ^ (k + 1))
    (hTA : (1440 : ℝ) * 2 ^ K ≤ (T : ℝ))
    (hmA : (1920 : ℝ) * 2 ^ K * (k : ℝ) ≤ (S.card : ℝ))
    (hNA : (1440 : ℝ) * 2 ^ K * (S.card : ℝ) * (T : ℝ) ≤ (N : ℝ))
    {K' : ℕ}
    (hcap : avg ((Finset.range N).image (fun x => c0 + Q * x))
        (fun n => (∑ i, w K' i * fluct S (ρ K' i) n) ^ 2)
      ≤ ((((S.card : ℝ) / (4 * T) - 3 * (S.card : ℝ) ^ 2 / N) / 2)
          * (1 - (1 / 16 : ℝ) ^ L)) * ((1 : ℝ) / 2) ^ (K / 2)) :
    2 ≤ K' := by
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hM0 : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hSne
  have hA1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
  have hv := dyadic_v_pos hA1 hT0 hN0 hM0 hNA
  have hL16 : (0 : ℝ) < 1 - (1 / 16 : ℝ) ^ L := by
    have : (1 / 16 : ℝ) ^ L < 1 := by
      apply pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith
  have hc : (0 : ℝ) < (((S.card : ℝ) / (4 * T) - 3 * (S.card : ℝ) ^ 2 / N) / 2)
      * (1 - (1 / 16 : ℝ) ^ L) := by positivity
  exact Budget.budget_forces_two_layers hc hK
    (roughRowVarianceLower_dyadic hT hQ hN S hge hle hQcop hcop ρ w hw hΔ hTA hmA hNA) hcap

/-! ### The capstone: cancellation ⇒ the density bound

`two_layers_of_dyadic` delivers `K′ ≥ 2` — at least two of the sampler's layers are *cancelled*.
Cancellation of layer `j` is, by DESIGN §4's definition, exactly row-balance of
`layer j d t`, so two cancelled layers is verbatim the hypothesis of `Sched.balanced_union_le`.
The composite below records the whole implication in one statement. -/

/-- The sampler cancels its first `K′` layers. -/
def LayersCancelled {K s : ℕ} (d t : (Fin K → Fin (s + 1)) → ℤ) (K' : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ K' → RowBalance.Balanced (RowBalance.layer j d t)

/-- Two cancelled layers, named. -/
lemma two_balanced_of_cancelled {K s K' : ℕ} {d t : (Fin K → Fin (s + 1)) → ℤ}
    (h : LayersCancelled d t K') (hK' : 2 ≤ K') :
    ∃ j j' : ℕ, j ≠ j' ∧ RowBalance.Balanced (RowBalance.layer j d t) ∧
      RowBalance.Balanced (RowBalance.layer j' d t) :=
  ⟨1, 2, by norm_num, h 1 le_rfl (by omega), h 2 (by omega) hK'⟩

open NormalNumbers.G4.Sched NormalNumbers.G4Confine in
/-- **The verdict, from cancellation.**  Every sampler in the family cancels at least two layers
(the conclusion of `two_layers_of_dyadic`); then the union of the windows it reads below `L` has
upper density `≤ dmin^{−H/2}`. -/
theorem cancelled_union_le (i : ℕ)
    {κ : Type*} [DecidableEq κ] (𝓕 : Finset κ)
    (d t : κ → (gridAt i).Atom → ℕ) (P : κ → Finset ℕ)
    (hinj : Set.InjOn (fun ν => ((fun α => (d ν α : ℤ)), (fun α => (t ν α : ℤ)))) 𝓕)
    (K' : κ → ℕ) (hK' : ∀ ν ∈ 𝓕, 2 ≤ K' ν)
    (hcancel : ∀ ν ∈ 𝓕,
      LayersCancelled (fun α => (d ν α : ℤ)) (fun α => (t ν α : ℤ)) (K' ν))
    (hd : ∀ ν ∈ 𝓕, ∀ α, dmin i ≤ d ν α ∧ d ν α ≤ dmax i)
    (ht : ∀ ν ∈ 𝓕, ∀ α, t ν α ≤ dmax i)
    (hcop : ∀ ν ∈ 𝓕, ∀ α β, α ≠ β → Nat.Coprime (d ν α) (d ν β))
    (hP : ∀ ν ∈ 𝓕, ∀ n ∈ P ν, ∀ α, n % d ν α = t ν α)
    (U : ℕ → Prop) [DecidablePred U] {L : ℕ}
    (hcov : ∀ j, j < L → U j → ∃ ν ∈ 𝓕, ∃ n ∈ P ν, ∃ α, ∃ h < kk i,
      j = 2 * physIdx (d ν α) (t ν α) n + h) :
    (((Finset.range L).filter U).card : ℝ) ≤
      (L : ℝ) / (dmin i : ℝ) ^ ((KK i ^ 2 + 1) ^ KK i / 2)
        + ((2 * dmax i + 1 : ℕ) : ℝ) ^ (2 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)))
            * (((KK i ^ 2 + 1) ^ KK i : ℕ) * kk i) :=
  balanced_union_le i 𝓕 d t P hinj
    (fun ν hν => two_balanced_of_cancelled (hcancel ν hν) (hK' ν hν))
    hd ht hcop hP U hcov

/-! ### Non-vacuity: rough primes of any prescribed total weight exist

The hypotheses of the chain are only worth proving if they can be met.  The one that is not
obviously satisfiable is the per-term variance: `Σ_{p ∈ S} (1/p − 1/p²) ≥ v` with **every** `p`
above the roughness threshold `T`.  It is satisfiable for every `v`, because the sum of prime
reciprocals diverges (`not_summable_one_div_on_primes`) — removing the finitely many primes below
`T` removes at most `T` from the total. -/

/-- **Rough primes of arbitrary total weight.**  For every roughness threshold `T ≥ 2` and every
target `V`, some finite set of primes, all `≥ T`, has `Σ (1/p − 1/p²) ≥ V`. -/
theorem exists_rough_primes (T : ℕ) (hT : 2 ≤ T) (V : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧ (∀ p ∈ S, T ≤ p) ∧
      V ≤ ∑ p ∈ S, ((1 : ℝ) / p - ((1 : ℝ) / p) ^ 2) := by
  classical
  set f : ℕ → ℝ := Set.indicator {p | Nat.Prime p} (fun n : ℕ => (1 : ℝ) / n) with hf
  have hfnn : ∀ n, 0 ≤ f n := fun n =>
    Set.indicator_nonneg (fun p _ => by positivity) n
  have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg hfnn).1
    not_summable_one_div_on_primes
  obtain ⟨M, hM⟩ := (Filter.tendsto_atTop.1 htend (2 * V + T)).exists
  refine ⟨(Finset.range M).filter (fun n => Nat.Prime n ∧ T ≤ n),
    fun p hp => (Finset.mem_filter.1 hp).2.1, fun p hp => (Finset.mem_filter.1 hp).2.2, ?_⟩
  set A := (Finset.range M).filter (fun n => Nat.Prime n) with hA
  set S := (Finset.range M).filter (fun n => Nat.Prime n ∧ T ≤ n) with hS
  have hprimes : ∑ n ∈ Finset.range M, f n = ∑ n ∈ A, (1 : ℝ) / n := by
    rw [hA, Finset.sum_filter]
    exact Finset.sum_congr rfl fun n _ => by
      simp [hf, Set.indicator_apply, Set.mem_setOf_eq]
  have hSeq : S = A.filter (fun n => T ≤ n) := by
    ext n
    simp only [hS, hA, Finset.mem_filter, Finset.mem_range]
    tauto
  have hsplit : ∑ n ∈ A, (1 : ℝ) / n
      = (∑ n ∈ A.filter (fun n => T ≤ n), (1 : ℝ) / n)
        + ∑ n ∈ A.filter (fun n => ¬ T ≤ n), (1 : ℝ) / n :=
    (Finset.sum_filter_add_sum_filter_not A _ _).symm
  have hsmallpart : ∑ n ∈ A.filter (fun n => ¬ T ≤ n), (1 : ℝ) / n ≤ (T : ℝ) := by
    have hsub : A.filter (fun n => ¬ T ≤ n) ⊆ Finset.range T := by
      intro n hn
      have h := (Finset.mem_filter.1 hn).2
      exact Finset.mem_range.2 (by omega)
    have hcard : (A.filter (fun n => ¬ T ≤ n)).card ≤ T := by
      have := Finset.card_le_card hsub
      simpa using this
    calc ∑ n ∈ A.filter (fun n => ¬ T ≤ n), (1 : ℝ) / n
        ≤ ∑ _n ∈ A.filter (fun n => ¬ T ≤ n), (1 : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hp : Nat.Prime n := (Finset.mem_filter.1 (Finset.mem_filter.1 hn).1).2
          have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.one_lt.le
          rw [div_le_one (by linarith)]; linarith
      _ = ((A.filter (fun n => ¬ T ≤ n)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (T : ℝ) := by exact_mod_cast hcard
  have hbig : 2 * V + T ≤ ∑ n ∈ A, (1 : ℝ) / n := by rw [← hprimes]; exact hM
  have hSsum : 2 * V ≤ ∑ p ∈ S, (1 : ℝ) / p := by
    rw [hSeq]; linarith [hsplit ▸ hbig]
  have hterm : ∀ p ∈ S, (1 : ℝ) / 2 * (1 / p) ≤ (1 : ℝ) / p - ((1 : ℝ) / p) ^ 2 := by
    intro p hp
    have hpp : Nat.Prime p := (Finset.mem_filter.1 hp).2.1
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have h1 : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    have hnn : (0 : ℝ) ≤ 1 / p := by positivity
    nlinarith
  calc V = (1 : ℝ) / 2 * (2 * V) := by ring
    _ ≤ (1 : ℝ) / 2 * ∑ p ∈ S, (1 : ℝ) / p := by linarith
    _ = ∑ p ∈ S, (1 : ℝ) / 2 * (1 / p) := by rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ S, ((1 : ℝ) / p - ((1 : ℝ) / p) ^ 2) := Finset.sum_le_sum hterm

/-! ### A roughness-only bound for the `Σ 1/p²` remainder

`dyadic_sq_sum_le` priced `Σ_{p∈S} 3/p²` by `3|S|/T²`, which forces `|S|` to stay small compared
with `T` — incompatible with making `Σ 1/p` large by taking *many* primes.  The correct bound is
`|S|`-free: every `p ∈ S` is `≥ T` and the `p` are distinct, so the sum is dominated by the tail
`Σ_{n ≥ T} 1/n² ≤ 1/(T−1)`, whatever `|S|` is.  This is what lets `exists_rough_primes` and the
correlation bound hold simultaneously. -/

/-- The telescoping step `1/n² ≤ 1/(n−1) − 1/n`. -/
lemma inv_sq_le_telescope {T : ℕ} (hT : 2 ≤ T) (j : ℕ) :
    ((1 : ℝ) / ((T + j : ℕ) : ℝ)) ^ 2
      ≤ (1 / ((T : ℝ) + j - 1) - 1 / ((T : ℝ) + j)) := by
  have hT2 : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hcast : (((T + j : ℕ) : ℝ)) = (T : ℝ) + j := by push_cast; ring
  rw [hcast]
  have h1 : (0 : ℝ) < (T : ℝ) + j - 1 := by linarith
  have h2 : (0 : ℝ) < (T : ℝ) + j := by linarith
  rw [div_pow, one_pow, div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2), div_le_div_iff₀
    (by positivity) (by positivity)]
  nlinarith

/-- **The `|S|`-free remainder bound.**  Distinct naturals `≥ T ≥ 2` have `Σ 1/p² ≤ 1/(T−1)`. -/
theorem sum_inv_sq_rough_le {T : ℕ} (hT : 2 ≤ T) (S : Finset ℕ) (hge : ∀ p ∈ S, T ≤ p) :
    ∑ p ∈ S, ((1 : ℝ) / p) ^ 2 ≤ 1 / ((T : ℝ) - 1) := by
  classical
  set L := S.sup id + 1 - T with hL
  have hsub : S ⊆ (Finset.range L).image (fun j => T + j) := by
    intro p hp
    have h1 : T ≤ p := hge p hp
    have h2 : p ≤ S.sup id := Finset.le_sup (f := id) hp
    exact Finset.mem_image.2 ⟨p - T, Finset.mem_range.2 (by omega), by omega⟩
  have himg : ∑ p ∈ (Finset.range L).image (fun j => T + j), ((1 : ℝ) / p) ^ 2
      = ∑ j ∈ Finset.range L, ((1 : ℝ) / ((T + j : ℕ) : ℝ)) ^ 2 := by
    refine Finset.sum_image ?_
    intro a _ b _ hab
    simp only at hab
    omega
  have hmono : ∑ p ∈ S, ((1 : ℝ) / p) ^ 2
      ≤ ∑ p ∈ (Finset.range L).image (fun j => T + j), ((1 : ℝ) / p) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have htel : ∑ j ∈ Finset.range L, ((1 : ℝ) / ((T + j : ℕ) : ℝ)) ^ 2
      ≤ ∑ j ∈ Finset.range L, (1 / ((T : ℝ) + j - 1) - 1 / ((T : ℝ) + (j + 1) - 1)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have := inv_sq_le_telescope hT j
    have heq : (T : ℝ) + (j + 1) - 1 = (T : ℝ) + j := by ring
    rw [heq]
    exact this
  have hsum : ∑ j ∈ Finset.range L, (1 / ((T : ℝ) + j - 1) - 1 / ((T : ℝ) + (j + 1) - 1))
      = 1 / ((T : ℝ) + 0 - 1) - 1 / ((T : ℝ) + L - 1) := by
    have := Finset.sum_range_sub' (f := fun j : ℕ => 1 / ((T : ℝ) + j - 1)) L
    simpa using this
  have hT2 : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hlast : (0 : ℝ) ≤ 1 / ((T : ℝ) + L - 1) := by
    have hLn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    exact le_of_lt (div_pos one_pos (by linarith))
  rw [himg] at hmono
  have : ∑ j ∈ Finset.range L, ((1 : ℝ) / ((T + j : ℕ) : ℝ)) ^ 2 ≤ 1 / ((T : ℝ) - 1) := by
    refine le_trans htel ?_
    rw [hsum]
    have : (T : ℝ) + 0 - 1 = (T : ℝ) - 1 := by ring
    rw [this]
    linarith
  linarith

/-- **(E) in Mertens form.**  `S` is any finite set of primes above the roughness threshold `T`,
with `T` above the frozen modulus `Q` (so coprimality is automatic).  The correlation level is
`ε = 4k/T + 3/(T−1) + 3|S|²/N` — the middle term now `|S|`-free, so `Σ(1/p − 1/p²) ≥ V` may be
made as large as one likes by `exists_rough_primes` without spoiling it. -/
theorem roughRowVarianceLower_mertens {K L T Q c0 N k : ℕ} (hT : 4 ≤ T) (hQ : 0 < Q)
    (hQT : Q < T) (hN : 0 < N)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) (hge : ∀ p ∈ S, T ≤ p)
    (ρ : ℕ → Fin (2 ^ K) × Fin L → ℤ) (w : ℕ → Fin (2 ^ K) × Fin L → ℝ)
    (hw : ∀ K' i, |w K' i| = (1 / 4 : ℝ) ^ (K' + 1 + (i.2 : ℕ)))
    (hΔ : ∀ (K' : ℕ) (i j), i ≠ j →
      ρ K' i - ρ K' j ≠ 0 ∧ (ρ K' i - ρ K' j).natAbs < T ^ (k + 1))
    {V : ℝ} (hV : V ≤ ∑ p ∈ S, ((1 : ℝ) / p - ((1 : ℝ) / p) ^ 2))
    (hsmall : (4 * (k : ℝ) / T + 3 / ((T : ℝ) - 1) + 3 * (S.card : ℝ) ^ 2 / N)
        * (5 * (2 : ℝ) ^ K / 3)
      ≤ (V - 3 * (S.card : ℝ) ^ 2 / N) / 2) :
    Budget.RoughRowVarianceLower
      (fun K' => avg ((Finset.range N).image (fun x => c0 + Q * x))
        (fun n => (∑ i, w K' i * fluct S (ρ K' i) n) ^ 2))
      (((V - 3 * (S.card : ℝ) ^ 2 / N) / 2) * (1 - (1 / 16 : ℝ) ^ L)) K := by
  classical
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hT1 : (0 : ℝ) < (T : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    linarith
  have hcop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q := fun p hp q hq hne =>
    (Nat.coprime_primes (hprime p hp) (hprime q hq)).2 hne
  have hQcop : ∀ p ∈ S, Nat.Coprime Q p := by
    intro p hp
    have hpp := hprime p hp
    have hlt : Q < p := lt_of_lt_of_le hQT (hge p hp)
    have : ¬ p ∣ Q := fun hdvd => by
      have := Nat.le_of_dvd hQ hdvd; omega
    exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hpp).2 this))
  have hεnn : (0 : ℝ) ≤ 4 * (k : ℝ) / T + 3 / ((T : ℝ) - 1) + 3 * (S.card : ℝ) ^ 2 / N := by
    positivity
  have hvnn : (0 : ℝ) ≤ V - 3 * (S.card : ℝ) ^ 2 / N := by
    have h5 : (0 : ℝ) ≤ 5 * (2 : ℝ) ^ K / 3 := by positivity
    nlinarith [mul_nonneg hεnn h5]
  refine roughRowVarianceLower_arith (g := 4 * (k : ℝ) / T) hQ hN S
      (fun p hp => (hprime p hp).pos) hQcop hcop ρ w hw hvnn hεnn ?_ ?_ ?_ hsmall
  · have h2 : 3 * (1 / (N : ℝ)) * (S.card : ℝ) ^ 2 = 3 * (S.card : ℝ) ^ 2 / N := by ring
    rw [h2]; linarith
  · intro K' i j hij
    exact gap_divisor_sum_le (by omega) S (hΔ K' i j hij).1 hge hcop (hΔ K' i j hij).2
  · have h := sum_inv_sq_rough_le (by omega : 2 ≤ T) S hge
    have h3 : (∑ p ∈ S, 3 * (1 / (p : ℝ)) ^ 2) = 3 * ∑ p ∈ S, ((1 : ℝ) / p) ^ 2 := by
      rw [Finset.mul_sum]
    have h4 : 3 * ∑ p ∈ S, ((1 : ℝ) / p) ^ 2 ≤ 3 * (1 / ((T : ℝ) - 1)) := by linarith
    rw [h3]
    have h5 : (3 : ℝ) * (1 / ((T : ℝ) - 1)) = 3 / ((T : ℝ) - 1) := by ring
    linarith

/-! ### The scales are satisfiable

The last thing an audit should ask of (E): are the hypotheses of
`roughRowVarianceLower_mertens` ever met?  They are, for every row size `K`, every gap exponent
`k` and every frozen modulus `Q` — choose `T` beyond `16·(5·2^K/3)·(4k+3) + 4 + Q`, then rough
primes of total weight `1` (`exists_rough_primes`), then a sample length `N` beyond
`24·(5·2^K/3)·|S|² + 6|S|²`.  Nothing in the chain is vacuous. -/

/-- **Non-vacuity of (E).**  For every `K`, `k`, `Q` there are a roughness threshold, a rough
prime set and a sample length meeting every numeric hypothesis of
`roughRowVarianceLower_mertens` at `V = 1`. -/
theorem scales_satisfiable (K k Q : ℕ) :
    ∃ (T : ℕ) (S : Finset ℕ) (N : ℕ), 4 ≤ T ∧ Q < T ∧ 0 < N ∧
      (∀ p ∈ S, Nat.Prime p) ∧ (∀ p ∈ S, T ≤ p) ∧
      (1 : ℝ) ≤ ∑ p ∈ S, ((1 : ℝ) / p - ((1 : ℝ) / p) ^ 2) ∧
      (4 * (k : ℝ) / T + 3 / ((T : ℝ) - 1) + 3 * (S.card : ℝ) ^ 2 / N) * (5 * (2 : ℝ) ^ K / 3)
        ≤ ((1 : ℝ) - 3 * (S.card : ℝ) ^ 2 / N) / 2 := by
  classical
  set A : ℝ := 5 * (2 : ℝ) ^ K / 3 with hAdef
  have hA1 : (1 : ℝ) ≤ A := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
    rw [hAdef]; linarith
  have hA0 : (0 : ℝ) < A := by linarith
  obtain ⟨T, hTge⟩ := exists_nat_ge (16 * A * (4 * (k : ℝ) + 3) + 4 + (Q : ℝ))
  have hQr : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have hkr : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hAk : 0 ≤ 16 * A * (4 * (k : ℝ) + 3) := by positivity
  have hT4r : (4 : ℝ) ≤ (T : ℝ) := by linarith
  have hT4 : 4 ≤ T := by exact_mod_cast hT4r
  have hQT : Q < T := by
    have : (Q : ℝ) < (T : ℝ) := by linarith
    exact_mod_cast this
  have hT0 : (0 : ℝ) < (T : ℝ) := by linarith
  have hT1 : (0 : ℝ) < (T : ℝ) - 1 := by linarith
  have h4k : 4 * (k : ℝ) / T ≤ 1 / (16 * A) := by
    rw [div_le_div_iff₀ hT0 (by positivity)]
    nlinarith
  have h3T : 3 / ((T : ℝ) - 1) ≤ 1 / (16 * A) := by
    rw [div_le_div_iff₀ hT1 (by positivity)]
    nlinarith
  obtain ⟨S, hprime, hge, hV⟩ := exists_rough_primes T (by omega) 1
  obtain ⟨N, hNge⟩ := exists_nat_ge (24 * A * (S.card : ℝ) ^ 2 + 6 * (S.card : ℝ) ^ 2 + 1)
  have hm0 : (0 : ℝ) ≤ (S.card : ℝ) ^ 2 := by positivity
  have hAm : 0 ≤ 24 * A * (S.card : ℝ) ^ 2 := by positivity
  have hN1r : (1 : ℝ) ≤ (N : ℝ) := by nlinarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hNpos : 0 < N := by exact_mod_cast hN1r
  have hb1 : 3 * (S.card : ℝ) ^ 2 / N ≤ 1 / (8 * A) := by
    rw [div_le_div_iff₀ hN0 (by positivity)]
    nlinarith
  have hb2 : 3 * (S.card : ℝ) ^ 2 / N ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hN0 (by norm_num)]
    nlinarith
  refine ⟨T, S, N, hT4, hQT, hNpos, hprime, hge, hV, ?_⟩
  have hsum : 4 * (k : ℝ) / T + 3 / ((T : ℝ) - 1) + 3 * (S.card : ℝ) ^ 2 / N
      ≤ 1 / (16 * A) + 1 / (16 * A) + 1 / (8 * A) := by linarith
  have hval : (1 / (16 * A) + 1 / (16 * A) + 1 / (8 * A)) * A = 1 / 4 := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ 4 * (k : ℝ) / T + 3 / ((T : ℝ) - 1) + 3 * (S.card : ℝ) ^ 2 / N := by
    have : (0 : ℝ) ≤ 3 / ((T : ℝ) - 1) := by positivity
    have h2 : (0 : ℝ) ≤ 4 * (k : ℝ) / T := by positivity
    have h3 : (0 : ℝ) ≤ 3 * (S.card : ℝ) ^ 2 / N := by positivity
    linarith
  calc (4 * (k : ℝ) / T + 3 / ((T : ℝ) - 1) + 3 * (S.card : ℝ) ^ 2 / N) * A
      ≤ (1 / (16 * A) + 1 / (16 * A) + 1 / (8 * A)) * A :=
        mul_le_mul_of_nonneg_right hsum hA0.le
    _ = 1 / 4 := hval
    _ ≤ ((1 : ℝ) - 3 * (S.card : ℝ) ^ 2 / N) / 2 := by linarith

/-! ### The grouped-sample criterion, made exact

`Grouped.grouped_union_card_le` prices a joint sample broken into `G` groups of minimum size `w`
by the coefficient `G·|𝓕|·m·H·dmax / (2 dmin^w)`.  The design's informal criterion was
"`w ≳ 2 log H / log dmin`"; the exact statement is below, with no logarithms: the coefficient
drops to `dmin^{−w/2}` — the same shape `Sched.balanced_union_le` achieves at `w = H` — as soon as

    |𝓕| · m · H² · dmax  ≤  2 · dmin^{w − w/2}.

Taking logarithms recovers `w/2 ≥ (2 log H + log(|𝓕| m dmax))/log dmin`. -/

/-- The grouped density coefficient drops to `dmin^{−w/2}` under the exact size condition. -/
theorem grouped_coeff_le {dmin dmax m H G w F L : ℕ} (hdmin : 0 < dmin) (hGH : G ≤ H)
    (hbig : F * m * H ^ 2 * dmax ≤ 2 * dmin ^ (w - w / 2)) :
    (G : ℝ) * ((F : ℝ) * ((L : ℝ) * m * H * dmax / (2 * (dmin : ℝ) ^ w)))
      ≤ (L : ℝ) / (dmin : ℝ) ^ (w / 2) := by
  have hd0 : (0 : ℝ) < (dmin : ℝ) := by exact_mod_cast hdmin
  have hsplit : (dmin : ℝ) ^ w = (dmin : ℝ) ^ (w / 2) * (dmin : ℝ) ^ (w - w / 2) := by
    rw [← pow_add]; congr 1; omega
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hGr : (G : ℝ) ≤ (H : ℝ) := by exact_mod_cast hGH
  have hbigr : (F : ℝ) * m * (H : ℝ) ^ 2 * dmax ≤ 2 * (dmin : ℝ) ^ (w - w / 2) := by
    exact_mod_cast hbig
  have hstep : (G : ℝ) * ((F : ℝ) * m * (H : ℝ) * dmax) ≤ 2 * (dmin : ℝ) ^ (w - w / 2) := by
    have hnn : (0 : ℝ) ≤ (F : ℝ) * m * (H : ℝ) * dmax := by positivity
    calc (G : ℝ) * ((F : ℝ) * m * (H : ℝ) * dmax)
        ≤ (H : ℝ) * ((F : ℝ) * m * (H : ℝ) * dmax) := mul_le_mul_of_nonneg_right hGr hnn
      _ = (F : ℝ) * m * (H : ℝ) ^ 2 * dmax := by ring
      _ ≤ 2 * (dmin : ℝ) ^ (w - w / 2) := hbigr
  have hlhs : (G : ℝ) * ((F : ℝ) * ((L : ℝ) * m * H * dmax / (2 * (dmin : ℝ) ^ w)))
      = ((L : ℝ) * ((G : ℝ) * ((F : ℝ) * m * (H : ℝ) * dmax))) / (2 * (dmin : ℝ) ^ w) := by
    field_simp
  rw [hlhs, div_le_div_iff₀ (by positivity) (by positivity), hsplit]
  have hp0 : (0 : ℝ) < (dmin : ℝ) ^ (w / 2) := by positivity
  nlinarith [mul_nonneg hL0 hp0.le, mul_le_mul_of_nonneg_left hstep (mul_nonneg hL0 hp0.le)]

open NormalNumbers.G4Confine in
/-- **Grouped confinement at the `dmin^{−w/2}` rate.**  The joint sample may be broken into
groups, provided each group still carries `w` atoms with `|𝓕| m H² dmax ≤ 2 dmin^{w−w/2}`. -/
theorem grouped_union_le' {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [DecidableEq κ]
    {G : ℕ} (grp : ι → Fin G)
    (𝓕 : Finset κ) (d t : κ → ι → ℕ) (P : κ → Fin G → Finset ℕ)
    {dmin dmax m L w : ℕ} (hdmin : 0 < dmin)
    (hw : ∀ g : Fin G, w ≤ Fintype.card {α : ι // grp α = g})
    (hGH : G ≤ Fintype.card ι)
    (hbig : 𝓕.card * m * Fintype.card ι ^ 2 * dmax ≤ 2 * dmin ^ (w - w / 2))
    (hd : ∀ ν ∈ 𝓕, ∀ α, dmin ≤ d ν α ∧ d ν α ≤ dmax)
    (hcop : ∀ ν ∈ 𝓕, ∀ α β, α ≠ β → Nat.Coprime (d ν α) (d ν β))
    (hP : ∀ ν ∈ 𝓕, ∀ g, ∀ n ∈ P ν g, ∀ α, grp α = g → n % d ν α = t ν α)
    (U : ℕ → Prop) [DecidablePred U]
    (hcov : ∀ j, j < L → U j → ∃ ν ∈ 𝓕, ∃ g, ∃ n ∈ P ν g, ∃ α, grp α = g ∧ ∃ h < m,
      j = 2 * physIdx (d ν α) (t ν α) n + h) :
    (((Finset.range L).filter U).card : ℝ) ≤
      (L : ℝ) / (dmin : ℝ) ^ (w / 2)
        + (G : ℝ) * ((𝓕.card : ℝ) * (Fintype.card ι * m)) := by
  have hbase := Grouped.grouped_union_card_le grp 𝓕 d t P hdmin hw hd hcop hP U hcov
  have hcoef := grouped_coeff_le (dmin := dmin) (dmax := dmax) (m := m)
    (H := Fintype.card ι) (G := G) (w := w) (F := 𝓕.card) (L := L) hdmin hGH hbig
  have hexp : (G : ℝ) * ((𝓕.card : ℝ) * ((L : ℝ) * m * Fintype.card ι * dmax
        / (2 * (dmin : ℝ) ^ w) + Fintype.card ι * m))
      = (G : ℝ) * ((𝓕.card : ℝ) * ((L : ℝ) * m * Fintype.card ι * dmax
          / (2 * (dmin : ℝ) ^ w)))
        + (G : ℝ) * ((𝓕.card : ℝ) * (Fintype.card ι * m)) := by ring
  rw [hexp] at hbase
  linarith

/-! ### R's open item 2: confinement for an arbitrary invariant

`Sched.balanced_union_le` bounds the sampler count by `(2dmax+1)^{2|skel|}` because two balanced
layers force `MDF`, and `MDF` is pinned by its values on `skel`.  Nothing in the confinement uses
`MDF` itself: **any** invariant `Inv` that is determined by its values on a small set `Sdet`
confines a family the same way, at `(2dmax+1)^{2|Sdet|}`.  So replacing the tensor matrix
`D_s^{⊗K}` by another matrix `A` costs only a determining set for `A`'s own balance relations —
no new confinement proof.  This is the general statement. -/

open NormalNumbers.G4Confine in
/-- **Confinement from any determined invariant.**  A family of samplers whose multiplier and
offset vectors satisfy an invariant pinned by its values on `Sdet` reads, below `L`, at most
`(2dmax+1)^{2|Sdet|}·(L m H dmax/(2 dmin^H) + H m)` positions. -/
theorem union_le_of_determining {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [DecidableEq κ]
    (Inv : (ι → ℤ) → Prop) (Sdet : Finset ι)
    (hdet : ∀ f g : ι → ℤ, Inv f → Inv g → (∀ β ∈ Sdet, f β = g β) → f = g)
    (𝓕 : Finset κ) (d t : κ → ι → ℕ) (P : κ → Finset ℕ)
    {dmin dmax m L : ℕ} (hdmin : 0 < dmin)
    (hinj : Set.InjOn (fun ν => ((fun α => (d ν α : ℤ)), (fun α => (t ν α : ℤ)))) 𝓕)
    (hI : ∀ ν ∈ 𝓕, Inv (fun α => (d ν α : ℤ)) ∧ Inv (fun α => (t ν α : ℤ)))
    (hd : ∀ ν ∈ 𝓕, ∀ α, dmin ≤ d ν α ∧ d ν α ≤ dmax)
    (ht : ∀ ν ∈ 𝓕, ∀ α, t ν α ≤ dmax)
    (hcop : ∀ ν ∈ 𝓕, ∀ α β, α ≠ β → Nat.Coprime (d ν α) (d ν β))
    (hP : ∀ ν ∈ 𝓕, ∀ n ∈ P ν, ∀ α, n % d ν α = t ν α)
    (U : ℕ → Prop) [DecidablePred U]
    (hcov : ∀ j, j < L → U j → ∃ ν ∈ 𝓕, ∃ n ∈ P ν, ∃ α, ∃ h < m,
      j = 2 * physIdx (d ν α) (t ν α) n + h) :
    (((Finset.range L).filter U).card : ℝ) ≤
      ((2 * dmax + 1 : ℕ) : ℝ) ^ (2 * Sdet.card)
        * ((L : ℝ) * m * Fintype.card ι * dmax / (2 * (dmin : ℝ) ^ Fintype.card ι)
          + Fintype.card ι * m) := by
  classical
  have hcardF : 𝓕.card ≤ (2 * dmax + 1) ^ (2 * Sdet.card) := by
    set 𝓕' := 𝓕.image (fun ν => ((fun α => (d ν α : ℤ)), (fun α => (t ν α : ℤ)))) with h𝓕'
    have hc : 𝓕.card = 𝓕'.card := (Finset.card_image_of_injOn hinj).symm
    rw [hc]
    refine RowBalance.card_pairs_le_of_determining Inv Sdet hdet 𝓕' ?_ ?_
    · intro p hp
      obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
      exact hI ν hν
    · intro p hp α
      obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
      refine ⟨?_, ?_⟩
      · show |((d ν α : ℕ) : ℤ)| ≤ (dmax : ℤ)
        rw [Nat.abs_cast]; exact_mod_cast (hd ν hν α).2
      · show |((t ν α : ℕ) : ℤ)| ≤ (dmax : ℤ)
        rw [Nat.abs_cast]; exact_mod_cast ht ν hν α
  have hU := union_card_le (ι := ι) 𝓕 d t P hdmin hd hcop hP U hcov
  have hF' : (𝓕.card : ℝ) ≤ ((2 * dmax + 1 : ℕ) : ℝ) ^ (2 * Sdet.card) := by
    exact_mod_cast hcardF
  have hpos : (0 : ℝ) ≤ (L : ℝ) * m * Fintype.card ι * dmax / (2 * (dmin : ℝ) ^ Fintype.card ι)
      + Fintype.card ι * m := by positivity
  exact le_trans hU (mul_le_mul_of_nonneg_right hF' hpos)

/-! ### Cube-local balance: the tool for the `K ≥ 3` family

`RowBalance.balanced_of_update_invariant` asks a function to ignore coordinate `i` *globally*.
The counterexample family below ignores a coordinate on each unit cube, but a **different** one
per cube, so the global criterion does not apply.  The pairing argument is entirely local, and
this is its local form. -/

/-- Toggling `i` in and out of `T`. -/
def toggle {K : ℕ} (i : Fin K) (T : Finset (Fin K)) : Finset (Fin K) :=
  if i ∈ T then T.erase i else insert i T

lemma toggle_toggle {K : ℕ} (i : Fin K) (T : Finset (Fin K)) : toggle i (toggle i T) = T := by
  classical
  by_cases hi : i ∈ T
  · have h2 : i ∉ T.erase i := fun h => (Finset.mem_erase.1 h).1 rfl
    simp only [toggle, if_pos hi, if_neg h2, Finset.insert_erase hi]
  · simp only [toggle, if_neg hi, if_pos (Finset.mem_insert_self i T), Finset.erase_insert hi]

lemma card_toggle {K : ℕ} (i : Fin K) (T : Finset (Fin K)) :
    (-1 : ℤ) ^ (toggle i T).card = -(-1 : ℤ) ^ T.card := by
  classical
  simp only [toggle]
  split_ifs with hi
  · rw [show T.card = (T.erase i).card + 1 from (Finset.card_erase_add_one hi).symm, pow_succ]
    ring
  · rw [Finset.card_insert_of_notMem hi, pow_succ]; ring

lemma toggle_ne {K : ℕ} (i : Fin K) (T : Finset (Fin K)) : toggle i T ≠ T := by
  classical
  intro hg
  have h := congrArg Finset.card hg
  simp only [toggle] at h
  split_ifs at h with hi
  · rw [Finset.card_erase_of_mem hi] at h
    have := Finset.card_pos.2 ⟨i, hi⟩; omega
  · rw [Finset.card_insert_of_notMem hi] at h; omega

/-- **The local pairing.**  An alternating sum over the subsets of `Fin K` vanishes as soon as
the summand is invariant under toggling one coordinate. -/
lemma sum_alt_toggle_zero {K : ℕ} (i : Fin K) (F : Finset (Fin K) → ℤ)
    (h : ∀ T, F (toggle i T) = F T) :
    ∑ T : Finset (Fin K), (-1 : ℤ) ^ T.card * F T = 0 := by
  classical
  refine Finset.sum_ninvolution (toggle i) (fun T => ?_) (fun T _ => toggle_ne i T)
    (fun T => Finset.mem_univ _) (fun T => toggle_toggle i T)
  rw [h, card_toggle]; ring

/-- **Cube-local balance.**  If on every unit cube some coordinate — possibly a different one on
each cube — leaves `ρ` unchanged, then `ρ` is row-balanced. -/
theorem balanced_of_cube_ignores {K s : ℕ} {ρ : (Fin K → Fin (s + 1)) → ℤ}
    (h : ∀ c : Fin K → Fin s, ∃ i : Fin K,
      ∀ T : Finset (Fin K), ρ (corner c (toggle i T)) = ρ (corner c T)) :
    Balanced ρ := by
  classical
  intro c v
  obtain ⟨i, hi⟩ := h c
  exact sum_alt_toggle_zero i (fun T => if ρ (corner c T) = v then 1 else 0)
    (fun T => by rw [hi T])

/-! ### The `K ≥ 4` counterexample family: a pointer function

R's refutation of "row-balanced ⇒ ignores a coordinate" rested on one witness at `K = 3, s = 2`,
found by search.  The cube-local criterion turns it into an explicit family for every `K ≥ 4`:
the **pointer function**

    ptrFun α  =  α (α 0)                   (coordinate `0` names the coordinate to read)

depends on *all* `K` coordinates, but on any single unit cube `α 0` takes only the two values
`c 0` and `c 0 + 1`, so `ptrFun` reads at most the three coordinates `0`, `c 0`, `c 0 + 1` there.
With `K ≥ 4` a fourth coordinate is always free, so every cube ignores one and `ptrFun` is
row-balanced.  Together with `ex` at `K = 3`, the rigidity threshold `K ≤ 2` of
`ignores_coord_of_balanced_two` is exact at **every** `K ≥ 3`. -/

/-- Reading a value of `Fin (s+1)` as a coordinate index. -/
def ptr {K s : ℕ} (hK : 0 < K) (a : Fin (s + 1)) : Fin K :=
  if h : (a : ℕ) < K then ⟨a, h⟩ else ⟨0, hK⟩

lemma ptr_lt {K s : ℕ} (hK : 0 < K) (a : Fin (s + 1)) (h : (a : ℕ) < K) :
    ptr (s := s) hK a = ⟨a, h⟩ := by
  simp [ptr, h]

/-- The pointer function: coordinate `0` names the coordinate whose value is returned. -/
def ptrFun {K s : ℕ} (hK : 0 < K) (α : Fin K → Fin (s + 1)) : ℤ :=
  ((α (ptr hK (α ⟨0, hK⟩)) : ℕ) : ℤ)

/-- **The family is row-balanced for every `K ≥ 4`.** -/
theorem ptrFun_balanced {K s : ℕ} (hK0 : 0 < K) (hK : 4 ≤ K) :
    Balanced (ptrFun (s := s) hK0) := by
  classical
  refine balanced_of_cube_ignores (fun c => ?_)
  -- the three coordinates any corner of this cube can read
  set i₀ : Fin K := ⟨0, hK0⟩ with hi₀
  set a₁ : Fin K := ptr (s := s) hK0 ((c i₀).castSucc) with ha₁
  set a₂ : Fin K := ptr (s := s) hK0 ((c i₀).succ) with ha₂
  obtain ⟨i, hi⟩ : ∃ i : Fin K, i ≠ i₀ ∧ i ≠ a₁ ∧ i ≠ a₂ := by
    by_contra hall
    push_neg at hall
    have hsub : (Finset.univ : Finset (Fin K)) ⊆ {i₀, a₁, a₂} := by
      intro x _
      have := hall x
      by_cases h1 : x = i₀
      · simp [h1]
      · by_cases h2 : x = a₁
        · simp [h2]
        · simp [this h1 h2]
    have h1 : (Finset.univ : Finset (Fin K)).card ≤ ({i₀, a₁, a₂} : Finset (Fin K)).card :=
      Finset.card_le_card hsub
    have h2 : ({i₀, a₁, a₂} : Finset (Fin K)).card ≤ 3 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      have := Finset.card_insert_le a₁ ({a₂} : Finset (Fin K))
      simp only [Finset.card_singleton] at this
      omega
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨hne0, hne1, hne2⟩ := hi
  refine ⟨i, fun T => ?_⟩
  -- the corner agrees off `i`, and `i` is none of the readable coordinates
  have hoff : ∀ j : Fin K, j ≠ i → corner c (toggle i T) j = corner c T j := by
    intro j hj
    have hmem : j ∈ toggle i T ↔ j ∈ T := by
      simp only [toggle]
      split_ifs with hiT
      · simp [Finset.mem_erase, hj]
      · simp [Finset.mem_insert, hj]
    unfold corner
    by_cases hjT : j ∈ T
    · rw [if_pos (hmem.2 hjT), if_pos hjT]
    · rw [if_neg (fun h => hjT (hmem.1 h)), if_neg hjT]
  have h0 : corner c (toggle i T) i₀ = corner c T i₀ := hoff i₀ (Ne.symm hne0)
  unfold ptrFun
  rw [h0]
  -- the read coordinate is `a₁` or `a₂`, neither of which is `i`
  have hread : ptr (s := s) hK0 (corner c T i₀) ≠ i := by
    unfold corner
    split_ifs
    · rw [← ha₂]; exact Ne.symm hne2
    · rw [← ha₁]; exact Ne.symm hne1
  rw [hoff _ hread]

/-- **The family ignores no coordinate.**  Whenever the value alphabet is wide enough to name
every coordinate (`K ≤ s + 1`), each coordinate genuinely moves `ptrFun`. -/
theorem ptrFun_not_ignoring {K s : ℕ} (hK0 : 0 < K) (hK2 : 2 ≤ K) (hKs : K ≤ s + 1) :
    ∀ j : Fin K, ∃ (α : Fin K → Fin (s + 1)) (b : Fin (s + 1)),
      ptrFun hK0 (Function.update α j b) ≠ ptrFun hK0 α := by
  classical
  have hs1 : 1 < s + 1 := by omega
  set i₀ : Fin K := ⟨0, hK0⟩ with hi₀
  set i₁ : Fin K := ⟨1, by omega⟩ with hi₁
  set z : Fin (s + 1) := ⟨0, by omega⟩ with hz
  set o : Fin (s + 1) := ⟨1, hs1⟩ with ho
  have hne : i₁ ≠ i₀ := by
    rw [hi₁, hi₀, Ne, Fin.mk.injEq]; omega
  have hptr0 : ptr (s := s) hK0 z = i₀ := by
    apply Fin.ext; simp [ptr, hz, hi₀, hK0]
  have hptr1 : ptr (s := s) hK0 o = i₁ := by
    apply Fin.ext
    have : (1 : ℕ) < K := by omega
    simp [ptr, ho, hi₁, this]
  intro j
  by_cases hj : j = i₀
  · subst hj
    set α : Fin K → Fin (s + 1) := fun x => if x = i₁ then o else z with hα
    refine ⟨α, o, ?_⟩
    have hαi₁ : α i₁ = o := by simp [hα]
    have hαi₀ : α i₀ = z := by simp [hα, Ne.symm hne]
    have e1 : ptrFun hK0 (Function.update α i₀ o) = 1 := by
      unfold ptrFun
      rw [Function.update_self, hptr1, Function.update_of_ne hne, hαi₁]
      simp [ho]
    have e2 : ptrFun hK0 α = 0 := by
      unfold ptrFun
      rw [hαi₀, hptr0, hαi₀]
      simp [hz]
    rw [e1, e2]; norm_num
  · set jv : Fin (s + 1) := ⟨(j : ℕ), lt_of_lt_of_le j.isLt hKs⟩ with hjv
    set α : Fin K → Fin (s + 1) := fun x => if x = i₀ then jv else z with hα
    refine ⟨α, o, ?_⟩
    have hptrj : ptr (s := s) hK0 jv = j := by
      apply Fin.ext; simp [ptr, hjv, j.isLt]
    have hαi₀ : α i₀ = jv := by simp [hα]
    have hαj : α j = z := by simp [hα, hj]
    have e1 : ptrFun hK0 (Function.update α j o) = 1 := by
      unfold ptrFun
      rw [Function.update_of_ne (Ne.symm hj), hαi₀, hptrj, Function.update_self]
      simp [ho]
    have e2 : ptrFun hK0 α = 0 := by
      unfold ptrFun
      rw [hαi₀, hptrj, hαj]
      simp [hz]
    rw [e1, e2]; norm_num

end NormalNumbers.G4.RowVariance
