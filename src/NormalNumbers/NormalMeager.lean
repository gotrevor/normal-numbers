/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.DisjunctiveBaire
import NormalNumbers.Wall

/-!
# Normal reals are meagre

For every integer base `b ≥ 2`, the set of base-`b` normal reals is meagre.
Together with `residual_absolutelyDisjunctive`, this gives a real that is
disjunctive in every base but normal in none: a lexicon with no statistics.

The dense-open construction is elementary.  At a sufficiently fine depth
`k`, descend into the interior of the tiny cylinder where the next
`3(k+1)` digits are zero.  Among the first `k + 3(k+1)` orbit points, more
than two thirds then visit `[0, 1/b)`.  Requiring such an excursion after
every cutoff is residual.  Wall's theorem says a normal real has visit
frequency tending to `1/b ≤ 1/2`, which is incompatible with those
arbitrarily late excursions.

As in `DisjunctiveBaire.lean`, every cylinder is replaced by its interior.
Thus no b-adic endpoint or double-expansion convention needs special
treatment, and integer translates make the argument valid on all of `ℝ`.
-/

namespace NormalNumbers

open Filter Set

private def zeroRunLength (k : ℕ) : ℕ := 3 * (k + 1)

/-- Points lying in the interior of a depth-`k` cylinder, for some `k ≥ N`,
whose next `zeroRunLength k` digits are zero. -/
private def longZeroRunOpen (b N : ℕ) : Set ℝ :=
  ⋃ k : ℕ, ⋃ (_ : N ≤ k), ⋃ z : ℤ,
    Set.Ioo ((z : ℝ) / (b : ℝ) ^ k)
      (((z : ℝ) + 1 / (b : ℝ) ^ zeroRunLength k) / (b : ℝ) ^ k)

private theorem isOpen_longZeroRunOpen (b N : ℕ) :
    IsOpen (longZeroRunOpen b N) := by
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
    isOpen_iUnion fun _ => isOpen_Ioo

private theorem dense_longZeroRunOpen (b : ℕ) (hb : 2 ≤ b) (N : ℕ) :
    Dense (longZeroRunOpen b N) := by
  rw [Metric.dense_iff]
  intro x ε hε
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hq0 : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
  have hq1 : (1 : ℝ) / b < 1 := (div_lt_one (by positivity)).mpr hbR
  have htend : Tendsto (fun k : ℕ => ((1 : ℝ) / b) ^ k)
      atTop (nhds 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hevent : ∀ᶠ k : ℕ in atTop, ((1 : ℝ) / b) ^ k < ε :=
    (tendsto_order.1 htend).2 _ hε
  obtain ⟨k, hkε, hNk⟩ := (hevent.and (eventually_ge_atTop N)).exists
  have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  have hinv : (1 : ℝ) / (b : ℝ) ^ k < ε := by
    simpa [one_div_pow] using hkε
  let R : ℕ := zeroRunLength k
  let δ : ℝ := 1 / (b : ℝ) ^ R
  let z : ℤ := ⌊x * (b : ℝ) ^ k⌋
  let t : ℝ := δ / 2
  let y : ℝ := ((z : ℝ) + t) / (b : ℝ) ^ k
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hpow1 : (1 : ℝ) ≤ (b : ℝ) ^ R := one_le_pow₀ hb1
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact (div_le_one (by positivity)).mpr hpow1
  have ht0 : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := by dsimp [t]; linarith
  have ht1 : t < 1 := htδ.trans_le hδ1
  have hfloor_lo : (z : ℝ) ≤ x * (b : ℝ) ^ k := by
    dsimp [z]
    exact_mod_cast Int.floor_le (x * (b : ℝ) ^ k)
  have hfloor_hi : x * (b : ℝ) ^ k < (z : ℝ) + 1 := by
    dsimp [z]
    exact_mod_cast Int.lt_floor_add_one (x * (b : ℝ) ^ k)
  have hy_mem : y ∈ longZeroRunOpen b N := by
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hNk,
      Set.mem_iUnion.2 ⟨z, ?_⟩⟩⟩
    constructor
    · dsimp [y]
      exact div_lt_div_of_pos_right (by linarith) hB
    · dsimp [y, t, δ, R]
      exact div_lt_div_of_pos_right (by
        change (z : ℝ) + 1 / (b : ℝ) ^ zeroRunLength k / 2 <
          (z : ℝ) + 1 / (b : ℝ) ^ zeroRunLength k
        have : 0 < (1 : ℝ) / (b : ℝ) ^ zeroRunLength k := by positivity
        linarith) hB
  have hy_lower : x - 1 / (b : ℝ) ^ k < y := by
    rw [show y = ((z : ℝ) + t) / (b : ℝ) ^ k by rfl]
    rw [lt_div_iff₀ hB]
    calc
      (x - 1 / (b : ℝ) ^ k) * (b : ℝ) ^ k
          = x * (b : ℝ) ^ k - 1 := by field_simp
      _ < (z : ℝ) := by linarith
      _ < (z : ℝ) + t := by linarith
  have hy_upper : y < x + 1 / (b : ℝ) ^ k := by
    rw [show y = ((z : ℝ) + t) / (b : ℝ) ^ k by rfl]
    rw [div_lt_iff₀ hB]
    calc
      (z : ℝ) + t < x * (b : ℝ) ^ k + 1 := by linarith
      _ = (x + 1 / (b : ℝ) ^ k) * (b : ℝ) ^ k := by field_simp
  refine ⟨y, ?_, hy_mem⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

private theorem orbit_add' (b : ℕ) (x : ℝ) (j i : ℕ) :
    orbit b x (j + i) = Int.fract (orbit b x j * (b : ℝ) ^ i) := by
  unfold orbit
  have h : Int.fract (x * (b : ℝ) ^ j) * (b : ℝ) ^ i
      = x * (b : ℝ) ^ (j + i) -
        ((⌊x * (b : ℝ) ^ j⌋ * (b ^ i : ℤ) : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [h, Int.fract_sub_intCast]

private def highZeroVisitSet (b N : ℕ) : Set ℝ :=
  {x | ∃ n ≥ N, (2 : ℝ) / 3 <
    (visitCount (orbit b x) 0 (1 / (b : ℝ)) n : ℝ) / n}

private theorem longZeroRunOpen_subset_highZeroVisitSet
    (b : ℕ) (hb : 2 ≤ b) (N : ℕ) :
    longZeroRunOpen b N ⊆ highZeroVisitSet b N := by
  classical
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨k, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hNk, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨z, hx⟩
  let R : ℕ := zeroRunLength k
  let δ : ℝ := 1 / (b : ℝ) ^ R
  have hbR0 : (0 : ℝ) < (b : ℝ) := by positivity
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hpow1 : (1 : ℝ) ≤ (b : ℝ) ^ R := one_le_pow₀ hb1
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact (div_le_one (by positivity)).mpr hpow1
  have hrun : orbit b x k ∈ Set.Ioo 0 δ := by
    apply orbit_mem_Ioo_of_mem_lift b hb x 0 δ (by norm_num) hδ1 k z
    simpa [δ, R] using hx
  have hzero : ∀ j < R, orbit b x (k + j) ∈ Set.Ico (0 : ℝ) (1 / b) := by
    intro j hj
    rw [orbit_add']
    have hprod0 : 0 ≤ orbit b x k * (b : ℝ) ^ j :=
      mul_nonneg hrun.1.le (by positivity)
    have hprod_lt : orbit b x k * (b : ℝ) ^ j < 1 / (b : ℝ) := by
      calc
        orbit b x k * (b : ℝ) ^ j
            < δ * (b : ℝ) ^ j :=
              mul_lt_mul_of_pos_right hrun.2 (by positivity)
        _ ≤ 1 / (b : ℝ) := by
          rw [le_div_iff₀ hbR0]
          calc
            δ * (b : ℝ) ^ j * (b : ℝ)
                = (b : ℝ) ^ (j + 1) / (b : ℝ) ^ R := by
                  dsimp [δ]
                  rw [pow_succ]
                  ring
            _ ≤ 1 := (div_le_one (by positivity)).mpr
              (pow_le_pow_right₀ hb1 (by omega))
    rw [Int.fract_eq_self.mpr ⟨hprod0, hprod_lt.trans_le
      ((div_le_one hbR0).mpr hb1)⟩]
    exact ⟨hprod0, hprod_lt⟩
  have hcard : R ≤ visitCount (orbit b x) 0 (1 / (b : ℝ)) (k + R) := by
    unfold visitCount
    calc
      R = (Finset.Ico k (k + R)).card := by simp
      _ ≤ ((Finset.range (k + R)).filter
          fun i => orbit b x i ∈ Set.Ico 0 (1 / (b : ℝ))).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_Ico] at hi
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨hi.2, ?_⟩
        have hz := hzero (i - k) (by omega)
        rwa [Nat.add_sub_of_le hi.1] at hz
  refine ⟨k + R, hNk.trans (Nat.le_add_right k R), ?_⟩
  have hnpos : (0 : ℝ) < (k + R : ℕ) := by
    have : 0 < R := by dsimp [R, zeroRunLength]; omega
    positivity
  have hratio : (2 : ℝ) / 3 < (R : ℝ) / (k + R : ℕ) := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 3) hnpos]
    norm_num [R, zeroRunLength]
    nlinarith
  exact hratio.trans_le
    (div_le_div_of_nonneg_right (by exact_mod_cast hcard) hnpos.le)

private theorem residual_highZeroVisitSet (b : ℕ) (hb : 2 ≤ b) (N : ℕ) :
    highZeroVisitSet b N ∈ residual ℝ :=
  Filter.mem_of_superset
    (residual_of_dense_open (isOpen_longZeroRunOpen b N)
      (dense_longZeroRunOpen b hb N))
    (longZeroRunOpen_subset_highZeroVisitSet b hb N)

/-! ## Headlines -/

/-- For each integer base `b ≥ 2`, the set of base-`b` normal reals is
meagre. -/
theorem isMeagre_setOf_isNormal (b : ℕ) (hb : 2 ≤ b) :
    IsMeagre {x : ℝ | IsNormal b x} := by
  rw [IsMeagre]
  let core : Set ℝ := ⋂ N : ℕ, highZeroVisitSet b N
  have hcore : core ∈ residual ℝ := by
    dsimp [core]
    exact countable_iInter_mem.2 (residual_highZeroVisitSet b hb)
  refine Filter.mem_of_superset hcore ?_
  intro x hx
  change ¬ IsNormal b x
  intro hnormal
  have hequid : Equidistributed (orbit b x) :=
    (isNormal_iff_equidistributed_orbit b hb x).mp hnormal
  have htend : Tendsto
      (fun n => (visitCount (orbit b x) 0 (1 / (b : ℝ)) n : ℝ) / n)
      atTop (nhds (1 / (b : ℝ))) := by
    simpa using hequid 0 (1 / (b : ℝ)) (by norm_num) (by positivity)
      ((div_le_one (by positivity : (0 : ℝ) < b)).mpr
        (by exact_mod_cast (show 1 ≤ b by omega)))
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hlim : (1 : ℝ) / b < 2 / 3 := by
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < b)
      (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  have hevent : ∀ᶠ n in atTop,
      (visitCount (orbit b x) 0 (1 / (b : ℝ)) n : ℝ) / n < 2 / 3 :=
    htend.eventually (isOpen_Iio.mem_nhds hlim)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  have hxN : x ∈ highZeroVisitSet b N := (Set.mem_iInter.mp hx) N
  obtain ⟨n, hnN, hn⟩ := hxN
  exact (not_lt_of_ge (hN n hnN).le) hn

/-- There is a real which is disjunctive in every integer base and normal
in no integer base. -/
theorem exists_absolutelyDisjunctive_forall_not_isNormal :
    ∃ x, AbsolutelyDisjunctive x ∧ ∀ b, 2 ≤ b → ¬ IsNormal b x := by
  let abnormal : Set ℝ := {x | ∀ b, 2 ≤ b → ¬ IsNormal b x}
  have habnormal : abnormal ∈ residual ℝ := by
    rw [show abnormal = ⋂ b : ℕ, {x : ℝ | 2 ≤ b → ¬ IsNormal b x} by
      ext x
      simp [abnormal]]
    refine countable_iInter_mem.2 fun b => ?_
    by_cases hb : 2 ≤ b
    · rw [show {x : ℝ | 2 ≤ b → ¬ IsNormal b x} =
          {x : ℝ | IsNormal b x}ᶜ by
        ext x
        simp [hb]]
      exact isMeagre_setOf_isNormal b hb
    · simp [hb]
  have hinter : {x : ℝ | AbsolutelyDisjunctive x} ∩ abnormal ∈ residual ℝ :=
    Filter.inter_mem residual_absolutelyDisjunctive habnormal
  obtain ⟨x, hx⟩ := nonempty_of_not_isMeagre
    (not_isMeagre_of_mem_residual hinter)
  exact ⟨x, hx.1, hx.2⟩

end NormalNumbers
