/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Disjunctive
import Mathlib.Topology.Baire.Lemmas

/-!
# Absolutely disjunctive reals are residual

The set of reals disjunctive in every integer base is residual (comeager).
This is the Baire-category half of Calude--Zamfirescu's observation that
"the typical real is a lexicon."

For an interval `(a, c) ⊆ (0, 1)`, `orbitLiftOpen b a c` is the union of
the interiors of every inverse-image cylinder for the map
`x ↦ Int.fract (b ^ n * x)`.  The union is open and dense.  Intersecting
these sets over rational `a, c` makes every multiply-by-`b` orbit dense;
intersecting again over the countable set of bases gives
`residual_absolutelyDisjunctive`.

The use of open cylinder interiors is deliberate: b-adic endpoints have two
digit expansions, but no endpoint ever enters the argument.  The construction
is periodic over all integer translates, so the theorem is naturally stated
on all of `ℝ`, consistently with `IsDisjunctive` and `IsNormal` reading the
fractional part.
-/

namespace NormalNumbers

open Filter Set

/-! ## Periodic open lifts of orbit targets -/

/-- The open periodic lift of `(a, c)` through every iterate of the
multiply-by-`b` map.  At depth `n`, the component indexed by `z : ℤ` is
`((z+a)/b^n, (z+c)/b^n)`. -/
def orbitLiftOpen (b : ℕ) (a c : ℝ) : Set ℝ :=
  ⋃ n : ℕ, ⋃ z : ℤ,
    Set.Ioo (((z : ℝ) + a) / (b : ℝ) ^ n)
      (((z : ℝ) + c) / (b : ℝ) ^ n)

theorem isOpen_orbitLiftOpen (b : ℕ) (a c : ℝ) :
    IsOpen (orbitLiftOpen b a c) := by
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Ioo

/-- A point in one lifted open cylinder has its depth-`n` orbit point in
the target interval.  The strict inequalities keep the proof away from both
b-adic boundaries. -/
theorem orbit_mem_Ioo_of_mem_lift (b : ℕ) (hb : 2 ≤ b) (x a c : ℝ)
    (ha : 0 ≤ a) (hc : c ≤ 1) (n : ℕ) (z : ℤ)
    (hx : x ∈ Set.Ioo (((z : ℝ) + a) / (b : ℝ) ^ n)
      (((z : ℝ) + c) / (b : ℝ) ^ n)) :
    orbit b x n ∈ Set.Ioo a c := by
  have hB : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hlo : (z : ℝ) + a < x * (b : ℝ) ^ n :=
    (div_lt_iff₀ hB).mp hx.1
  have hhi : x * (b : ℝ) ^ n < (z : ℝ) + c :=
    (lt_div_iff₀ hB).mp hx.2
  have ht0 : 0 ≤ x * (b : ℝ) ^ n - (z : ℝ) := by linarith
  have ht1 : x * (b : ℝ) ^ n - (z : ℝ) < 1 := by linarith
  have horbit : orbit b x n = x * (b : ℝ) ^ n - (z : ℝ) := by
    unfold orbit
    conv_lhs =>
      congr
      rw [show x * (b : ℝ) ^ n =
        (x * (b : ℝ) ^ n - (z : ℝ)) + (z : ℝ) by ring]
    rw [Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨ht0, ht1⟩]
  rw [horbit]
  constructor <;> linarith

/-- The periodic lift of any nonempty interval in `[0,1]` is dense.  A
depth-`n` component has mesh `b⁻ⁿ`; the midpoint of the target interval in
the component based at `⌊x bⁿ⌋` lies within one mesh width of `x`. -/
theorem dense_orbitLiftOpen (b : ℕ) (hb : 2 ≤ b) (a c : ℝ)
    (ha : 0 ≤ a) (hac : a < c) (hc : c ≤ 1) :
    Dense (orbitLiftOpen b a c) := by
  rw [Metric.dense_iff]
  intro x ε hε
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hq1 : (1 : ℝ) / b < 1 := (div_lt_one (by positivity)).mpr hbR
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((1 : ℝ) / b) ^ n < ε :=
    exists_pow_lt_of_lt_one hε hq1
  have hB : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hinv : (1 : ℝ) / (b : ℝ) ^ n < ε := by
    simpa [one_div_pow] using hn
  let z : ℤ := ⌊x * (b : ℝ) ^ n⌋
  let t : ℝ := (a + c) / 2
  let y : ℝ := ((z : ℝ) + t) / (b : ℝ) ^ n
  have hat : a < t := by dsimp [t]; linarith
  have htc : t < c := by dsimp [t]; linarith
  have ht0 : 0 < t := lt_of_le_of_lt ha hat
  have ht1 : t < 1 := lt_of_lt_of_le htc hc
  have hfloor_lo : (z : ℝ) ≤ x * (b : ℝ) ^ n := by
    dsimp [z]
    exact_mod_cast Int.floor_le (x * (b : ℝ) ^ n)
  have hfloor_hi : x * (b : ℝ) ^ n < (z : ℝ) + 1 := by
    dsimp [z]
    exact_mod_cast Int.lt_floor_add_one (x * (b : ℝ) ^ n)
  have hy_mem : y ∈ orbitLiftOpen b a c := by
    refine Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨z, ?_⟩⟩
    constructor
    · dsimp [y]
      exact div_lt_div_of_pos_right (by linarith) hB
    · dsimp [y]
      exact div_lt_div_of_pos_right (by linarith) hB
  have hy_lower : x - 1 / (b : ℝ) ^ n < y := by
    rw [show y = ((z : ℝ) + t) / (b : ℝ) ^ n by rfl]
    rw [lt_div_iff₀ hB]
    calc
      (x - 1 / (b : ℝ) ^ n) * (b : ℝ) ^ n
          = x * (b : ℝ) ^ n - 1 := by field_simp
      _ < (z : ℝ) := by linarith
      _ < (z : ℝ) + t := by linarith
  have hy_upper : y < x + 1 / (b : ℝ) ^ n := by
    rw [show y = ((z : ℝ) + t) / (b : ℝ) ^ n by rfl]
    rw [div_lt_iff₀ hB]
    calc
      (z : ℝ) + t < x * (b : ℝ) ^ n + 1 := by linarith
      _ = (x + 1 / (b : ℝ) ^ n) * (b : ℝ) ^ n := by field_simp
  refine ⟨y, ?_, hy_mem⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem orbitLiftOpen_subset_hits (b : ℕ) (hb : 2 ≤ b) (a c : ℝ)
    (ha : 0 ≤ a) (hc : c ≤ 1) :
    orbitLiftOpen b a c ⊆ {x | ∃ n, orbit b x n ∈ Set.Ico a c} := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨n, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨z, hx⟩
  have hn := orbit_mem_Ioo_of_mem_lift b hb x a c ha hc n z hx
  exact ⟨n, ⟨hn.1.le, hn.2⟩⟩

/-! ## Residual disjunctivity -/

/-- For every base `b ≥ 2`, the set of base-`b` disjunctive reals is
residual. -/
theorem residual_isDisjunctive (b : ℕ) (hb : 2 ≤ b) :
    {x : ℝ | IsDisjunctive b x} ∈ residual ℝ := by
  let core : Set ℝ := ⋂ q : ℚ, ⋂ r : ℚ,
    if (0 : ℝ) ≤ q ∧ (q : ℝ) < r ∧ (r : ℝ) ≤ 1
      then orbitLiftOpen b q r else Set.univ
  have hcore : core ∈ residual ℝ := by
    dsimp [core]
    refine countable_iInter_mem.2 fun q => countable_iInter_mem.2 fun r => ?_
    split_ifs with h
    · exact residual_of_dense_open (isOpen_orbitLiftOpen b q r)
        (dense_orbitLiftOpen b hb q r h.1 h.2.1 h.2.2)
    · exact Filter.univ_mem
  refine Filter.mem_of_superset hcore ?_
  intro x hx
  rw [Set.mem_iInter] at hx
  intro a c ha hac hc
  obtain ⟨q : ℚ, haq, hqc⟩ := exists_rat_btwn hac
  obtain ⟨r : ℚ, hqr, hrc⟩ := exists_rat_btwn hqc
  have hvalid : (0 : ℝ) ≤ q ∧ (q : ℝ) < r ∧ (r : ℝ) ≤ 1 :=
    ⟨ha.trans haq.le, hqr, hrc.le.trans hc⟩
  have hxqr := hx q
  rw [Set.mem_iInter] at hxqr
  have hxopen : x ∈ orbitLiftOpen b q r := by
    simpa [hvalid] using hxqr r
  obtain ⟨n, hn⟩ := orbitLiftOpen_subset_hits b hb q r hvalid.1 hvalid.2.2 hxopen
  exact ⟨n, ⟨haq.le.trans hn.1, hn.2.trans hrc⟩⟩

/-- **Calude--Zamfirescu (1999):** the absolutely disjunctive reals form a
residual subset of `ℝ`. -/
theorem residual_absolutelyDisjunctive :
    {x : ℝ | AbsolutelyDisjunctive x} ∈ residual ℝ := by
  rw [show {x : ℝ | AbsolutelyDisjunctive x} =
      ⋂ b : ℕ, {x : ℝ | 2 ≤ b → IsDisjunctive b x} by
    ext x
    simp [AbsolutelyDisjunctive]]
  refine countable_iInter_mem.2 fun b => ?_
  by_cases hb : 2 ≤ b
  · simpa [hb] using residual_isDisjunctive b hb
  · simp [hb]

end NormalNumbers
