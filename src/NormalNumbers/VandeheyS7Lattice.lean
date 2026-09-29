/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Hecke

/-!
# S7-L: the arithmetic of `Φ` — Galois repulsion in `ℤ[φ]`

The directive's fact (γ) asks for the *arithmetic* of the affine map `Φ`, not soft rigidity.  This
module supplies the first unconditional piece.

## Why this is the right object

For the additive instance `x ↦ x + φ` the affine matrix is the shear `Φ = [[1,φ],[0,1]]`, and the
transducer state at input time `n` is `s_n = O_n⁻¹ Φ P_n` with `O_n, P_n ∈ SL₂(ℤ)`.  Every entry of
`s_n` therefore lies in `ℤ[φ]`, and `det s_n = 1`: **the state is a point of the Hilbert modular
group `SL₂(ℤ[φ])`**, not merely of `SL₂(ℝ)`.  The endpoints of the state's image interval are
`ℤ[φ]`-numbers.

The bad-state phenomenon of lap 30 fact 2 is exactly "an image endpoint sits at distance `≪ |E|`
from a rational `p/q`".  In `ℤ[φ]` such a coincidence is not free: it is paid for by the Galois
conjugate.

## The theorems

* `one_le_abs_zval_mul_zconj` — `|ξ| · |ξ'| ≥ 1` for `0 ≠ ξ ∈ ℤ[φ]` (the norm form is a nonzero
  rational integer).  Conjugation is `φ ↦ ψ = goldenConj`.
* `abs_zval_ge_inv_abs_zconj` — hence `|ξ| ≥ 1/|ξ'|`.
* `dist_rat_ge` — the quantitative form: `|ξ − p/q| ≥ 1/(q · |qξ' − p|)`.
* `abs_zconj_sub_rat_ge` — **Galois repulsion**: if `ξ` is within `δ` of `p/q` then its conjugate
  is at distance at least `1/(q²δ)` from the same `p/q`.  Closeness to a rational costs conjugate
  height, and it costs it at the reciprocal rate.
* `abs_coeff_le_of_bounded`, `finite_bounded_zPairs` — a `ℤ[φ]`-number bounded together with its
  conjugate has bounded coefficients, so only finitely many such numbers exist.  This is the
  counting statement behind "the state set is discrete": states with *both* archimedean components
  bounded form a finite set, and the second component of `s_n` has size `≍ q_ℓ(y) q_n(x)`, which is
  why the state set actually encountered is infinite (`no_window_function`, from the arithmetic
  side).

## Guard rule

Content locator: `one_le_abs_zval_mul_zconj` is where integrality enters — it is false over
`ℚ(φ)`, and that is precisely why the same argument says nothing for a rational multiplier (where
Vandehey 2017 Theorem 1.1 already applies).  Degenerate cases: `ξ = 0` is excluded throughout;
`b = 0` makes `ξ = ξ' = a` and the repulsion statement degenerates to `|a − p/q| ≥ 1/q²`, the
classical bound for rationals, which is correct.
-/

namespace NormalNumbers.VandeheyS7

open NormalNumbers

/-- A number of `ℤ[φ]`, as a real. -/
noncomputable def zval (a b : ℤ) : ℝ := (a : ℝ) + (b : ℝ) * Real.goldenRatio

/-- Its Galois conjugate, `φ ↦ ψ`. -/
noncomputable def zconj (a b : ℤ) : ℝ := (a : ℝ) + (b : ℝ) * Real.goldenConj

/-- The norm form of `ℤ[φ]`: `(a + bφ)(a + bψ) = a² + ab − b²`. -/
theorem zval_mul_zconj (a b : ℤ) :
    zval a b * zconj a b = ((a ^ 2 + a * b - b ^ 2 : ℤ) : ℝ) := by
  have h := goldenNorm_factor a (-b)
  simp only [zval, zconj]
  push_cast at h ⊢
  linarith [h]

/-- Integrality: a nonzero element of `ℤ[φ]` has norm at least `1` in absolute value. -/
theorem one_le_abs_zval_mul_zconj {a b : ℤ} (h : ¬ (a = 0 ∧ b = 0)) :
    (1 : ℝ) ≤ |zval a b| * |zconj a b| := by
  have hne : ¬ (a = 0 ∧ -b = 0) := by
    rintro ⟨ha, hb⟩; exact h ⟨ha, by omega⟩
  have h1 : (1 : ℝ) ≤ |((a ^ 2 - a * (-b) - (-b) ^ 2 : ℤ) : ℝ)| := one_le_abs_goldenNorm hne
  have hrw : ((a ^ 2 - a * (-b) - (-b) ^ 2 : ℤ) : ℝ) = ((a ^ 2 + a * b - b ^ 2 : ℤ) : ℝ) := by
    push_cast; ring
  rw [hrw, ← zval_mul_zconj, abs_mul] at h1
  exact h1

theorem zval_ne_zero {a b : ℤ} (h : ¬ (a = 0 ∧ b = 0)) : zval a b ≠ 0 := by
  intro hz
  have := one_le_abs_zval_mul_zconj h
  rw [hz] at this; simp at this; linarith

theorem zconj_ne_zero {a b : ℤ} (h : ¬ (a = 0 ∧ b = 0)) : zconj a b ≠ 0 := by
  intro hz
  have := one_le_abs_zval_mul_zconj h
  rw [hz] at this; simp at this; linarith

/-- **Galois reciprocity, crude form.**  A small element of `ℤ[φ]` has a large conjugate. -/
theorem abs_zval_ge_inv_abs_zconj {a b : ℤ} (h : ¬ (a = 0 ∧ b = 0)) :
    1 / |zconj a b| ≤ |zval a b| := by
  have h1 := one_le_abs_zval_mul_zconj h
  have hc : 0 < |zconj a b| := abs_pos.2 (zconj_ne_zero h)
  rw [div_le_iff₀ hc]
  linarith [h1]

/-! ## Distance to a rational -/

theorem zval_mul_sub (a b p q : ℤ) :
    (q : ℝ) * zval a b - (p : ℝ) = zval (q * a - p) (q * b) := by
  simp only [zval]; push_cast; ring

theorem zconj_mul_sub (a b p q : ℤ) :
    (q : ℝ) * zconj a b - (p : ℝ) = zconj (q * a - p) (q * b) := by
  simp only [zconj]; push_cast; ring

/-- The coefficient pair of `qξ − p` is nonzero exactly when `ξ ≠ p/q`. -/
theorem zPair_ne_zero_of_ne_rat {a b p q : ℤ} (hq : 0 < q)
    (hne : zval a b ≠ (p : ℝ) / (q : ℝ)) : ¬ (q * a - p = 0 ∧ q * b = 0) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rintro ⟨h1, h2⟩
  have hb : b = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · omega
    · exact h
  apply hne
  have hp : (p : ℝ) = (q : ℝ) * (a : ℝ) := by
    have : p = q * a := by omega
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
  have hz : zval a b = (a : ℝ) := by simp [zval, hb]
  rw [hz, hp]
  field_simp

/-- **The separation bound.**  If `ξ = a + bφ` is not the rational `p/q`, then
`|ξ − p/q| ≥ 1 / (q · |qξ' − p|)`: the only way `ξ` can be close to `p/q` is for the conjugate
combination `qξ' − p` to be large. -/
theorem dist_rat_ge {a b p q : ℤ} (hq : 0 < q) (hne : zval a b ≠ (p : ℝ) / (q : ℝ)) :
    1 / ((q : ℝ) * |(q : ℝ) * zconj a b - (p : ℝ)|) ≤ |zval a b - (p : ℝ) / (q : ℝ)| := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hnz := zPair_ne_zero_of_ne_rat hq hne
  have key := abs_zval_ge_inv_abs_zconj hnz
  rw [← zval_mul_sub a b p q, ← zconj_mul_sub a b p q] at key
  have hfac : (q : ℝ) * (zval a b - (p : ℝ) / (q : ℝ)) = (q : ℝ) * zval a b - (p : ℝ) := by
    field_simp
  have habs : |(q : ℝ) * zval a b - (p : ℝ)| = (q : ℝ) * |zval a b - (p : ℝ) / (q : ℝ)| := by
    rw [← hfac, abs_mul, abs_of_pos hq0]
  rw [habs] at key
  have hcpos : 0 < |(q : ℝ) * zconj a b - (p : ℝ)| := by
    rw [zconj_mul_sub]
    exact abs_pos.2 (zconj_ne_zero hnz)
  rw [div_le_iff₀ hcpos] at key
  rw [div_le_iff₀ (by positivity)]
  nlinarith [key]

/-- **Galois repulsion.**  If a `ℤ[φ]`-number sits within `δ` of the rational `p/q`, then its
conjugate sits at distance at least `1/(q²δ)` from that same rational.  This is the arithmetic
price of a "bad state": an image endpoint that hugs a rational forces the conjugate component of
the state to be large, at the reciprocal rate. -/
theorem abs_zconj_sub_rat_ge {a b p q : ℤ} (hq : 0 < q) {δ : ℝ} (hδ : 0 < δ)
    (hne : zval a b ≠ (p : ℝ) / (q : ℝ))
    (hclose : |zval a b - (p : ℝ) / (q : ℝ)| ≤ δ) :
    1 / ((q : ℝ) ^ 2 * δ) ≤ |zconj a b - (p : ℝ) / (q : ℝ)| := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hnz := zPair_ne_zero_of_ne_rat hq hne
  have key := dist_rat_ge hq hne
  have hfac : (q : ℝ) * (zconj a b - (p : ℝ) / (q : ℝ)) = (q : ℝ) * zconj a b - (p : ℝ) := by
    field_simp
  have hcabs : |(q : ℝ) * zconj a b - (p : ℝ)| = (q : ℝ) * |zconj a b - (p : ℝ) / (q : ℝ)| := by
    rw [← hfac, abs_mul, abs_of_pos hq0]
  have hCpos : 0 < |zconj a b - (p : ℝ) / (q : ℝ)| := by
    have h0 : 0 < |(q : ℝ) * zconj a b - (p : ℝ)| := by
      rw [zconj_mul_sub]; exact abs_pos.2 (zconj_ne_zero hnz)
    rw [hcabs] at h0
    nlinarith [abs_nonneg (zconj a b - (p : ℝ) / (q : ℝ)), h0]
  rw [hcabs] at key
  have h1 : 1 / ((q : ℝ) * ((q : ℝ) * |zconj a b - (p : ℝ) / (q : ℝ)|)) ≤ δ :=
    le_trans key hclose
  rw [div_le_iff₀ (by positivity)] at h1
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h1]

/-! ## The form the state actually needs: a quotient of `ℤ[φ]`-numbers -/

theorem zval_lin (b1 b2 d1 d2 p q : ℤ) :
    zval (q * b1 - p * d1) (q * b2 - p * d2)
      = (q : ℝ) * zval b1 b2 - (p : ℝ) * zval d1 d2 := by
  simp only [zval]; push_cast; ring

theorem zconj_lin (b1 b2 d1 d2 p q : ℤ) :
    zconj (q * b1 - p * d1) (q * b2 - p * d2)
      = (q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2 := by
  simp only [zconj]; push_cast; ring

/-- **Galois repulsion for a state endpoint.**  A transducer state of the additive instance has
entries in `ℤ[φ]`, so each endpoint of its image interval is a quotient `β/δ` of `ℤ[φ]`-numbers.
Such a quotient can only hug the rational `p/q` at a price paid in the conjugates: the distance is
at least `1 / (q · |δ| · |qβ' − pδ'|)`.

This is the state-level form of `dist_rat_ge`, and it is the arithmetic content behind "a bad
state is expensive": a state whose image straddles `1/k` at scale `≪ γ(I_w)` must have a large
conjugate component, i.e. must sit far out in the second archimedean factor of the Hilbert modular
group `SL₂(ℤ[φ])`. -/
theorem zquot_sub_rat_ge {b1 b2 d1 d2 p q : ℤ} (hq : 0 < q) (hd : zval d1 d2 ≠ 0)
    (hne : zval b1 b2 / zval d1 d2 ≠ (p : ℝ) / (q : ℝ)) :
    1 / ((q : ℝ) * |zval d1 d2| * |(q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2|)
      ≤ |zval b1 b2 / zval d1 d2 - (p : ℝ) / (q : ℝ)| := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hdpos : 0 < |zval d1 d2| := abs_pos.2 hd
  -- the numerator pair is nonzero
  have hnz : ¬ (q * b1 - p * d1 = 0 ∧ q * b2 - p * d2 = 0) := by
    rintro ⟨h1, h2⟩
    apply hne
    have : (q : ℝ) * zval b1 b2 - (p : ℝ) * zval d1 d2 = 0 := by
      rw [← zval_lin, h1, h2]; simp [zval]
    field_simp
    linarith [this]
  have key := abs_zval_ge_inv_abs_zconj hnz
  rw [zval_lin, zconj_lin] at key
  -- rewrite the difference
  have hcpos : 0 < |(q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2| := by
    rw [← zconj_lin]; exact abs_pos.2 (zconj_ne_zero hnz)
  have hdiff : zval b1 b2 / zval d1 d2 - (p : ℝ) / (q : ℝ)
      = ((q : ℝ) * zval b1 b2 - (p : ℝ) * zval d1 d2) / ((q : ℝ) * zval d1 d2) := by
    field_simp
    try ring
  rw [hdiff, abs_div, abs_mul, abs_of_pos hq0]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [div_le_iff₀ hcpos] at key
  nlinarith [key, mul_pos hq0 hdpos, abs_nonneg ((q : ℝ) * zval b1 b2 - (p : ℝ) * zval d1 d2)]

/-! ## Discreteness: bounded together with its conjugate ⟹ finitely many -/

/-- Coefficient bounds from a two-sided bound.  `b` is recovered as `(ξ − ξ')/√5`. -/
theorem abs_coeff_le_of_bounded {a b : ℤ} {R : ℝ} (hR : 0 ≤ R)
    (h1 : |zval a b| ≤ R) (h2 : |zconj a b| ≤ R) :
    |(b : ℝ)| ≤ R ∧ |(a : ℝ)| ≤ 3 * R := by
  have hsub : zval a b - zconj a b = (b : ℝ) * Real.sqrt 5 := by
    have h5 : Real.goldenRatio - Real.goldenConj = Real.sqrt 5 := by
      simp [Real.goldenRatio, Real.goldenConj]
      try ring
    simp only [zval, zconj]
    rw [← h5]; ring
  have hs5 : (2 : ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  have hb : |(b : ℝ)| * Real.sqrt 5 ≤ 2 * R := by
    have : |(b : ℝ) * Real.sqrt 5| ≤ 2 * R := by
      rw [← hsub]
      calc |zval a b - zconj a b| ≤ |zval a b| + |zconj a b| := abs_sub _ _
        _ ≤ 2 * R := by linarith
    rwa [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 5)] at this
  have hbR : |(b : ℝ)| ≤ R := by nlinarith [abs_nonneg ((b : ℝ))]
  refine ⟨hbR, ?_⟩
  have hphi : Real.goldenRatio ≤ 2 := by
    have := Real.goldenRatio_lt_two
    linarith
  have hphi0 : (0 : ℝ) ≤ Real.goldenRatio := le_of_lt Real.goldenRatio_pos
  have ha : (a : ℝ) = zval a b - (b : ℝ) * Real.goldenRatio := by simp [zval]
  calc |(a : ℝ)| = |zval a b - (b : ℝ) * Real.goldenRatio| := by rw [ha]
    _ ≤ |zval a b| + |(b : ℝ) * Real.goldenRatio| := abs_sub _ _
    _ ≤ R + R * 2 := by
        have : |(b : ℝ) * Real.goldenRatio| ≤ R * 2 := by
          rw [abs_mul, abs_of_nonneg hphi0]
          exact mul_le_mul hbR hphi hphi0 hR
        linarith
    _ = 3 * R := by ring

/-- **Discreteness of the state lattice.**  Only finitely many elements of `ℤ[φ]` are bounded by
`R` simultaneously with their conjugates. -/
theorem finite_bounded_zPairs (R : ℝ) :
    {ab : ℤ × ℤ | |zval ab.1 ab.2| ≤ R ∧ |zconj ab.1 ab.2| ≤ R}.Finite := by
  by_cases hR : 0 ≤ R
  swap
  · replace hR : R < 0 := not_le.1 hR
    apply Set.Finite.subset (Set.finite_empty)
    rintro ⟨a, b⟩ ⟨h1, -⟩
    exact absurd (le_trans (abs_nonneg _) h1) (not_le.2 hR)
  · have hsub : {ab : ℤ × ℤ | |zval ab.1 ab.2| ≤ R ∧ |zconj ab.1 ab.2| ≤ R} ⊆
        (Set.Icc (-⌈3 * R⌉) ⌈3 * R⌉) ×ˢ (Set.Icc (-⌈3 * R⌉) ⌈3 * R⌉) := by
      rintro ⟨a, b⟩ ⟨h1, h2⟩
      obtain ⟨hb, ha⟩ := abs_coeff_le_of_bounded hR h1 h2
      have hRle : R ≤ 3 * R := by linarith
      have hb' : |(b : ℝ)| ≤ 3 * R := le_trans hb hRle
      constructor
      · simp only [Set.mem_Icc]
        constructor
        · have : -(3 * R) ≤ (a : ℝ) := neg_le_of_abs_le ha
          have h3 : (-⌈3 * R⌉ : ℝ) ≤ (a : ℝ) := by
            have := Int.le_ceil (3 * R)
            push_cast
            linarith
          exact_mod_cast h3
        · have : (a : ℝ) ≤ 3 * R := le_of_abs_le ha
          have h3 : (a : ℝ) ≤ (⌈3 * R⌉ : ℝ) := le_trans this (Int.le_ceil _)
          exact_mod_cast h3
      · simp only [Set.mem_Icc]
        constructor
        · have : -(3 * R) ≤ (b : ℝ) := neg_le_of_abs_le hb'
          have h3 : (-⌈3 * R⌉ : ℝ) ≤ (b : ℝ) := by
            have := Int.le_ceil (3 * R)
            push_cast
            linarith
          exact_mod_cast h3
        · have : (b : ℝ) ≤ 3 * R := le_of_abs_le hb'
          have h3 : (b : ℝ) ≤ (⌈3 * R⌉ : ℝ) := le_trans this (Int.le_ceil _)
          exact_mod_cast h3
    exact Set.Finite.subset ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)) hsub

#print axioms abs_zconj_sub_rat_ge
#print axioms zquot_sub_rat_ge
#print axioms finite_bounded_zPairs

end NormalNumbers.VandeheyS7
