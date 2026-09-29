/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-ST: the straddle cap — Galois repulsion forbids a narrow state from straddling

Directive fact (β) is the whole reason the pullback bound needs a width floor: a state whose image
`J` straddles a digit boundary `1/k` at a scale far below `γ(I_w)` has `γ(s⁻¹ I_w) ≈ 1/2`.  And the
straddle is also what blocks the *cancellation* that would make the clock rate unconditional
(S7-RD): a read of the large digit `a` costs `2 log a` of lag, and the emitter should immediately buy
it back as a block of `L ≍ 2 log a / log φ²` digits — **but only if the narrow image lies inside a
cylinder at all.**  Straddling is exactly the failure of that.

So the cancellation and (β) are the same obstruction, and this module prices it with the
**arithmetic of `Φ`**, which is what the directive asks for.  The state's image endpoints are
quotients `β/δ` of `ℤ[φ]`-numbers, and `VandeheyS7Lattice.zquot_sub_rat_ge` says such a quotient
repels rationals: `|β/δ − p/q| ≥ 1 / (q·|δ|·|qβ' − pδ'|)`.  Bounding the conjugate combination by
`q(B + D)` where `B, D` bound `|β'|, |δ'|`, an image of width below `1/(Q²·|δ|·(B+D))`
**cannot contain any rational of denominator `≤ Q`** — so it cannot straddle a digit boundary of
depth `≤ Q`, and the emitter must fire.

`image_no_rational_of_zquot` is that statement.  `notMem_uIcc_of_gap` is its elementary core, kept
separate because it is the only place the interval geometry enters.

## Where this degrades — the wall, located

The cap is effective only while `|δ|·(B+D)` is small compared with `1/width`.  For the Raney state
`Oₙ⁻¹ Φ Pₙ` the conjugate entries grow: `Φ' = diag(ψ,1)` and the conjugate height runs like
`q_out·q_in`, so `log(|δ|(B+D)) ≍ 2λn` while the lag we want to drain is `O(1)`.  **Galois repulsion
therefore controls the straddle at the first `O(1)` scales and weakens linearly after that.**  That is
the precise location of the self-joining wall: what is needed is not a better repulsion estimate but
equidistribution in the *second archimedean place* — the frequency with which the conjugate height is
large relative to the scale.  Recording this is the point: the arithmetic of `Φ` does real work here,
and it is now visible exactly how much.
-/
import NormalNumbers.VandeheyS7Lattice
import NormalNumbers.VandeheyS7Read

namespace NormalNumbers.VandeheyS7

/-- **The elementary core.**  A point further from `u` than `v` is, cannot lie between them. -/
theorem notMem_uIcc_of_gap {u v r : ℝ} (h : |v - u| < |u - r|) : r ∉ Set.uIcc u v := by
  intro hmem
  have hkey : |u - r| ≤ |v - u| := by
    rcases Set.mem_uIcc.1 hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_sub_comm u r, abs_of_nonneg (by linarith : (0:ℝ) ≤ r - u),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ v - u)]
      linarith
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u - r), abs_sub_comm v u,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ u - v)]
      linarith
  linarith

/-- **The straddle cap.**  An image interval with one endpoint a `ℤ[φ]`-quotient of conjugate
height `≤ B + D`, and width below `1/(Q²·|δ|·(B+D))`, contains **no** rational of denominator at
most `Q` — so it straddles no digit boundary of that depth, and the emitter must fire.

This is the arithmetic of `Φ` doing the work that no distortion estimate can: `zquot_sub_rat_ge`
is false over `ℚ(φ)` and true over `ℤ[φ]`. -/
theorem image_no_rational_of_zquot {b1 b2 d1 d2 : ℤ} {v B D : ℝ} {Q : ℕ}
    (hd : zval d1 d2 ≠ 0) (hirr : Irrational (zval b1 b2 / zval d1 d2))
    (hB : |zconj b1 b2| ≤ B) (hD : |zconj d1 d2| ≤ D) (hQ : 1 ≤ Q)
    (hBD : 0 < B + D)
    (hw : |v - zval b1 b2 / zval d1 d2|
            < 1 / ((Q : ℝ) ^ 2 * |zval d1 d2| * (B + D))) :
    ∀ p q : ℤ, 0 < q → q ≤ (Q : ℤ) → |p| ≤ q →
      (p : ℝ) / (q : ℝ) ∉ Set.uIcc (zval b1 b2 / zval d1 d2) v := by
  intro p q hq hqQ hpq
  have hq0 : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hdpos : (0:ℝ) < |zval d1 d2| := abs_pos.2 hd
  have hQ0 : (0:ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hqQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
  have hne : zval b1 b2 / zval d1 d2 ≠ (p : ℝ) / (q : ℝ) := by
    intro hc
    exact hirr ⟨(p : ℚ) / (q : ℚ), by push_cast; exact hc.symm⟩
  -- the numerator pair is nonzero, so the conjugate combination is
  have hnzpair : ¬ (q * b1 - p * d1 = 0 ∧ q * b2 - p * d2 = 0) := by
    rintro ⟨h1, h2⟩
    apply hne
    have hz : (q : ℝ) * zval b1 b2 - (p : ℝ) * zval d1 d2 = 0 := by
      rw [← zval_lin, h1, h2]; simp [zval]
    field_simp
    linarith [hz]
  have hcpos : (0:ℝ) < |(q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2| := by
    rw [← zconj_lin]; exact abs_pos.2 (zconj_ne_zero hnzpair)
  -- Galois repulsion at the state endpoint
  have hrep := zquot_sub_rat_ge hq hd hne
  -- bound the conjugate combination by `q (B + D)`
  have hconj : |(q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2| ≤ (q : ℝ) * (B + D) := by
    have hpR : |(p : ℝ)| ≤ (q : ℝ) := by
      have h := (by exact_mod_cast hpq : ((|p| : ℤ) : ℝ) ≤ (q : ℝ))
      rwa [Int.cast_abs] at h
    calc |(q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2|
        ≤ |(q : ℝ) * zconj b1 b2| + |(p : ℝ) * zconj d1 d2| := abs_sub _ _
      _ = (q : ℝ) * |zconj b1 b2| + |(p : ℝ)| * |zconj d1 d2| := by
          rw [abs_mul, abs_mul, abs_of_pos hq0]
      _ ≤ (q : ℝ) * B + (q : ℝ) * D := by
          gcongr
      _ = (q : ℝ) * (B + D) := by ring
  -- so the repulsion floor is at least `1/(Q²|δ|(B+D))`
  have hfloor : 1 / ((Q : ℝ) ^ 2 * |zval d1 d2| * (B + D))
      ≤ 1 / ((q : ℝ) * |zval d1 d2| * |(q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2|) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    calc (q : ℝ) * |zval d1 d2| * |(q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2|
        ≤ (q : ℝ) * |zval d1 d2| * ((q : ℝ) * (B + D)) := by gcongr
      _ = ((q : ℝ) * (q : ℝ)) * |zval d1 d2| * (B + D) := by ring
      _ ≤ ((Q : ℝ) * (Q : ℝ)) * |zval d1 d2| * (B + D) := by gcongr <;> positivity
      _ = (Q : ℝ) ^ 2 * |zval d1 d2| * (B + D) := by ring
  refine notMem_uIcc_of_gap ?_
  calc |v - zval b1 b2 / zval d1 d2|
      < 1 / ((Q : ℝ) ^ 2 * |zval d1 d2| * (B + D)) := hw
    _ ≤ 1 / ((q : ℝ) * |zval d1 d2| * |(q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2|) := hfloor
    _ ≤ |zval b1 b2 / zval d1 d2 - (p : ℝ) / (q : ℝ)| := hrep

section Audit

#print axioms notMem_uIcc_of_gap
#print axioms image_no_rational_of_zquot

end Audit

end NormalNumbers.VandeheyS7
