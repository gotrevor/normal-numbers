/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyMat2

/-!
# Vandehey §2: the finite state set `M_D`

Vandehey 2017 §2 defines, for `D ∈ ℕ`, the set `M_D` of integer matrices `[[α,β],[γ,δ]]` of
determinant `±D` satisfying one of six sign/size patterns (Types I–VI).  The point of the
definition is the one-line consequence he records right after it:

> `|α|, |β|, |γ|, |δ| ≤ D`, and thus `M_D` is a finite set.

That is `isMD_entry_bounds` and `finite_isMD` here.  Finiteness is what makes the transducer
of Lemma 2.1 a *finite-state* machine, hence what makes the skew product of §3 (our
`VandeheyClassEquidist`) an object with finitely many states at all.

The types, in the paper's coordinates (`α β / γ δ` = our `a b / c d`):

| type | shape |
| --- | --- |
| I   | `γ = 0`, `β ≥ 0`, `α, δ > 0`, `β < δ` |
| II  | `δ = 0`, `α ≥ 0`, `β, γ > 0`, `α < γ` |
| III | `α = 0`, `δ ≥ 0`, `β, γ > 0`, `δ < β` |
| IV  | `β = 0`, `γ ≥ 0`, `α, δ > 0`, `γ < α` |
| V   | `α < 0`, `β, γ, δ > 0`, `|α| < γ` |
| VI  | `β < 0`, `α, γ, δ > 0`, `|β| < δ` |

Note each type forces a *sign* on the determinant, which is where the entry bound comes
from: in Types I and IV the determinant is `αδ = ±D` with both factors positive, in II and
III it is `−βγ`, and in V and VI the two products reinforce rather than cancel.
-/

namespace NormalNumbers

namespace Mat2

/-- Type I: `γ = 0`, `β ≥ 0`, `α, δ > 0`, `β < δ`. -/
def TypeI (M : Mat2) : Prop := M.c = 0 ∧ 0 ≤ M.b ∧ 0 < M.a ∧ 0 < M.d ∧ M.b < M.d

/-- Type II: `δ = 0`, `α ≥ 0`, `β, γ > 0`, `α < γ`. -/
def TypeII (M : Mat2) : Prop := M.d = 0 ∧ 0 ≤ M.a ∧ 0 < M.b ∧ 0 < M.c ∧ M.a < M.c

/-- Type III: `α = 0`, `δ ≥ 0`, `β, γ > 0`, `δ < β`. -/
def TypeIII (M : Mat2) : Prop := M.a = 0 ∧ 0 ≤ M.d ∧ 0 < M.b ∧ 0 < M.c ∧ M.d < M.b

/-- Type IV: `β = 0`, `γ ≥ 0`, `α, δ > 0`, `γ < α`. -/
def TypeIV (M : Mat2) : Prop := M.b = 0 ∧ 0 ≤ M.c ∧ 0 < M.a ∧ 0 < M.d ∧ M.c < M.a

/-- Type V: `α < 0`, `β, γ, δ > 0`, `|α| < γ`. -/
def TypeV (M : Mat2) : Prop := M.a < 0 ∧ 0 < M.b ∧ 0 < M.c ∧ 0 < M.d ∧ |M.a| < M.c

/-- Type VI: `β < 0`, `α, γ, δ > 0`, `|β| < δ`. -/
def TypeVI (M : Mat2) : Prop := M.b < 0 ∧ 0 < M.a ∧ 0 < M.c ∧ 0 < M.d ∧ |M.b| < M.d

/-- **Vandehey's `M_D`**: determinant `±D`, in one of the six normal forms. -/
def IsMD (D : ℕ) (M : Mat2) : Prop :=
  (M.det = (D : ℤ) ∨ M.det = -(D : ℤ)) ∧
    (TypeI M ∨ TypeII M ∨ TypeIII M ∨ TypeIV M ∨ TypeV M ∨ TypeVI M)

/-- **The entry bound.**  Every matrix in `M_D` has all entries bounded by `D` in absolute
value.  This is the finiteness of the transducer's state set. -/
theorem isMD_entry_bounds {D : ℕ} {M : Mat2} (h : IsMD D M) :
    |M.a| ≤ (D : ℤ) ∧ |M.b| ≤ (D : ℤ) ∧ |M.c| ≤ (D : ℤ) ∧ |M.d| ≤ (D : ℤ) := by
  obtain ⟨hdet, htype⟩ := h
  have hD : |M.det| = (D : ℤ) := by
    rcases hdet with h | h <;> rw [h] <;> simp
  rw [det] at hD
  rcases htype with ⟨hc, hb, ha, hd, hbd⟩ | ⟨hd, ha, hb, hc, hac⟩ | ⟨ha, hd, hb, hc, hdb⟩ |
      ⟨hb, hc, ha, hd, hca⟩ | ⟨ha, hb, hc, hd, hac⟩ | ⟨hb, ha, hc, hd, hbd⟩
  · -- Type I: `det = α δ`
    rw [hc, mul_zero, sub_zero, abs_of_nonneg (by positivity)] at hD
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_of_nonneg (by omega)] <;> nlinarith
  · -- Type II: `det = −β γ`
    rw [hd, mul_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity)] at hD
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_of_nonneg (by omega)] <;> nlinarith
  · -- Type III: `det = −β γ`
    rw [ha, zero_mul, zero_sub, abs_neg, abs_of_nonneg (by positivity)] at hD
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_of_nonneg (by omega)] <;> nlinarith
  · -- Type IV: `det = α δ`
    rw [hb, zero_mul, sub_zero, abs_of_nonneg (by positivity)] at hD
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_of_nonneg (by omega)] <;> nlinarith
  · -- Type V: `det = α δ − β γ`, both terms `≤ 0`
    have hneg : M.a * M.d - M.b * M.c < 0 := by nlinarith
    rw [abs_of_neg hneg] at hD
    have h1 : -(M.a) * M.d + M.b * M.c = (D : ℤ) := by linarith
    have hab : |M.a| = -(M.a) := abs_of_neg ha
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hab]; nlinarith
    · rw [abs_of_nonneg (by omega)]; nlinarith
    · rw [abs_of_nonneg (by omega)]; nlinarith
    · rw [abs_of_nonneg (by omega)]; nlinarith
  · -- Type VI: `det = α δ − β γ`, both terms `≥ 0`
    have hpos : 0 < M.a * M.d - M.b * M.c := by nlinarith
    rw [abs_of_pos hpos] at hD
    have hbb : |M.b| = -(M.b) := abs_of_neg hb
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [abs_of_nonneg (by omega)]; nlinarith
    · rw [hbb]; nlinarith
    · rw [abs_of_nonneg (by omega)]; nlinarith
    · rw [abs_of_nonneg (by omega)]; nlinarith

/-- **`M_D` is finite** — the transducer of Lemma 2.1 is a finite-state machine. -/
theorem finite_isMD (D : ℕ) : {M : Mat2 | IsMD D M}.Finite := by
  have hinj : Function.Injective (fun M : Mat2 => (M.a, M.b, M.c, M.d)) := by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
    simp only [Prod.mk.injEq] at h
    simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine Set.Finite.subset (((Set.finite_Icc (-(D : ℤ)) (D : ℤ)).prod
    ((Set.finite_Icc (-(D : ℤ)) (D : ℤ)).prod
      ((Set.finite_Icc (-(D : ℤ)) (D : ℤ)).prod (Set.finite_Icc (-(D : ℤ)) (D : ℤ)))))) ?_
  rintro ⟨a, b, c, d⟩ ⟨M, hM, hEq⟩
  simp only [Prod.mk.injEq] at hEq
  obtain ⟨ha, hb, hc, hd⟩ := hEq
  subst ha; subst hb; subst hc; subst hd
  obtain ⟨h1, h2, h3, h4⟩ := isMD_entry_bounds hM
  rw [abs_le] at h1 h2 h3 h4
  exact ⟨⟨h1.1, h1.2⟩, ⟨h2.1, h2.2⟩, ⟨h3.1, h3.2⟩, h4.1, h4.2⟩

/-- **Content locator** (guard rule): the trivial instance.  `diag(D,1)` is in `M_D` — it is
the Type I matrix the transducer for `x ↦ D·x` starts from — so `M_D` is never empty. -/
theorem isMD_diag {D : ℕ} (hD : 0 < D) : IsMD D ⟨(D : ℤ), 0, 0, 1⟩ := by
  refine ⟨Or.inl ?_, Or.inl ⟨rfl, le_refl 0, ?_, one_pos, one_pos⟩⟩
  · simp [det]
  · show (0 : ℤ) < (D : ℤ)
    exact_mod_cast hD

/-- **Degenerate-case verdict** (guard rule): `M_0` is empty.  Every type forces the
determinant away from `0`, so the singular case carries no states — which is exactly why
Theorem 1.1 excludes `det = 0`. -/
theorem not_isMD_zero {M : Mat2} : ¬ IsMD 0 M := by
  rintro ⟨hdet, htype⟩
  have hD : M.det = 0 := by rcases hdet with h | h <;> simpa using h
  rw [det] at hD
  rcases htype with ⟨hc, hb, ha, hd, hbd⟩ | ⟨hd, ha, hb, hc, hac⟩ | ⟨ha, hd, hb, hc, hdb⟩ |
      ⟨hb, hc, ha, hd, hca⟩ | ⟨ha, hb, hc, hd, hac⟩ | ⟨hb, ha, hc, hd, hbd⟩ <;> nlinarith

end Mat2

end NormalNumbers
