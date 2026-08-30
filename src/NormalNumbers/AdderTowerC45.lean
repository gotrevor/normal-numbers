/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG
import NormalNumbers.LnTwoIrrational

/-!
# Tower claims C4 and C5: base-3 two-track families (kernel tier)

Brief: `BRIEF-adder-tower.md` phase C items 4–5; dossier
`EVIDENCE-2026-08-29-tower-formalization.md` §C4–C5.

**C4** (base-3 four-channel single-digit family): for `X, Y` not both
rational, at least one of — digit 0 i.o. in `Y` · digit 2 i.o. in `3Y` ·
digit 0 i.o. in `3X+Y` · digit 2 i.o. in `X+Y`.  Instances (X = ln 2,
Y = ln 3): ln 3, ln 27, ln 24, ln 6.

**C5** (escape from Cantor): for `X, Y` not both rational, at least one of
`Y, 2Y, X+4Y, 2X, 4X` has ternary digit 1 i.o.  Instances: ln 3, ln 9,
ln 162, ln 4, ln 16.  The `y = x` instance (one of `x, 2x, 4x, 5x` has
digit 1 i.o. for irrational `x`) is subsumed by C1 (`c1_ternary_digit`) —
per the brief no extra theorem is stated; C5's value is the two-real form.

Certificates emitted and re-verified by `adder_baseg_emit.py c4 / c5`
(24 ambient / 6 live and 80 ambient / 6 live, fixed points, agreeing with
the dossier's collapse verdicts), checked here by kernel `decide` against
our own `gfamPred` over the packed alphabet `σ = x + 3y < 9`.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-! ## C4 -/

/-- The C4 family: channels `(0,1)/0 · (0,3)/2 · (3,1)/0 · (1,1)/2`. -/
def c4Fam : List ZChannel :=
  [⟨0, 1, [0]⟩, ⟨0, 3, [2]⟩, ⟨3, 1, [0]⟩, ⟨1, 1, [2]⟩]

def c4live : ℕ → Bool := fun s => [1, 16, 17, 19, 20, 22].contains s
def c4rho : ℕ → ℕ := fun s =>
  (([(17, 2), (19, 1), (20, 2)] : List (ℕ × ℕ)).lookup s).getD 0
def c4omega : ℕ → ℕ := fun s =>
  (([(4, 1), (14, 1), (23, 1)] : List (ℕ × ℕ)).lookup s).getD 0
def c4forced : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(1, (3, 1)), (16, (4, 16)), (22, (5, 22))] : List (ℕ × ℕ × ℕ)).lookup s

theorem c4_cert : checkCertA (fun σ s' => gfamPred 3 c4Fam (σ % 3) (σ / 3) s')
    (3 ^ 2) 24 c4live c4rho c4omega c4forced = true := by decide

/-- **C4, universal form**: for reals `X, Y` not both rational, ternary
digit 0 occurs i.o. in `Y`, or 2 in `3Y`, or 0 in `3X+Y`, or 2 in `X+Y`. -/
theorem c4_disjunction_universal (X Y : ℝ)
    (hXY : ¬ (∃ p : ℚ, (p:ℝ) = X) ∨ ¬ (∃ q : ℚ, (q:ℝ) = Y)) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 Y [0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (3 * Y) [2] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (3 * X + Y) [0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (X + Y) [2] n) := by
  have hirr : Irrational X ∨ Irrational Y := by
    rcases hXY with hX | hY
    · exact Or.inl fun ⟨p, hp⟩ => hX ⟨p, hp⟩
    · exact Or.inr fun ⟨q, hq⟩ => hY ⟨q, hq⟩
  obtain ⟨ch, hch, hocc⟩ := signed_engine_g 3 (by norm_num) c4Fam (by decide) c4_cert
    X Y hirr (by decide) (by decide) (by decide)
  fin_cases hch
  · refine Or.inl ?_
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 3 (((0:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [0] n := hocc
    rwa [show ((0:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = Y from by push_cast; ring] at h
  · refine Or.inr (Or.inl ?_)
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 3 (((0:ℤ):ℝ) * X + ((3:ℤ):ℝ) * Y) [2] n := hocc
    rwa [show ((0:ℤ):ℝ) * X + ((3:ℤ):ℝ) * Y = 3 * Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inl ?_))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 3 (((3:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [0] n := hocc
    rwa [show ((3:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = 3 * X + Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr ?_))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 3 (((1:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [2] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = X + Y from by push_cast; ring] at h

/-- **C4** (ln-instance): ternary digit 0 occurs i.o. in ln 3, or 2 in
ln 27, or 0 in ln 24, or 2 in ln 6. -/
theorem c4_disjunction :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (Real.log 3) [0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (Real.log 27) [2] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (Real.log 24) [0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (Real.log 6) [2] n) := by
  have h27 : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27:ℝ) = 3 ^ 3 from by norm_num, Real.log_pow]
    push_cast; ring
  have h24 : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
    rw [show (24:ℝ) = 2 ^ 3 * 3 from by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6:ℝ) = 2 * 3 from by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [h27, h24, h6]
  exact c4_disjunction_universal (Real.log 2) (Real.log 3)
    (Or.inl fun ⟨p, hp⟩ => irrational_log_two ⟨p, hp⟩)

/-! ## C5 -/

/-- The C5 family (escape from Cantor): channels
`(0,1) · (0,2) · (1,4) · (2,0) · (4,0)`, all avoiding ternary digit 1. -/
def c5Fam : List ZChannel :=
  [⟨0, 1, [1]⟩, ⟨0, 2, [1]⟩, ⟨1, 4, [1]⟩, ⟨2, 0, [1]⟩, ⟨4, 0, [1]⟩]

def c5live : ℕ → Bool := fun s => [0, 7, 9, 70, 72, 79].contains s
def c5omega : ℕ → ℕ := fun s =>
  (([(2, 1), (5, 1), (20, 2), (22, 1), (25, 1), (27, 2), (29, 3), (30, 2),
     (32, 1), (37, 1), (39, 2), (40, 2), (42, 1), (47, 1), (49, 2), (50, 3),
     (52, 2), (54, 1), (57, 1), (59, 2), (74, 1), (77, 1)] :
    List (ℕ × ℕ)).lookup s).getD 0
def c5forced : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (7, (6, 7)), (9, (6, 9)), (70, (2, 70)), (72, (2, 72)),
    (79, (8, 79))] : List (ℕ × ℕ × ℕ)).lookup s

theorem c5_cert : checkCertA (fun σ s' => gfamPred 3 c5Fam (σ % 3) (σ / 3) s')
    (3 ^ 2) 80 c5live (fun _ => 0) c5omega c5forced = true := by decide

/-- **C5 (escape from Cantor), universal form**: for reals `X, Y` not both
rational, ternary digit 1 occurs i.o. in one of `Y, 2Y, X+4Y, 2X, 4X`. -/
theorem c5_disjunction_universal (X Y : ℝ)
    (hXY : ¬ (∃ p : ℚ, (p:ℝ) = X) ∨ ¬ (∃ q : ℚ, (q:ℝ) = Y)) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 Y [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (2 * Y) [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (X + 4 * Y) [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (2 * X) [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (4 * X) [1] n) := by
  have hirr : Irrational X ∨ Irrational Y := by
    rcases hXY with hX | hY
    · exact Or.inl fun ⟨p, hp⟩ => hX ⟨p, hp⟩
    · exact Or.inr fun ⟨q, hq⟩ => hY ⟨q, hq⟩
  obtain ⟨ch, hch, hocc⟩ := signed_engine_g 3 (by norm_num) c5Fam (by decide) c5_cert
    X Y hirr (by decide) (by decide) (by decide)
  fin_cases hch
  · refine Or.inl ?_
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 3 (((0:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [1] n := hocc
    rwa [show ((0:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = Y from by push_cast; ring] at h
  · refine Or.inr (Or.inl ?_)
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 3 (((0:ℤ):ℝ) * X + ((2:ℤ):ℝ) * Y) [1] n := hocc
    rwa [show ((0:ℤ):ℝ) * X + ((2:ℤ):ℝ) * Y = 2 * Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inl ?_))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 3 (((1:ℤ):ℝ) * X + ((4:ℤ):ℝ) * Y) [1] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((4:ℤ):ℝ) * Y = X + 4 * Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 3 (((2:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y) [1] n := hocc
    rwa [show ((2:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y = 2 * X from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 3 (((4:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y) [1] n := hocc
    rwa [show ((4:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y = 4 * X from by push_cast; ring] at h

/-- **C5** (ln-instance): ternary digit 1 occurs i.o. in one of
ln 3, ln 9, ln 162, ln 4, ln 16. -/
theorem c5_disjunction :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (Real.log 3) [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (Real.log 9) [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (Real.log 162) [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (Real.log 4) [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (Real.log 16) [1] n) := by
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9:ℝ) = 3 ^ 2 from by norm_num, Real.log_pow]
    push_cast; ring
  have h162 : Real.log 162 = Real.log 2 + 4 * Real.log 3 := by
    rw [show (162:ℝ) = 2 * 3 ^ 4 from by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
    push_cast; ring
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2 ^ 4 from by norm_num, Real.log_pow]
    push_cast; ring
  rw [h9, h162, h4, h16]
  exact c5_disjunction_universal (Real.log 2) (Real.log 3)
    (Or.inl fun ⟨p, hp⟩ => irrational_log_two ⟨p, hp⟩)

end NormalNumbers.Adder
