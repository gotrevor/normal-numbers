/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG

/-!
# Tower claim C6: the base-4 positioned-binary family (kernel tier)

Brief: `BRIEF-adder-tower.md` phase C item 6; dossier
`EVIDENCE-2026-08-29-tower-formalization.md` §C6.

For `X, Y` not both rational, at least one base-4 digit claim holds i.o.:
3 in `X` · 1 in `X+3Y` · 3 in `X+4Y` · 2 in `2X−Y` · 0 in `2X` ·
0 in `2X+2Y`.  (Base-4 digit `d` at position `n` is the binary word
`[d≥2][d mod 2]` at even-aligned position `2n−1`, so this family is a
POSITIONED-binary statement — the base-4 reading is the theorem, the
binary reading is the interpretation.)

First exercise of the signed (negative-coefficient) base-g carry window:
channel `(2,−1)` has `off = 1`.  Certificate emitted and re-verified by
`adder_baseg_emit.py c6` (480 ambient, 19 live, fixed points, collapse
verdict agreeing with the dossier's `base_g_digit_hunt.py 4`), checked
here by kernel `decide` against our own `gfamPred` over the packed
alphabet `σ = x + 4y < 16`.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-- The C6 family: channels
`(1,0)/3 · (1,3)/1 · (1,4)/3 · (2,−1)/2 · (2,0)/0 · (2,2)/0` (base 4). -/
def c6Fam : List ZChannel :=
  [⟨1, 0, [3]⟩, ⟨1, 3, [1]⟩, ⟨1, 4, [3]⟩, ⟨2, -1, [2]⟩, ⟨2, 0, [0]⟩,
   ⟨2, 2, [0]⟩]

def c6live : ℕ → Bool := fun s =>
  [5, 20, 24, 25, 129, 130, 134, 149, 150, 209, 220, 224, 225, 229, 259,
   274, 330, 339, 459].contains s

def c6rho : ℕ → ℕ := fun s =>
  (([(5, 1), (20, 3), (24, 2), (25, 3), (129, 3), (130, 2), (134, 1),
     (149, 5), (150, 4), (224, 1), (225, 2), (259, 4), (274, 3), (330, 1),
     (339, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def c6omega : ℕ → ℕ := fun s =>
  (([(0, 1), (4, 2), (8, 1), (9, 1), (21, 1), (28, 1), (29, 1), (124, 1),
     (125, 1), (128, 1), (133, 1), (135, 1), (138, 1), (139, 1), (140, 1),
     (141, 1), (144, 1), (145, 2), (148, 1), (153, 1), (154, 2), (200, 1),
     (201, 1), (204, 1), (205, 2), (206, 1), (210, 1), (221, 1), (226, 1),
     (230, 1), (249, 1), (250, 1), (253, 1), (254, 3), (255, 2), (258, 2),
     (269, 1), (270, 1), (273, 1), (275, 2), (278, 1), (279, 1), (325, 1),
     (326, 1), (329, 2), (334, 2), (335, 2), (338, 1), (345, 1), (346, 1),
     (349, 1), (350, 1), (454, 1), (455, 1), (458, 1)] :
    List (ℕ × ℕ)).lookup s).getD 0

def c6forced : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(209, (6, 209)), (220, (2, 220)), (229, (6, 229)), (459, (14, 459))] :
    List (ℕ × ℕ × ℕ)).lookup s

set_option maxHeartbeats 8000000 in
/-- The C6 certificate, kernel tier. -/
theorem c6_cert : checkCertA (fun σ s' => gfamPred 4 c6Fam (σ % 4) (σ / 4) s')
    (4 ^ 2) 480 c6live c6rho c6omega c6forced = true := by decide +kernel

/-- **C6 (base-4 positioned-binary family), universal form**: for reals
`X, Y` not both rational, base-4 digit 3 occurs i.o. in `X`, or 1 in
`X+3Y`, or 3 in `X+4Y`, or 2 in `2X−Y`, or 0 in `2X`, or 0 in `2X+2Y`. -/
theorem c6_disjunction_universal (X Y : ℝ)
    (hXY : ¬ (∃ p : ℚ, (p:ℝ) = X) ∨ ¬ (∃ q : ℚ, (q:ℝ) = Y)) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 4 X [3] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 4 (X + 3 * Y) [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 4 (X + 4 * Y) [3] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 4 (2 * X - Y) [2] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 4 (2 * X) [0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 4 (2 * X + 2 * Y) [0] n) := by
  have hirr : Irrational X ∨ Irrational Y := by
    rcases hXY with hX | hY
    · exact Or.inl fun ⟨p, hp⟩ => hX ⟨p, hp⟩
    · exact Or.inr fun ⟨q, hq⟩ => hY ⟨q, hq⟩
  obtain ⟨ch, hch, hocc⟩ := signed_engine_g 4 (by norm_num) c6Fam (by decide) c6_cert
    X Y hirr (by decide) (by decide) (by decide)
  fin_cases hch
  · refine Or.inl ?_
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 4 (((1:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y) [3] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y = X from by push_cast; ring] at h
  · refine Or.inr (Or.inl ?_)
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 4 (((1:ℤ):ℝ) * X + ((3:ℤ):ℝ) * Y) [1] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((3:ℤ):ℝ) * Y = X + 3 * Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inl ?_))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 4 (((1:ℤ):ℝ) * X + ((4:ℤ):ℝ) * Y) [3] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((4:ℤ):ℝ) * Y = X + 4 * Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 4 (((2:ℤ):ℝ) * X + ((-1:ℤ):ℝ) * Y) [2] n := hocc
    rwa [show ((2:ℤ):ℝ) * X + ((-1:ℤ):ℝ) * Y = 2 * X - Y from by
      push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 4 (((2:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y) [0] n := hocc
    rwa [show ((2:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y = 2 * X from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 4 (((2:ℤ):ℝ) * X + ((2:ℤ):ℝ) * Y) [0] n := hocc
    rwa [show ((2:ℤ):ℝ) * X + ((2:ℤ):ℝ) * Y = 2 * X + 2 * Y from by
      push_cast; ring] at h

end NormalNumbers.Adder
