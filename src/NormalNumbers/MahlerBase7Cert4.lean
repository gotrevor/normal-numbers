/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG

/-! Base-7 Mahler collapse certificate for digit `4` (see
`MahlerBase7Exact.lean` for the statement and the per-digit subset table).
Kept in its own module: the seven kernel `decide`s together exhaust memory in
one `lean` process, but each is under two minutes on its own. -/

namespace NormalNumbers.Adder

open NormalNumbers

/-- Digit `4`: channels [1, 2, 3, 4, 5, 6], ambient `720`, 16 live. -/
def m7Chans4 (w : ℕ) : List ZChannel := [⟨1, 0, [w]⟩, ⟨2, 0, [w]⟩, ⟨3, 0, [w]⟩, ⟨4, 0, [w]⟩, ⟨5, 0, [w]⟩, ⟨6, 0, [w]⟩]

def m7live4 : ℕ → Bool := fun s => [0, 120, 144, 150, 272, 296, 297, 302, 303, 416, 417, 422, 423, 569, 575, 719].contains s

def m7rho4 : ℕ → ℕ := fun s =>
  (([(0, 4), (120, 2), (150, 1), (272, 1), (296, 3), (575, 1), (719, 2)] : List (ℕ × ℕ)).lookup s).getD 0

def m7omega4 : ℕ → ℕ := fun s =>
  (([(6, 1), (24, 1), (30, 1), (126, 1), (152, 1), (174, 1), (176, 1), (270, 1), (294, 1), (593, 1), (599, 1), (689, 1), (695, 1), (713, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m7forced4 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (144, (1, 569)), (150, (1, 575)), (296, (3, 296)), (297, (3, 297)), (302, (3, 302)), (303, (3, 303)), (416, (3, 416)), (417, (3, 417)), (422, (3, 422)), (423, (3, 423)), (569, (5, 144)), (575, (5, 150)), (719, (6, 719))] : List (ℕ × ℕ × ℕ)).lookup s

theorem m7_cert4 : checkCertA (fun σ s' => gfamPred 7 (m7Chans4 4) (σ % 7) (σ / 7) s')
    7 720 m7live4 m7rho4 m7omega4 m7forced4 = true := by
  decide +kernel


end NormalNumbers.Adder
