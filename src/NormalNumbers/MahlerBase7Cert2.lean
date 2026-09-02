/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG

/-! Base-7 Mahler collapse certificate for digit `2` (see
`MahlerBase7Exact.lean` for the statement and the per-digit subset table).
Kept in its own module: the seven kernel `decide`s together exhaust memory in
one `lean` process, but each is under two minutes on its own. -/

namespace NormalNumbers.Adder

open NormalNumbers

/-- Digit `2`: channels [1, 2, 3, 4, 5, 6], ambient `720`, 16 live. -/
def m7Chans2 (w : ℕ) : List ZChannel := [⟨1, 0, [w]⟩, ⟨2, 0, [w]⟩, ⟨3, 0, [w]⟩, ⟨4, 0, [w]⟩, ⟨5, 0, [w]⟩, ⟨6, 0, [w]⟩]

def m7live2 : ℕ → Bool := fun s => [0, 144, 150, 296, 297, 302, 303, 416, 417, 422, 423, 447, 569, 575, 599, 719].contains s

def m7rho2 : ℕ → ℕ := fun s =>
  (([(0, 2), (144, 1), (423, 3), (447, 1), (569, 1), (599, 2), (719, 4)] : List (ℕ × ℕ)).lookup s).getD 0

def m7omega2 : ℕ → ℕ := fun s =>
  (([(6, 1), (24, 1), (30, 1), (120, 1), (126, 1), (425, 1), (449, 1), (543, 1), (545, 1), (567, 1), (593, 1), (689, 1), (695, 1), (713, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m7forced2 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (144, (1, 569)), (150, (1, 575)), (296, (3, 296)), (297, (3, 297)), (302, (3, 302)), (303, (3, 303)), (416, (3, 416)), (417, (3, 417)), (422, (3, 422)), (423, (3, 423)), (569, (5, 144)), (575, (5, 150)), (719, (6, 719))] : List (ℕ × ℕ × ℕ)).lookup s

theorem m7_cert2 : checkCertA (fun σ s' => gfamPred 7 (m7Chans2 2) (σ % 7) (σ / 7) s')
    7 720 m7live2 m7rho2 m7omega2 m7forced2 = true := by
  decide +kernel


end NormalNumbers.Adder
