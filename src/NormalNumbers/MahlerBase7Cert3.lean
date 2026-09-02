/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG

/-! Base-7 Mahler collapse certificate for digit `3` (see
`MahlerBase7Exact.lean` for the statement and the per-digit subset table).
Kept in its own module: the seven kernel `decide`s together exhaust memory in
one `lean` process, but each is under two minutes on its own. -/

namespace NormalNumbers.Adder

open NormalNumbers

/-- Digit `3`: channels [1, 2, 3, 4, 5, 6, 8], ambient `5760`, 18 live. -/
def m7Chans3 (w : ℕ) : List ZChannel := [⟨1, 0, [w]⟩, ⟨2, 0, [w]⟩, ⟨3, 0, [w]⟩, ⟨4, 0, [w]⟩, ⟨5, 0, [w]⟩, ⟨6, 0, [w]⟩, ⟨8, 0, [w]⟩]

def m7live3 : ℕ → Bool := fun s => [0, 840, 864, 1590, 1592, 1710, 1712, 2432, 2456, 3303, 3327, 4047, 4049, 4167, 4169, 4895, 4919, 5759].contains s

def m7rho3 : ℕ → ℕ := fun s =>
  (([(0, 2), (1712, 1), (4047, 1), (5759, 2)] : List (ℕ × ℕ)).lookup s).getD 0

def m7omega3 : ℕ → ℕ := fun s =>
  (([(720, 1), (726, 1), (744, 1), (750, 1), (846, 1), (870, 1), (1440, 1), (1446, 1), (1464, 1), (1470, 1), (1560, 1), (1566, 1), (1584, 1), (1614, 1), (1616, 1), (1734, 1), (1736, 1), (2310, 1), (2312, 1), (2334, 1), (2336, 1), (2430, 1), (2454, 1), (3305, 1), (3329, 1), (3423, 1), (3425, 1), (3447, 1), (3449, 1), (4023, 1), (4025, 1), (4143, 1), (4145, 1), (4175, 1), (4193, 1), (4199, 1), (4289, 1), (4295, 1), (4313, 1), (4319, 1), (4889, 1), (4913, 1), (5009, 1), (5015, 1), (5033, 1), (5039, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m7forced3 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (840, (1, 2432)), (864, (1, 2456)), (1590, (2, 1590)), (1592, (2, 1592)), (1710, (2, 1710)), (1712, (2, 1712)), (2432, (2, 4895)), (2456, (2, 4919)), (3303, (4, 840)), (3327, (4, 864)), (4047, (4, 4047)), (4049, (4, 4049)), (4167, (4, 4167)), (4169, (4, 4169)), (4895, (5, 3303)), (4919, (5, 3327)), (5759, (6, 5759))] : List (ℕ × ℕ × ℕ)).lookup s

theorem m7_cert3 : checkCertA (fun σ s' => gfamPred 7 (m7Chans3 3) (σ % 7) (σ / 7) s')
    7 5760 m7live3 m7rho3 m7omega3 m7forced3 = true := by
  decide +kernel


end NormalNumbers.Adder
