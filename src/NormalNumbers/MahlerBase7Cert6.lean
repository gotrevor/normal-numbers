/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG

/-! Base-7 Mahler collapse certificate for digit `6` (see
`MahlerBase7Exact.lean` for the statement and the per-digit subset table).
Kept in its own module: the seven kernel `decide`s together exhaust memory in
one `lean` process, but each is under two minutes on its own. -/

namespace NormalNumbers.Adder

open NormalNumbers

/-- Digit `6`: channels [1, 2, 3, 4, 5, 6, 8], ambient `5760`, 12 live. -/
def m7Chans6 (w : ℕ) : List ZChannel := [⟨1, 0, [w]⟩, ⟨2, 0, [w]⟩, ⟨3, 0, [w]⟩, ⟨4, 0, [w]⟩, ⟨5, 0, [w]⟩, ⟨6, 0, [w]⟩, ⟨8, 0, [w]⟩]

def m7live6 : ℕ → Bool := fun s => [0, 840, 864, 1590, 1712, 2456, 3303, 3327, 4169, 4895, 4919, 5039].contains s

def m7rho6 : ℕ → ℕ := fun s =>
  (([(0, 6), (864, 1), (1590, 3), (1712, 2), (2456, 1), (3303, 5), (3327, 1), (4169, 4), (4895, 3), (4919, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m7omega6 : ℕ → ℕ := fun s =>
  (([(720, 1), (846, 1), (870, 1), (1560, 1), (1566, 1), (1584, 1), (1592, 1), (1616, 1), (1736, 1), (2312, 1), (2336, 1), (2432, 1), (2457, 1), (2463, 1), (2577, 1), (2583, 1), (3177, 1), (3183, 1), (3297, 1), (3329, 1), (3447, 1), (3449, 1), (4047, 1), (4049, 1), (4167, 1), (4175, 1), (4199, 1), (4295, 1), (4319, 1), (5015, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m7forced6 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (840, (1, 840)), (864, (1, 2456)), (1590, (1, 4895)), (1712, (2, 1712)), (2456, (2, 4919)), (3303, (3, 3303)), (3327, (4, 864)), (4169, (4, 4169)), (4895, (5, 1590)), (4919, (5, 3327)), (5039, (5, 5039))] : List (ℕ × ℕ × ℕ)).lookup s

theorem m7_cert6 : checkCertA (fun σ s' => gfamPred 7 (m7Chans6 6) (σ % 7) (σ / 7) s')
    7 5760 m7live6 m7rho6 m7omega6 m7forced6 = true := by
  decide +kernel


end NormalNumbers.Adder
