/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG

/-! Base-7 Mahler collapse certificate for digit `0` (see
`MahlerBase7Exact.lean` for the statement and the per-digit subset table).
Kept in its own module: the seven kernel `decide`s together exhaust memory in
one `lean` process, but each is under two minutes on its own. -/

namespace NormalNumbers.Adder

open NormalNumbers

/-- Digit `0`: channels [1, 2, 3, 4, 5, 6, 8], ambient `5760`, 12 live. -/
def m7Chans0 (w : ℕ) : List ZChannel := [⟨1, 0, [w]⟩, ⟨2, 0, [w]⟩, ⟨3, 0, [w]⟩, ⟨4, 0, [w]⟩, ⟨5, 0, [w]⟩, ⟨6, 0, [w]⟩, ⟨8, 0, [w]⟩]

def m7live0 : ℕ → Bool := fun s => [720, 840, 864, 1590, 2432, 2456, 3303, 4047, 4169, 4895, 4919, 5759].contains s

def m7rho0 : ℕ → ℕ := fun s =>
  (([(840, 1), (864, 3), (1590, 4), (2432, 1), (2456, 5), (3303, 1), (4047, 2), (4169, 3), (4895, 1), (5759, 6)] : List (ℕ × ℕ)).lookup s).getD 0

def m7omega0 : ℕ → ℕ := fun s =>
  (([(744, 1), (1440, 1), (1464, 1), (1560, 1), (1584, 1), (1592, 1), (1710, 1), (1712, 1), (2310, 1), (2312, 1), (2430, 1), (2462, 1), (2576, 1), (2582, 1), (3176, 1), (3182, 1), (3296, 1), (3302, 1), (3327, 1), (3423, 1), (3447, 1), (4023, 1), (4143, 1), (4167, 1), (4175, 1), (4193, 1), (4199, 1), (4889, 1), (4913, 1), (5039, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m7forced0 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(720, (1, 720)), (840, (1, 2432)), (864, (1, 4169)), (1590, (2, 1590)), (2432, (2, 4895)), (2456, (3, 2456)), (3303, (4, 840)), (4047, (4, 4047)), (4169, (5, 864)), (4895, (5, 3303)), (4919, (5, 4919)), (5759, (6, 5759))] : List (ℕ × ℕ × ℕ)).lookup s

theorem m7_cert0 : checkCertA (fun σ s' => gfamPred 7 (m7Chans0 0) (σ % 7) (σ / 7) s')
    7 5760 m7live0 m7rho0 m7omega0 m7forced0 = true := by
  decide +kernel


end NormalNumbers.Adder
