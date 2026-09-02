/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG

/-! Base-7 Mahler collapse certificate for digit `5` (see
`MahlerBase7Exact.lean` for the statement and the per-digit subset table).
Kept in its own module: the seven kernel `decide`s together exhaust memory in
one `lean` process, but each is under two minutes on its own. -/

namespace NormalNumbers.Adder

open NormalNumbers

/-- Digit `5`: channels [1, 3, 4, 5, 6, 9], ambient `3240`, 27 live. -/
def m7Chans5 (w : ℕ) : List ZChannel := [⟨1, 0, [w]⟩, ⟨3, 0, [w]⟩, ⟨4, 0, [w]⟩, ⟨5, 0, [w]⟩, ⟨6, 0, [w]⟩, ⟨9, 0, [w]⟩]

def m7live5 : ℕ → Bool := fun s => [0, 420, 432, 792, 795, 796, 855, 856, 1155, 1156, 1215, 1216, 1228, 1588, 1591, 1648, 1651, 2023, 2024, 2083, 2084, 2383, 2384, 2443, 2444, 2879, 3239].contains s

def m7rho5 : ℕ → ℕ := fun s =>
  (([(0, 8), (420, 4), (432, 3), (792, 2), (795, 3), (1216, 2), (1228, 6), (1588, 7), (1651, 2), (2023, 1), (2879, 5), (3239, 4)] : List (ℕ × ℕ)).lookup s).getD 0

def m7omega5 : ℕ → ℕ := fun s =>
  (([(360, 2), (363, 1), (372, 1), (375, 1), (423, 1), (435, 1), (720, 1), (723, 1), (732, 1), (735, 1), (780, 1), (783, 1), (807, 1), (808, 1), (867, 1), (868, 1), (1167, 1), (1168, 1), (1227, 1), (1231, 1), (1288, 1), (1291, 1), (1948, 1), (1951, 1), (2008, 1), (2011, 1), (2012, 1), (2071, 1), (2072, 1), (2371, 1), (2372, 1), (2431, 1), (2432, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m7forced5 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (795, (2, 795)), (796, (2, 796)), (855, (2, 855)), (856, (2, 856)), (1155, (2, 1155)), (1156, (2, 1156)), (1215, (2, 1215)), (1216, (2, 1216)), (1588, (3, 1588)), (1591, (3, 1591)), (1648, (3, 1648)), (1651, (3, 1651)), (2023, (4, 2023)), (2024, (4, 2024)), (2083, (4, 2083)), (2084, (4, 2084)), (2383, (4, 2383)), (2384, (4, 2384)), (2443, (4, 2443)), (2444, (4, 2444)), (3239, (6, 3239))] : List (ℕ × ℕ × ℕ)).lookup s

theorem m7_cert5 : checkCertA (fun σ s' => gfamPred 7 (m7Chans5 5) (σ % 7) (σ / 7) s')
    7 3240 m7live5 m7rho5 m7omega5 m7forced5 = true := by
  decide +kernel


end NormalNumbers.Adder
