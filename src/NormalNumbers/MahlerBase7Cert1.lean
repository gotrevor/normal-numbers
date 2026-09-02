/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG

/-! Base-7 Mahler collapse certificate for digit `1` (see
`MahlerBase7Exact.lean` for the statement and the per-digit subset table).
Kept in its own module: the seven kernel `decide`s together exhaust memory in
one `lean` process, but each is under two minutes on its own. -/

namespace NormalNumbers.Adder

open NormalNumbers

/-- Digit `1`: channels [1, 3, 4, 5, 6, 9], ambient `3240`, 27 live. -/
def m7Chans1 (w : ℕ) : List ZChannel := [⟨1, 0, [w]⟩, ⟨3, 0, [w]⟩, ⟨4, 0, [w]⟩, ⟨5, 0, [w]⟩, ⟨6, 0, [w]⟩, ⟨9, 0, [w]⟩]

def m7live1 : ℕ → Bool := fun s => [0, 360, 795, 796, 855, 856, 1155, 1156, 1215, 1216, 1588, 1591, 1648, 1651, 2011, 2023, 2024, 2083, 2084, 2383, 2384, 2443, 2444, 2447, 2807, 2819, 3239].contains s

def m7rho1 : ℕ → ℕ := fun s =>
  (([(0, 4), (360, 5), (1216, 1), (1588, 2), (1651, 7), (2011, 6), (2023, 2), (2444, 3), (2447, 2), (2807, 3), (2819, 4), (3239, 8)] : List (ℕ × ℕ)).lookup s).getD 0

def m7omega1 : ℕ → ℕ := fun s =>
  (([(807, 1), (808, 1), (867, 1), (868, 1), (1167, 1), (1168, 1), (1227, 1), (1228, 1), (1231, 1), (1288, 1), (1291, 1), (1948, 1), (1951, 1), (2008, 1), (2012, 1), (2071, 1), (2072, 1), (2371, 1), (2372, 1), (2431, 1), (2432, 1), (2456, 1), (2459, 1), (2504, 1), (2507, 1), (2516, 1), (2519, 1), (2804, 1), (2816, 1), (2864, 1), (2867, 1), (2876, 1), (2879, 2)] : List (ℕ × ℕ)).lookup s).getD 0

def m7forced1 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (795, (2, 795)), (796, (2, 796)), (855, (2, 855)), (856, (2, 856)), (1155, (2, 1155)), (1156, (2, 1156)), (1215, (2, 1215)), (1216, (2, 1216)), (1588, (3, 1588)), (1591, (3, 1591)), (1648, (3, 1648)), (1651, (3, 1651)), (2023, (4, 2023)), (2024, (4, 2024)), (2083, (4, 2083)), (2084, (4, 2084)), (2383, (4, 2383)), (2384, (4, 2384)), (2443, (4, 2443)), (2444, (4, 2444)), (3239, (6, 3239))] : List (ℕ × ℕ × ℕ)).lookup s

theorem m7_cert1 : checkCertA (fun σ s' => gfamPred 7 (m7Chans1 1) (σ % 7) (σ / 7) s')
    7 3240 m7live1 m7rho1 m7omega1 m7forced1 = true := by
  decide +kernel


end NormalNumbers.Adder
