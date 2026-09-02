/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG
import NormalNumbers.MahlerPrimeLowerBound

/-!
# `M(5,1) = 6`: the Mahler constant, pinned exactly at a prime base 🧮

`MahlerPrimeLowerBound.lean` proves `M(5,1) ≥ 6` (background+burst witness
`2/4 + Σ 5^(−i!)`, digit `1`).  This file proves the matching **upper** half,

    for every irrational `X` and every base-5 digit `w`, some `m ≤ 6`
    has `w` occurring infinitely often in the base-5 expansion of `m·X`,

so `M(5,1) = 6` **exactly** — the first Mahler constant pinned to a point at a
prime base beyond Berend–Boshernitzan 1994's `M(3,1) = 2` (`AdderTowerC1.lean`).
For comparison the general bounds give only `4 ≤ M(5,1) ≤ 25`.

The five certificates are kernel `decide`s of the single-track base-5 signed
engine (`signed_engine_g_single`) on the six-channel family
`x, 2x, 3x, 4x, 5x, 6x`, each avoiding the one-digit word `[w]`.  Ambient state
space `1·2·3·4·5·6 = 720` (channel `a` carries `T ∈ {0,…,a−1}`); after pruning
only `6`–`11` states survive, and each surviving component is a simple cycle —
the collapse verdict.  Emitted and independently re-verified by
`experiments/mahler_collapse_cert.py 5 6`.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-- The base-5 Mahler family for digit `w`: channels `x, 2x, …, 6x`, each
avoiding the single digit `w`. -/
def m5Chans (w : ℕ) : List ZChannel :=
  [⟨1, 0, [w]⟩, ⟨2, 0, [w]⟩, ⟨3, 0, [w]⟩, ⟨4, 0, [w]⟩, ⟨5, 0, [w]⟩, ⟨6, 0, [w]⟩]

def m5live0 : ℕ → Bool := fun s => [144, 150, 296, 447, 569, 719].contains s

def m5rho0 : ℕ → ℕ := fun s =>
  (([(150, 1), (296, 2), (447, 1), (719, 3)] : List (ℕ × ℕ)).lookup s).getD 0

def m5omega0 : ℕ → ℕ := fun s =>
  (([(264, 1), (270, 1), (302, 1), (416, 1), (422, 1), (449, 1), (567, 1), (599, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m5forced0 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(144, (1, 144)), (150, (1, 447)), (296, (2, 296)), (447, (3, 150)), (569, (3, 569)), (719, (4, 719))] : List (ℕ × ℕ × ℕ)).lookup s


def m5live1 : ℕ → Bool := fun s => [0, 296, 297, 302, 303, 416, 417, 422, 423, 569, 719].contains s

def m5rho1 : ℕ → ℕ := fun s =>
  (([(569, 1), (719, 2)] : List (ℕ × ℕ)).lookup s).getD 0

def m5omega1 : ℕ → ℕ := fun s =>
  (([(120, 1), (447, 1), (449, 1), (453, 1), (455, 1), (567, 1), (573, 1), (575, 2), (599, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m5forced1 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (296, (2, 296)), (297, (2, 297)), (302, (2, 302)), (303, (2, 303)), (416, (2, 416)), (417, (2, 417)), (422, (2, 422)), (423, (2, 423)), (719, (4, 719))] : List (ℕ × ℕ × ℕ)).lookup s


def m5live2 : ℕ → Bool := fun s => [0, 150, 152, 270, 272, 447, 449, 567, 569, 719].contains s

def m5rho2 : ℕ → ℕ := fun s =>
  (([(0, 1), (719, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m5omega2 : ℕ → ℕ := fun s =>
  (([(120, 1), (144, 1), (146, 1), (264, 1), (266, 1), (453, 1), (455, 1), (573, 1), (575, 1), (599, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m5forced2 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (150, (1, 447)), (152, (1, 449)), (270, (1, 567)), (272, (1, 569)), (447, (3, 150)), (449, (3, 152)), (567, (3, 270)), (569, (3, 272)), (719, (4, 719))] : List (ℕ × ℕ × ℕ)).lookup s


def m5live3 : ℕ → Bool := fun s => [0, 150, 296, 297, 302, 303, 416, 417, 422, 423, 719].contains s

def m5rho3 : ℕ → ℕ := fun s =>
  (([(0, 2), (150, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m5omega3 : ℕ → ℕ := fun s =>
  (([(120, 1), (144, 2), (146, 1), (152, 1), (264, 1), (266, 1), (270, 1), (272, 1), (599, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m5forced3 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (296, (2, 296)), (297, (2, 297)), (302, (2, 302)), (303, (2, 303)), (416, (2, 416)), (417, (2, 417)), (422, (2, 422)), (423, (2, 423)), (719, (4, 719))] : List (ℕ × ℕ × ℕ)).lookup s


def m5live4 : ℕ → Bool := fun s => [0, 150, 272, 423, 569, 575].contains s

def m5rho4 : ℕ → ℕ := fun s =>
  (([(0, 3), (272, 1), (423, 2), (569, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m5omega4 : ℕ → ℕ := fun s =>
  (([(120, 1), (152, 1), (270, 1), (297, 1), (303, 1), (417, 1), (449, 1), (455, 1)] : List (ℕ × ℕ)).lookup s).getD 0

def m5forced4 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (150, (1, 150)), (272, (1, 569)), (423, (2, 423)), (569, (3, 272)), (575, (3, 575))] : List (ℕ × ℕ × ℕ)).lookup s


theorem m5_cert0 : checkCertA (fun σ s' => gfamPred 5 (m5Chans 0) (σ % 5) (σ / 5) s')
    5 720 m5live0 m5rho0 m5omega0 m5forced0 = true := by decide +kernel

theorem m5_cert1 : checkCertA (fun σ s' => gfamPred 5 (m5Chans 1) (σ % 5) (σ / 5) s')
    5 720 m5live1 m5rho1 m5omega1 m5forced1 = true := by decide +kernel

theorem m5_cert2 : checkCertA (fun σ s' => gfamPred 5 (m5Chans 2) (σ % 5) (σ / 5) s')
    5 720 m5live2 m5rho2 m5omega2 m5forced2 = true := by decide +kernel

theorem m5_cert3 : checkCertA (fun σ s' => gfamPred 5 (m5Chans 3) (σ % 5) (σ / 5) s')
    5 720 m5live3 m5rho3 m5omega3 m5forced3 = true := by decide +kernel

theorem m5_cert4 : checkCertA (fun σ s' => gfamPred 5 (m5Chans 4) (σ % 5) (σ / 5) s')
    5 720 m5live4 m5rho4 m5omega4 m5forced4 = true := by decide +kernel

/-- **`M(5,1) ≤ 6`.**  For every irrational `X` and every base-5 digit `w`
there is a multiplier `1 ≤ m ≤ 6` such that `w` occurs infinitely often in the
base-5 expansion of `m·X`. -/
theorem m5_mahler_upper (X : ℝ) (hX : Irrational X) (w : ℕ) (hw : w < 5) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 6 ∧ ∀ N, ∃ n, N ≤ n ∧ OccursAt 5 ((m : ℝ) * X) [w] n := by
  have key : ∃ ch ∈ m5Chans w, ∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (ch.a * X) ch.word n := by
    interval_cases w
    · exact signed_engine_g_single 5 (by norm_num) (m5Chans 0) rfl m5_cert0 X hX
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 5 (by norm_num) (m5Chans 1) rfl m5_cert1 X hX
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 5 (by norm_num) (m5Chans 2) rfl m5_cert2 X hX
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 5 (by norm_num) (m5Chans 3) rfl m5_cert3 X hX
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 5 (by norm_num) (m5Chans 4) rfl m5_cert4 X hX
        (by decide) (by decide) (by decide)
  obtain ⟨ch, hch, hio⟩ := key
  fin_cases hch
  · exact ⟨1, by norm_num, by norm_num, by simpa using hio⟩
  · exact ⟨2, by norm_num, by norm_num, by simpa using hio⟩
  · exact ⟨3, by norm_num, by norm_num, by simpa using hio⟩
  · exact ⟨4, by norm_num, by norm_num, by simpa using hio⟩
  · exact ⟨5, by norm_num, by norm_num, by simpa using hio⟩
  · exact ⟨6, by norm_num, by norm_num, by simpa using hio⟩

/-- **`M(5,1) = 6`, both halves.**  `6` multipliers always suffice (part 1), and
`5` do not (part 2, the background+burst witness `2/4 + Σ 5^(−i!)` with digit
`1`).  So the optimal universal Mahler multiplier for base 5, block length 1, is
exactly `6`. -/
theorem mahler_M_five_eq_six :
    (∀ X : ℝ, Irrational X → ∀ w < 5, ∃ m : ℕ, 1 ≤ m ∧ m ≤ 6 ∧
        ∀ N, ∃ n, N ≤ n ∧ OccursAt 5 ((m : ℝ) * X) [w] n) ∧
    (∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 5 →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt 5 ((m : ℝ) * α) [1] n) :=
  ⟨fun X hX w hw => m5_mahler_upper X hX w hw, Mahler.mahler_lower_bound_base5⟩

end NormalNumbers.Adder
