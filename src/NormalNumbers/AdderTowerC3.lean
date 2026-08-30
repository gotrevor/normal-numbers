/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG

/-!
# Tower claim C3: the {1, 5} ternary digit variants (lane 2, B–B orbit)

Brief: `BRIEF-adder-tower.md` phase C item 3; dossier
`EVIDENCE-2026-08-29-tower-formalization.md` §C3.

For every irrational `x` and every ternary digit `d`: `d` occurs infinitely
often in the base-3 expansion of `x` or of `5x`.  Per the brief this is at
most a variant delta over Berend–Boshernitzan 1994 (same lane-2 treatment
as C1: cite the framework, never headline as new).

Family per digit `d`: channels `x` (stateless) and `5x` (carry `T ∈ [0,4]`)
— five family states, alphabet 3.  Certificates emitted and re-verified by
`experiments/adder_baseg_emit.py c3` (the other instrument), then checked
here independently by kernel `decide` against our own `gfamPred`.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-- The C3 family for digit `d`: channels `x` and `5x`, both avoiding the
single ternary digit `d`. -/
def c3Chans (d : ℕ) : List ZChannel := [⟨1, 0, [d]⟩, ⟨5, 0, [d]⟩]

/-- d = 0: two live carries {2, 4}, forced self-loops. -/
def c3live0 : ℕ → Bool := fun s => [2, 4].contains s
def c3omega0 : ℕ → ℕ := fun s => (([(1, 1), (3, 2)] : List (ℕ × ℕ)).lookup s).getD 0
def c3forced0 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(2, (1, 2)), (4, (2, 4))] : List (ℕ × ℕ × ℕ)).lookup s

/-- d = 1: four live carries {0, 1, 3, 4}, a forced 2-cycle and two
self-loops. -/
def c3live1 : ℕ → Bool := fun s => [0, 1, 3, 4].contains s
def c3forced1 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (1, (0, 3)), (3, (2, 1)), (4, (2, 4))] : List (ℕ × ℕ × ℕ)).lookup s

/-- d = 2: two live carries {0, 2}, forced self-loops. -/
def c3live2 : ℕ → Bool := fun s => [0, 2].contains s
def c3omega2 : ℕ → ℕ := fun s => (([(1, 2), (3, 1)] : List (ℕ × ℕ)).lookup s).getD 0
def c3forced2 : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (2, (1, 2))] : List (ℕ × ℕ × ℕ)).lookup s

theorem c3_cert0 : checkCertA (fun σ s' => gfamPred 3 (c3Chans 0) (σ % 3) (σ / 3) s')
    3 5 c3live0 (fun _ => 0) c3omega0 c3forced0 = true := by decide

theorem c3_cert1 : checkCertA (fun σ s' => gfamPred 3 (c3Chans 1) (σ % 3) (σ / 3) s')
    3 5 c3live1 (fun _ => 0) (fun _ => 0) c3forced1 = true := by decide

theorem c3_cert2 : checkCertA (fun σ s' => gfamPred 3 (c3Chans 2) (σ % 3) (σ / 3) s')
    3 5 c3live2 (fun _ => 0) c3omega2 c3forced2 = true := by decide

/-- **C3 ({1, 5} ternary variants — lane 2, Berend–Boshernitzan orbit)**:
for every irrational `x` and every ternary digit `d`, `d` occurs infinitely
often in the base-3 expansion of `x` or of `5x`. -/
theorem c3_ternary_digit_five (X : ℝ) (hX : Irrational X) (d : ℕ) (hd : d < 3) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 X [d] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (5 * X) [d] n) := by
  have key : ∃ ch ∈ c3Chans d, ∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (ch.a * X) ch.word n := by
    interval_cases d
    · exact signed_engine_g_single 3 (by norm_num) (c3Chans 0) rfl c3_cert0 X hX
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 3 (by norm_num) (c3Chans 1) rfl c3_cert1 X hX
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 3 (by norm_num) (c3Chans 2) rfl c3_cert2 X hX
        (by decide) (by decide) (by decide)
  obtain ⟨ch, hch, hio⟩ := key
  fin_cases hch
  · left
    intro N
    obtain ⟨n, hn, hocc⟩ := hio N
    refine ⟨n, hn, ?_⟩
    rw [show (((1:ℤ):ℝ)) * X = X from by push_cast; ring] at hocc
    exact hocc
  · right
    intro N
    obtain ⟨n, hn, hocc⟩ := hio N
    refine ⟨n, hn, ?_⟩
    rw [show (((5:ℤ):ℝ)) * X = 5 * X from by push_cast; ring] at hocc
    exact hocc

end NormalNumbers.Adder
