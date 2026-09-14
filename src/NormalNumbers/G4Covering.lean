/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Disjunctive

/-!
# G4 disjunctivity, §4B: cylinder covering of an orbit closure that omits a word

If the base-four orbit of `x` never enters the cylinder `[w/B, (w+1)/B)`, `B = 4^ℓ`, then for
every `M` the orbit closure (in the circle) is covered by the `(B−1)^M` closed cylinders of
length `B^{−M}` whose `M` blocks (base-`B` digits) all differ from `w`
(`orbitClosure_subset_cylinders`).  This is the covering exponent `d = log_B(B−1) < 1` of
draft (4.4), in finite covering-number form (no box-dimension library).

Ingredients: the orbit shift `orbit b x (n+k) = fract (orbit b x n · b^k)`, the block digits
`block ℓ x n j = ⌊orbit 4 x (n + ℓ j) · B⌋`, the finite base-`B` expansion
`orbit 4 x n = ∑_{j<M} block_j / B^{j+1} + orbit 4 x (n + ℓM) / B^M`, and the omission
`block_j ≠ w`.
-/

open Set Finset
open scoped BigOperators

namespace NormalNumbers

/-- Orbit shift: `orbit b x (n + k) = fract (orbit b x n · b^k)`. -/
theorem orbit_add (b : ℕ) (x : ℝ) (n k : ℕ) :
    orbit b x (n + k) = Int.fract (orbit b x n * (b : ℝ) ^ k) := by
  unfold orbit
  rw [pow_add, ← mul_assoc]
  have : Int.fract (x * (b : ℝ) ^ n) * (b : ℝ) ^ k
      = x * (b : ℝ) ^ n * (b : ℝ) ^ k - ((⌊x * (b : ℝ) ^ n⌋ * (b ^ k : ℤ) : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [this, Int.fract_sub_intCast]

namespace G4

/-- The `j`-th base-`4^ℓ` block of the orbit point `orbit 4 x n`. -/
noncomputable def block (ℓ : ℕ) (x : ℝ) (n j : ℕ) : ℕ :=
  (⌊orbit 4 x (n + ℓ * j) * (4 : ℝ) ^ ℓ⌋).toNat

lemma floor_orbit_mul_nonneg (ℓ : ℕ) (x : ℝ) (m : ℕ) :
    0 ≤ ⌊orbit 4 x m * (4 : ℝ) ^ ℓ⌋ :=
  Int.floor_nonneg.mpr (mul_nonneg (orbit_mem_Ico 4 x m).1 (by positivity))

lemma block_cast (ℓ : ℕ) (x : ℝ) (n j : ℕ) :
    (block ℓ x n j : ℝ) = (⌊orbit 4 x (n + ℓ * j) * (4 : ℝ) ^ ℓ⌋ : ℝ) := by
  unfold block
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (floor_orbit_mul_nonneg ℓ x _)]

lemma block_lt (ℓ : ℕ) (x : ℝ) (n j : ℕ) : block ℓ x n j < 4 ^ ℓ := by
  have h1 : (block ℓ x n j : ℝ) ≤ orbit 4 x (n + ℓ * j) * (4 : ℝ) ^ ℓ := by
    rw [block_cast]; exact Int.floor_le _
  have h2 : orbit 4 x (n + ℓ * j) * (4 : ℝ) ^ ℓ < (4 : ℝ) ^ ℓ := by
    have := (orbit_mem_Ico 4 x (n + ℓ * j)).2
    have hp : (0 : ℝ) < (4 : ℝ) ^ ℓ := by positivity
    nlinarith
  exact_mod_cast h1.trans_lt h2

/-- One digit step: `y = ⌊yB⌋/B + fract(yB)/B`. -/
lemma orbit_eq_block_add (ℓ : ℕ) (x : ℝ) (n j : ℕ) :
    orbit 4 x (n + ℓ * j)
      = (block ℓ x n j : ℝ) / (4 : ℝ) ^ ℓ + orbit 4 x (n + ℓ * (j + 1)) / (4 : ℝ) ^ ℓ := by
  rw [show n + ℓ * (j + 1) = (n + ℓ * j) + ℓ by ring, orbit_add 4 x (n + ℓ * j) ℓ, block_cast]
  have hp : (0 : ℝ) < (4 : ℝ) ^ ℓ := by positivity
  push_cast
  rw [← add_div, Int.floor_add_fract, mul_div_cancel_right₀ _ hp.ne']

/-- The finite base-`B` expansion of an orbit point, `B = 4^ℓ`. -/
theorem orbit_expansion (ℓ : ℕ) (x : ℝ) (n M : ℕ) :
    orbit 4 x n = ∑ j ∈ range M, (block ℓ x n j : ℝ) / ((4 : ℝ) ^ ℓ) ^ (j + 1)
      + orbit 4 x (n + ℓ * M) / ((4 : ℝ) ^ ℓ) ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [ih, Finset.sum_range_succ, orbit_eq_block_add ℓ x n M]
    have hp : (0 : ℝ) < (4 : ℝ) ^ ℓ := by positivity
    field_simp
    ring

/-- Omission of the cylinder `[w/B, (w+1)/B)` forces every block to differ from `w`. -/
lemma block_ne_of_omit {ℓ w : ℕ} {x : ℝ}
    (homit : ∀ m, orbit 4 x m ∉ Ico ((w : ℝ) / 4 ^ ℓ) (((w : ℝ) + 1) / 4 ^ ℓ))
    (n j : ℕ) : block ℓ x n j ≠ w := by
  intro hb
  apply homit (n + ℓ * j)
  have hp : (0 : ℝ) < (4 : ℝ) ^ ℓ := by positivity
  have hc := block_cast ℓ x n j
  rw [hb] at hc
  have hfl : ⌊orbit 4 x (n + ℓ * j) * (4 : ℝ) ^ ℓ⌋ = (w : ℤ) := by exact_mod_cast hc.symm
  rw [Int.floor_eq_iff] at hfl
  push_cast at hfl
  constructor
  · rw [div_le_iff₀ hp]; exact hfl.1
  · rw [lt_div_iff₀ hp]; exact hfl.2

/-- The left endpoint of the cylinder indexed by a block sequence `b : Fin M → Fin B`. -/
noncomputable def cylLeft (B M : ℕ) (b : Fin M → Fin B) : ℝ :=
  ∑ j : Fin M, ((b j : ℕ) : ℝ) / (B : ℝ) ^ ((j : ℕ) + 1)

/-- The closed cylinder `[cylLeft b, cylLeft b + B^{−M}]`. -/
noncomputable def cyl (B M : ℕ) (b : Fin M → Fin B) : Set ℝ :=
  Icc (cylLeft B M b) (cylLeft B M b + 1 / (B : ℝ) ^ M)

/-- The admissible block sequences: every block differs from `w`. -/
def admissible (B M : ℕ) (w : Fin B) : Finset (Fin M → Fin B) :=
  Fintype.piFinset fun _ => Finset.univ.erase w

lemma card_admissible (B M : ℕ) (w : Fin B) : (admissible B M w).card = (B - 1) ^ M := by
  unfold admissible
  rw [Fintype.card_piFinset]
  simp [Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin]

/-- Every orbit point lies in an admissible closed cylinder. -/
theorem orbit_mem_cyl {ℓ w : ℕ} {x : ℝ} (hw : w < 4 ^ ℓ)
    (homit : ∀ m, orbit 4 x m ∉ Ico ((w : ℝ) / 4 ^ ℓ) (((w : ℝ) + 1) / 4 ^ ℓ))
    (M n : ℕ) :
    ∃ b ∈ admissible (4 ^ ℓ) M ⟨w, hw⟩, orbit 4 x n ∈ cyl (4 ^ ℓ) M b := by
  refine ⟨fun j => ⟨block ℓ x n j, block_lt ℓ x n j⟩, ?_, ?_⟩
  · rw [admissible, Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_erase]
    exact ⟨fun h => block_ne_of_omit homit n j (by simpa [Fin.ext_iff] using h), Finset.mem_univ _⟩
  · have hexp := orbit_expansion ℓ x n M
    have hleft : cylLeft (4 ^ ℓ) M (fun j => ⟨block ℓ x n j, block_lt ℓ x n j⟩)
        = ∑ j ∈ range M, (block ℓ x n j : ℝ) / ((4 : ℝ) ^ ℓ) ^ (j + 1) := by
      unfold cylLeft
      rw [Finset.sum_range]
      push_cast; rfl
    have hp : (0 : ℝ) < ((4 : ℝ) ^ ℓ) ^ M := by positivity
    have h0 := (orbit_mem_Ico 4 x (n + ℓ * M)).1
    have h1 := (orbit_mem_Ico 4 x (n + ℓ * M)).2
    constructor
    · rw [hleft, hexp]
      have : 0 ≤ orbit 4 x (n + ℓ * M) / ((4 : ℝ) ^ ℓ) ^ M := by positivity
      linarith
    · rw [hleft, hexp]
      push_cast
      have : orbit 4 x (n + ℓ * M) / ((4 : ℝ) ^ ℓ) ^ M ≤ 1 / ((4 : ℝ) ^ ℓ) ^ M := by
        gcongr
      linarith

/-- **Cylinder covering of the orbit closure.**  If the base-four orbit of `x` omits the
cylinder `[w/4^ℓ, (w+1)/4^ℓ)`, its closure in the circle is covered by the `(4^ℓ−1)^M`
admissible closed cylinders of length `4^{−ℓM}`. -/
theorem orbitClosure_subset_cylinders {ℓ w : ℕ} {x : ℝ} (hw : w < 4 ^ ℓ)
    (homit : ∀ m, orbit 4 x m ∉ Ico ((w : ℝ) / 4 ^ ℓ) (((w : ℝ) + 1) / 4 ^ ℓ)) (M : ℕ) :
    closure (Set.range fun n : ℕ => ((orbit 4 x n : ℝ) : UnitAddCircle))
      ⊆ ⋃ b ∈ admissible (4 ^ ℓ) M ⟨w, hw⟩,
          ((↑) : ℝ → UnitAddCircle) '' cyl (4 ^ ℓ) M b := by
  refine closure_minimal ?_ ?_
  · rintro _ ⟨n, rfl⟩
    obtain ⟨b, hb, hmem⟩ := orbit_mem_cyl hw homit M n
    exact Set.mem_biUnion hb ⟨_, hmem, rfl⟩
  · refine Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun b _ => ?_
    exact (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed

end G4
end NormalNumbers
