/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Disjunctive

/-!
# G4 disjunctivity, §4B: cylinder covering of an orbit closure that omits a word

If the base-`b` orbit of `x` never enters the cylinder `[w/B, (w+1)/B)`, `B = b^ℓ`, then for
every `M` the orbit closure (in the circle) is covered by the `(B−1)^M` closed cylinders of
length `B^{−M}` whose `M` blocks (base-`B` digits) all differ from `w`
(`orbitClosure_subset_cylinders`).  This is the covering exponent `d = log_B(B−1) < 1` of
draft (4.4), in finite covering-number form (no box-dimension library).

**Proved for every base `b ≥ 1`** (campaign G4B, brief §7.1); `G4GridTube` instantiates at
`b = 4`.  Ingredients: the orbit shift `orbit b x (n+k) = fract (orbit b x n · b^k)`, the
block digits `block b ℓ x n j = ⌊orbit b x (n + ℓ j) · B⌋`, the finite base-`B` expansion
`orbit b x n = ∑_{j<M} block_j / B^{j+1} + orbit b x (n + ℓM) / B^M`, and the omission
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

/-- The `j`-th base-`b^ℓ` block of the orbit point `orbit b x n`. -/
noncomputable def block (bb ℓ : ℕ) (x : ℝ) (n j : ℕ) : ℕ :=
  (⌊orbit bb x (n + ℓ * j) * (bb : ℝ) ^ ℓ⌋).toNat

lemma floor_orbit_mul_nonneg (bb ℓ : ℕ) (x : ℝ) (m : ℕ) :
    0 ≤ ⌊orbit bb x m * (bb : ℝ) ^ ℓ⌋ :=
  Int.floor_nonneg.mpr (mul_nonneg (orbit_mem_Ico bb x m).1
    (pow_nonneg (Nat.cast_nonneg bb) ℓ))

lemma block_cast (bb ℓ : ℕ) (x : ℝ) (n j : ℕ) :
    (block bb ℓ x n j : ℝ) = (⌊orbit bb x (n + ℓ * j) * (bb : ℝ) ^ ℓ⌋ : ℝ) := by
  unfold block
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (floor_orbit_mul_nonneg bb ℓ x _)]

lemma block_lt {bb : ℕ} (hbb : 0 < bb) (ℓ : ℕ) (x : ℝ) (n j : ℕ) :
    block bb ℓ x n j < bb ^ ℓ := by
  have hbpos : (0 : ℝ) < (bb : ℝ) := by exact_mod_cast hbb
  have hp : (0 : ℝ) < (bb : ℝ) ^ ℓ := pow_pos hbpos ℓ
  have h1 : (block bb ℓ x n j : ℝ) ≤ orbit bb x (n + ℓ * j) * (bb : ℝ) ^ ℓ := by
    rw [block_cast]; exact Int.floor_le _
  have h2 : orbit bb x (n + ℓ * j) * (bb : ℝ) ^ ℓ < (bb : ℝ) ^ ℓ := by
    have := (orbit_mem_Ico bb x (n + ℓ * j)).2
    nlinarith
  exact_mod_cast h1.trans_lt h2

/-- One digit step: `y = ⌊yB⌋/B + fract(yB)/B`. -/
lemma orbit_eq_block_add {bb : ℕ} (hbb : 0 < bb) (ℓ : ℕ) (x : ℝ) (n j : ℕ) :
    orbit bb x (n + ℓ * j)
      = (block bb ℓ x n j : ℝ) / (bb : ℝ) ^ ℓ
        + orbit bb x (n + ℓ * (j + 1)) / (bb : ℝ) ^ ℓ := by
  have hbpos : (0 : ℝ) < (bb : ℝ) := by exact_mod_cast hbb
  have hp : (0 : ℝ) < (bb : ℝ) ^ ℓ := pow_pos hbpos ℓ
  rw [show n + ℓ * (j + 1) = (n + ℓ * j) + ℓ by ring, orbit_add bb x (n + ℓ * j) ℓ, block_cast]
  push_cast
  rw [← add_div, Int.floor_add_fract, mul_div_cancel_right₀ _ hp.ne']

/-- The finite base-`B` expansion of an orbit point, `B = b^ℓ`. -/
theorem orbit_expansion {bb : ℕ} (hbb : 0 < bb) (ℓ : ℕ) (x : ℝ) (n M : ℕ) :
    orbit bb x n = ∑ j ∈ range M, (block bb ℓ x n j : ℝ) / ((bb : ℝ) ^ ℓ) ^ (j + 1)
      + orbit bb x (n + ℓ * M) / ((bb : ℝ) ^ ℓ) ^ M := by
  have hbpos : (0 : ℝ) < (bb : ℝ) := by exact_mod_cast hbb
  have hp : (0 : ℝ) < (bb : ℝ) ^ ℓ := pow_pos hbpos ℓ
  induction M with
  | zero => simp
  | succ M ih =>
    rw [ih, Finset.sum_range_succ, orbit_eq_block_add hbb ℓ x n M]
    field_simp
    ring

/-- Omission of the cylinder `[w/B, (w+1)/B)` forces every block to differ from `w`. -/
lemma block_ne_of_omit {bb ℓ w : ℕ} (hbb : 0 < bb) {x : ℝ}
    (homit : ∀ m, orbit bb x m ∉ Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ))
    (n j : ℕ) : block bb ℓ x n j ≠ w := by
  intro hb
  apply homit (n + ℓ * j)
  have hbpos : (0 : ℝ) < (bb : ℝ) := by exact_mod_cast hbb
  have hp : (0 : ℝ) < (bb : ℝ) ^ ℓ := pow_pos hbpos ℓ
  have hc := block_cast bb ℓ x n j
  rw [hb] at hc
  have hfl : ⌊orbit bb x (n + ℓ * j) * (bb : ℝ) ^ ℓ⌋ = (w : ℤ) := by exact_mod_cast hc.symm
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
theorem orbit_mem_cyl {bb ℓ w : ℕ} (hbb : 0 < bb) {x : ℝ} (hw : w < bb ^ ℓ)
    (homit : ∀ m, orbit bb x m ∉ Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ))
    (M n : ℕ) :
    ∃ b ∈ admissible (bb ^ ℓ) M ⟨w, hw⟩, orbit bb x n ∈ cyl (bb ^ ℓ) M b := by
  have hbpos : (0 : ℝ) < (bb : ℝ) := by exact_mod_cast hbb
  refine ⟨fun j => ⟨block bb ℓ x n j, block_lt hbb ℓ x n j⟩, ?_, ?_⟩
  · rw [admissible, Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_erase]
    exact ⟨fun h => block_ne_of_omit hbb homit n j (by simpa [Fin.ext_iff] using h),
      Finset.mem_univ _⟩
  · have hexp := orbit_expansion hbb ℓ x n M
    have hcastB : ((bb ^ ℓ : ℕ) : ℝ) = (bb : ℝ) ^ ℓ := by push_cast; ring
    have hleft : cylLeft (bb ^ ℓ) M (fun j => ⟨block bb ℓ x n j, block_lt hbb ℓ x n j⟩)
        = ∑ j ∈ range M, (block bb ℓ x n j : ℝ) / ((bb : ℝ) ^ ℓ) ^ (j + 1) := by
      unfold cylLeft
      rw [Finset.sum_range]
      simp only [hcastB]
    have hp : (0 : ℝ) < ((bb : ℝ) ^ ℓ) ^ M := by positivity
    have h0 := (orbit_mem_Ico bb x (n + ℓ * M)).1
    have h1 := (orbit_mem_Ico bb x (n + ℓ * M)).2
    rw [cyl, hcastB]
    constructor
    · rw [hleft, hexp]
      have : 0 ≤ orbit bb x (n + ℓ * M) / ((bb : ℝ) ^ ℓ) ^ M := by positivity
      linarith
    · rw [hleft, hexp]
      have : orbit bb x (n + ℓ * M) / ((bb : ℝ) ^ ℓ) ^ M ≤ 1 / ((bb : ℝ) ^ ℓ) ^ M := by
        gcongr
      linarith

/-- **Cylinder covering of the orbit closure.**  If the base-`b` orbit of `x` omits the
cylinder `[w/b^ℓ, (w+1)/b^ℓ)`, its closure in the circle is covered by the `(b^ℓ−1)^M`
admissible closed cylinders of length `b^{−ℓM}`. -/
theorem orbitClosure_subset_cylinders {bb ℓ w : ℕ} (hbb : 0 < bb) {x : ℝ} (hw : w < bb ^ ℓ)
    (homit : ∀ m, orbit bb x m ∉ Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ))
    (M : ℕ) :
    closure (Set.range fun n : ℕ => ((orbit bb x n : ℝ) : UnitAddCircle))
      ⊆ ⋃ b ∈ admissible (bb ^ ℓ) M ⟨w, hw⟩,
          ((↑) : ℝ → UnitAddCircle) '' cyl (bb ^ ℓ) M b := by
  refine closure_minimal ?_ ?_
  · rintro _ ⟨n, rfl⟩
    obtain ⟨b, hb, hmem⟩ := orbit_mem_cyl hbb hw homit M n
    exact Set.mem_biUnion hb ⟨_, hmem, rfl⟩
  · refine Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun b _ => ?_
    exact (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed

end G4
end NormalNumbers
