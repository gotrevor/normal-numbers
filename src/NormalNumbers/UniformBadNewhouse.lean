/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.UniformBadThreshold

/-!
# The Newhouse route to `c⋆ ≤ 4`

**Idea (c⋆ lap 5).**  Counting and potential engines lose a dimension deficit: they charge a
window against a sparse alive set (`UniformBadJoint`, Maze row "counted medium bases").  The
Newhouse gap lemma has no such loss: two compact sets with thicknesses `τ₁ τ₂ > 1`, neither inside
a gap of the other, intersect.  Split the bases as `{2}` against `{b ≥ 3}`:

* `A = E₂(4) = {x ∈ [0,1] : ‖2ⁿx‖ ≥ 2⁻⁴ ∀ n}` has thickness exactly `3` (`thick_E2_four`).  Its
  gaps are `A/2ⁿ ± 2⁻ⁿ/15` (each window `A/2ⁿ ± 2^{−n−4}` absorbs the cascade of windows at its
  edges, `1/15 = 0.000100010001…₂`); the worst ratio is the gap around `1/8`, of length `1/60`,
  with bridge `1/20` to the gap around `0`.
* `B ⊆ ⋂_{b ≥ 3} E_b(4)` must be compact with thickness `> 1/3` (`ThickCore`).  The raw intersection
  has thickness `0` (windows of different bases can nearly touch), but merging the near-touching
  windows costs almost nothing: probe `scripts/cstar_models/thick.py`,
  `merge.py` (bases `3 … 40`, all windows of length `≥ 3·10⁻⁷`): forcing thickness `0.4 / 1 / 2`
  needs `26 / 64 / 126` merges among `≈ 56 700` gaps, and the hull `[1/80, 79/80]` is untouched.
* The intersection point then has `‖bⁿξ‖ ≥ b⁻⁴` for every `b ≥ 2` (`cStar_le_four_of_newhouse`).

Control (known answer): below the lower bound `c⋆ ≥ 12/5` the same probe collapses (`c = 2.2, 2.4`:
the merged `E₂` shrinks to a neighbourhood of `2/3` and the merged `B` has thickness `< 0.005`).
At `c = 3`, `τ(E₂(3)) = 1` and the merged `B` reaches `1.05`, so the route plausibly gives `c⋆ ≤ 3`
as well (`CStarLeThree`), with a thin margin.
-/

namespace NormalNumbers.UniformBadThreshold

open NormalNumbers.UniformBad (dnear)

namespace Newhouse

/-- `(a, b)` is a bounded gap of `K`: its endpoints lie in `K` and it misses `K`. -/
def IsGap (K : Set ℝ) (a b : ℝ) : Prop := a < b ∧ a ∈ K ∧ b ∈ K ∧ Disjoint (Set.Ioo a b) K

/-- Newhouse thickness at least `τ`, in the separation form (Falconer–Yavicoli, Definition 3,
symmetrised): two disjoint gaps are at distance at least `τ` times the shorter one, and every gap
is at distance at least `τ` times its length from the ends of the convex hull. -/
def Thick (K : Set ℝ) (τ : ℝ) : Prop :=
  (∀ a b a' b', IsGap K a b → IsGap K a' b' → b ≤ a' →
      τ * min (b - a) (b' - a') ≤ a' - b) ∧
    ∀ a b, IsGap K a b → τ * (b - a) ≤ a - sInf K ∧ τ * (b - a) ≤ sSup K - b

/-- **Newhouse gap lemma** (Newhouse 1979; Falconer–Yavicoli 2022, Theorem 2).  Believed 95% for
this transcription (classical; the separation form of thickness used here is at least as strong as
the bridge form).  Two compact sets with `τ₁ τ₂ > 1` whose hulls overlap and neither of which lies
inside a bounded gap of the other intersect.

English proof (Palis–Takens).  If not, the hull condition gives a linked pair of gaps `(U₁, U₂)`
(each contains exactly one endpoint of the other).  At the endpoints, the bridges `C₁, C₂` satisfy
`|C₁| ≥ τ₁|U₁|`, `|C₂| ≥ τ₂|U₂|`, so `|C₁| > |U₂|` or `|C₂| > |U₁|`; in the first case the far endpoint
of `U₂` lies in `C₁`, hence in a gap of `K₁` shorter than `U₁`, linked with `U₂`.  Gap lengths in a
compact set accumulate only at `0`, so the linked pairs shrink to a common point of `K₁ ∩ K₂`. -/
theorem gap_lemma {K₁ K₂ : Set ℝ} {τ₁ τ₂ : ℝ} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂)
    (hne₁ : K₁.Nonempty) (hne₂ : K₂.Nonempty) (ht₁ : Thick K₁ τ₁) (ht₂ : Thick K₂ τ₂)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ : 1 < τ₁ * τ₂)
    (hhull₁ : sInf K₁ ≤ sSup K₂) (hhull₂ : sInf K₂ ≤ sSup K₁)
    (hgap₁ : ¬ ∃ a b, IsGap K₁ a b ∧ K₂ ⊆ Set.Ioo a b)
    (hgap₂ : ¬ ∃ a b, IsGap K₂ a b ∧ K₁ ⊆ Set.Ioo a b) :
    (K₁ ∩ K₂).Nonempty := by
  sorry

/-- The base-`b` good set at exponent `c`: `‖bⁿx‖ ≥ b^{−c}` for every `n`. -/
def goodSet (c b : ℕ) : Set ℝ := {x | ∀ n : ℕ, ((b : ℝ) ^ c)⁻¹ ≤ dnear ((b : ℝ) ^ n * x)}

/-- `E₂(c)` on `[0, 1]`. -/
def E2 (c : ℕ) : Set ℝ := Set.Icc 0 1 ∩ goodSet c 2

/-- **Node.**  Believed 90%.  `E₂(4)` is compact, its hull is `[1/15, 14/15]`, its gaps have length
at most `1/15`, and its thickness is `3` (probe: `thick.py 4 1e-7 2` returns exactly `3.000`, at the
gap `(7/60, 2/15)`).  Proof plan: the gaps are `A/2ⁿ ± 2⁻ⁿ/15` (`A` odd), and the bridge from the
gap of order `n` to a gap of order `m ≤ n` is `(k − (2^{n−m} + 1)/15)·2⁻ⁿ` for the least admissible
integer `k`, whose ratio to `2·2⁻ⁿ/15` is at least `3`. -/
theorem e2_four_facts :
    IsCompact (E2 4) ∧ (1 / 15 : ℝ) ∈ E2 4 ∧ (14 / 15 : ℝ) ∈ E2 4 ∧ E2 4 ⊆ Set.Icc (1 / 15) (14 / 15) ∧
      (∀ a b, IsGap (E2 4) a b → b - a ≤ 1 / 15) ∧ Thick (E2 4) 3 := by
  sorry

/-- **Crux node: a thick core for the bases `b ≥ 3`.**  A compact `B` inside every `E_b(c)`,
`b ≥ 3`, with thickness `τ`, short gaps, and points near both ends of `[0, 1]`.

Believed for `c = 4`, `τ = 2/5`: 70% (probe in the module doc: merging near-touching windows of
bases `3 … 40` to thickness `0.4` costs `26` merges and leaves the hull `[1/80, 79/80]`; the open
point is a worst-case bound on merge cascades at all scales and over all bases, where the windows
of distinct bases can cluster near rationals with large denominators). -/
def ThickCore (c : ℕ) (τ : ℝ) : Prop :=
  ∃ B : Set ℝ, IsCompact B ∧ Thick B τ ∧ (∀ b : ℕ, 3 ≤ b → B ⊆ goodSet c b) ∧
    (∀ a b, IsGap B a b → b - a ≤ 1 / 10) ∧
    (∃ x ∈ B, x ≤ 1 / 4) ∧ (∃ y ∈ B, 3 / 4 ≤ y) ∧ B ⊆ Set.Icc 0 1

/-- **The route.**  A thick core at exponent `4` with `τ > 1/3` gives `c⋆ ≤ 4`. -/
theorem cStar_le_four_of_newhouse {τ : ℝ} (hτ : 1 / 3 < τ) (h : ThickCore 4 τ) : cStar ≤ 4 := by
  obtain ⟨B, hBc, hBt, hBgood, hBgap, ⟨x, hxB, hx⟩, ⟨y, hyB, hy⟩, hB01⟩ := h
  obtain ⟨hAc, h1A, h2A, hAsub, hAgap, hAt⟩ := e2_four_facts
  have hτ0 : 0 < τ := lt_trans (by norm_num) hτ
  have hBbdd : BddBelow B := hBc.bddBelow
  have hBbddA : BddAbove B := hBc.bddAbove
  have hAbdd : BddBelow (E2 4) := hAc.bddBelow
  have hAbddA : BddAbove (E2 4) := hAc.bddAbove
  have hInfA : sInf (E2 4) ≤ 1 / 15 := csInf_le hAbdd h1A
  have hSupA : 14 / 15 ≤ sSup (E2 4) := le_csSup hAbddA h2A
  have hInfB : sInf B ≤ 1 / 4 := (csInf_le hBbdd hxB).trans hx
  have hSupB : 3 / 4 ≤ sSup B := hy.trans (le_csSup hBbddA hyB)
  obtain ⟨ξ, hξA, hξB⟩ := gap_lemma hAc hBc ⟨_, h1A⟩ ⟨x, hxB⟩ hAt hBt (by norm_num) hτ0
    (by nlinarith) (by linarith) (by linarith)
    (by
      rintro ⟨a, b, hab, hsub⟩
      have h1 := hsub hxB
      have h2 := hsub hyB
      have := hAgap a b hab
      simp only [Set.mem_Ioo] at h1 h2
      linarith)
    (by
      rintro ⟨a, b, hab, hsub⟩
      have h1 := hsub h1A
      have h2 := hsub h2A
      have := hBgap a b hab
      simp only [Set.mem_Ioo] at h1 h2
      linarith)
  -- ξ is good in every base
  have hgood : ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ, ((b : ℝ) ^ 4)⁻¹ ≤ dnear ((b : ℝ) ^ n * ξ) := by
    intro b hb n
    rcases (by omega : b = 2 ∨ 3 ≤ b) with rfl | hb3
    · exact hξA.2 n
    · exact hBgood b hb3 hξB n
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => csInf_le bddBelow_admissible ?_
  refine ⟨ξ, fun b hb n => lt_of_lt_of_le ?_ (hgood b hb n)⟩
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have h1 : (b : ℝ) ^ ((4 : ℕ) : ℝ) < (b : ℝ) ^ c :=
    Real.rpow_lt_rpow_of_exponent_lt hb1 (by exact_mod_cast hc)
  rw [Real.rpow_natCast] at h1
  rw [Real.rpow_neg (by positivity)]
  exact (inv_lt_inv₀ (by positivity) (by positivity)).2 h1

/-- **Crux statement (frozen 2026-10-07).**  Believed 70%: a thick core at `c = 4` with `τ = 2/5`. -/
theorem thickCore_four : ThickCore 4 (2 / 5) := by
  sorry

end Newhouse

end NormalNumbers.UniformBadThreshold
