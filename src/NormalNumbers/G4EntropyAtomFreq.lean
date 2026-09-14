/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWindows
import NormalNumbers.G4EntropyPosition

/-!
# Entropy expedition — one atom already carries every word at its correct frequency

`tendsto_occursCountP_primeLambertFour` averages over **all** triples `(n, α, p)`.  This module
renders `G4EntropyGoodAtoms.coordAvg` at the schedule and shows the average over `α` is not
needed: at each scale there is a *single* atom whose own windows already carry every binary word
at its correct density, to within `2√(log 2·ℓ·100√K/(m_K−ℓ+1))`.

The atom is chosen by `exists_good_coord`, which is `ℓ`- and word-free — so **one** atom works
for every word of every length at that scale.  Combined with `window_gap_same_atom` (the windows
at a fixed atom are pairwise disjoint), this is a window family that is simultaneously

* certified — its own statistics obey the capture bound, with no averaging over atoms, and
* geometrically clean — its windows never overlap, so reading it in position order is literally
  the concatenation of its window contents.

That pair is what a subsequence construction consumes.  It does **not** give normality: by
`certified_granule_exceeds_previous_scale`, the prefix frequencies still cannot converge across
scales.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The count rendering of one atom's average -/

open Classical in
/-- **One atom's count rendering.**  `coordAvg` at the scale-`i` law is the density, among the
`|P_K|·(m_K−ℓ+1)` pairs `(n, p)` at the fixed atom `α`, of those whose `ℓ`-block at window
position `p` is `w`. -/
theorem coordAvg_eq_count (i ℓ : ℕ) (x : ℝ) (α : (gridAt i).Atom) (w : Fin (2 ^ ℓ)) :
    coordAvg (kk i) ℓ (jointLawAt i x) α w
      = (∑ p : Fin (kk i - ℓ + 1),
            (((PK i).filter fun n =>
              posAt (kk i) ℓ (p : ℕ) (ZVec (gridAt i) (kk i) x n α) = w).card : ℝ))
        / (((PK i).card : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ)) := by
  classical
  have hp : ∀ p : Fin (kk i - ℓ + 1),
      ((soloLaw (jointLawAt i x) α).map
          (fun z : Unit → Fin (2 ^ kk i) => posAt (kk i) ℓ (p : ℕ) (z default))).prob {w}
        = (((PK i).filter fun n =>
              posAt (kk i) ℓ (p : ℕ) (ZVec (gridAt i) (kk i) x n α) = w).card : ℝ)
          / ((PK i).card : ℝ) := by
    intro p
    rw [soloLaw, FinLaw.prob_singleton_map_map, FinLaw.prob, Finset.sum_singleton]
    exact map_empirical_p (apSample_nonempty (gridAt i) (b₀_lt_X_at i)) _ _ w
  rw [coordAvg, posAvg, Fintype.sum_prod_type]
  simp only [Fintype.card_unit, Nat.cast_one, one_mul, Finset.univ_unique,
    Finset.sum_singleton, hp]
  rw [← Finset.sum_div, div_div]

open Classical in
/-- **One atom's digit rendering.** -/
theorem coordAvg_eq_digits (i ℓ : ℕ) (hℓm : ℓ ≤ kk i) (x : ℝ) (α : (gridAt i).Atom)
    (w : Fin (2 ^ ℓ)) :
    coordAvg (kk i) ℓ (jointLawAt i x) α w
      = (∑ p : Fin (kk i - ℓ + 1),
            (((PK i).filter fun n =>
              blockVal (Int.fract x) (2 * kIdx (gridAt i) n α + (p : ℕ)) ℓ = (w : ℕ)).card : ℝ))
        / (((PK i).card : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ)) := by
  classical
  rw [coordAvg_eq_count i ℓ x α w]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  have hZ : ∀ n : ℕ, ZVec (gridAt i) (kk i) x n α
      = ⟨blockVal (Int.fract x) (2 * kIdx (gridAt i) n α) (kk i), blockVal_lt _ _ _⟩ :=
    fun n => Fin.ext (ZSample_eq_blockVal (gridAt i) (kk i) x n α)
  have hfit : (p : ℕ) + ℓ ≤ kk i := by
    have := p.isLt
    omega
  refine Finset.filter_congr fun n _ => ?_
  rw [hZ n, posAt_blockVal _ _ _ _ _ hfit]
  exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

/-! ### The good atom at scale `i` -/

/-- The scale-`i` per-window deficit at `ρ = 1/2`: `entropy_E1`'s `50√K`, doubled. -/
noncomputable def atomDeficit (i : ℕ) : ℝ := 100 * Real.sqrt (KK i)

open Classical in
/-- **At every scale one atom is good for every word of every length.**  `exists_good_coord` at
`ρ = 1/2`, fed `entropy_E1`'s deficit. -/
theorem exists_good_atom (i : ℕ) :
    ∃ α : (gridAt i).Atom, ∀ ℓ : ℕ, 0 < ℓ → ℓ ≤ kk i → ∀ w : Fin (2 ^ ℓ),
      |coordAvg (kk i) ℓ (jointLawAt i (primeLambertAtBase 4)) α w - 1 / (2 : ℝ) ^ ℓ|
        ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * atomDeficit i / ((kk i : ℝ) - ℓ + 1)) := by
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hδ : (0 : ℝ) < 50 * Real.sqrt (KK i) := by
    have := Real.sqrt_pos.2 hKpos
    linarith
  obtain ⟨α, hα⟩ := exists_good_coord (jointLawAt i (primeLambertAtBase 4)) hδ
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1) (deficit_primeLambertFour i)
  refine ⟨α, fun ℓ hℓ hℓm w => ?_⟩
  have h := hα ℓ hℓ hℓm w
  have hrw : 50 * Real.sqrt (KK i) / (1 / 2 : ℝ) = atomDeficit i := by
    rw [atomDeficit]; ring
  rwa [hrw] at h

end NormalNumbers.G4.Sched
