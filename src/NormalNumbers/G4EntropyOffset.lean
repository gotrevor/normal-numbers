/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyTiling

/-!
# All offsets, not just the aligned ones

`G4EntropyTiling` controls the frequency of a word `w` among the `⌊m/ℓ⌋` blocks of the sampled
window that start at positions `0, ℓ, 2ℓ, …` — one *aligned* tiling.  Normality counts
occurrences at **every** position of the window, so the honest statement averages over the `ℓ`
offset classes `r = 0, …, ℓ−1`.

The reduction is free of loss.  Dropping the top `r` bits of each window is the map
`lowCoord`; the pair (top `r` bits, low `m−r` bits) is injective, so by generalized
subadditivity

    `H₂ L ≤ H₂ (L.map lowTuple) + |A|·r`,

i.e. a window law with deficit `δ·|A|` on `m` bits truncates to a window law with the **same**
deficit `δ·|A|` on `m − r` bits (the maximum drops by exactly `|A|·r` too).  The aligned tiling
of the truncated window is the offset-`r` tiling of the original, so every offset class inherits
the tiled capacity bound with `m` replaced by `m − r`.

* `FinLaw.map_map`, `FinLaw.H₂_map_injective` — pushforward algebra.
* `H₂_lowTuple_ge` — the truncation costs at most `|A|·r` bits.
* `abs_avg_block_prob_tile_opt` — the abstract, `t`-optimized form of
  `abs_avg_block_prob_tile_le` (the tiled capacity bound for a `FinLaw`, no schedule).
* `abs_avg_block_prob_offset_le` — the same bound for the offset-`r` tiling.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

namespace FinLaw

variable {Ω Ω' Ω'' : Type*} [Fintype Ω] [Fintype Ω'] [Fintype Ω'']

/-- **Entropy is invariant under an injective post-composition.** -/
theorem H₂_map_comp_injective [DecidableEq Ω'] [DecidableEq Ω''] (L : FinLaw Ω) (f : Ω → Ω')
    {g : Ω' → Ω''} (hg : Function.Injective g) :
    (L.map (fun ω => g (f ω))).H₂ = (L.map f).H₂ := by
  classical
  have key : ∀ ω' : Ω', (L.map (fun ω => g (f ω))).p (g ω') = (L.map f).p ω' := by
    intro ω'
    rw [map_p, map_p]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    refine Finset.filter_congr fun ω _ => ?_
    exact ⟨fun h => hg h, fun h => by rw [h]⟩
  have hzero : ∀ ω'' ∈ (Finset.univ : Finset Ω'') \ Finset.univ.image g,
      Real.negMulLog ((L.map (fun ω => g (f ω))).p ω'') = 0 := by
    intro ω'' hω''
    rw [Finset.mem_sdiff, Finset.mem_image] at hω''
    have hmass : (L.map (fun ω => g (f ω))).p ω'' = 0 := by
      rw [map_p]
      refine Finset.sum_eq_zero fun ω hω => ?_
      rw [Finset.mem_filter] at hω
      exact absurd ⟨f ω, Finset.mem_univ _, hω.2⟩ hω''.2
    rw [hmass, Real.negMulLog_zero]
  have hsum : ∑ ω'' : Ω'', Real.negMulLog ((L.map (fun ω => g (f ω))).p ω'')
      = ∑ ω' : Ω', Real.negMulLog ((L.map f).p ω') := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image g))
      (fun ω'' _ h => hzero ω'' (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩))]
    rw [Finset.sum_image (fun a _ b _ h => hg h)]
    exact Finset.sum_congr rfl fun ω' _ => by rw [key ω']
  rw [H₂, H₂, hsum]

end FinLaw

/-! ### Truncating the top `r` bits -/

/-- The low `m − r` bits of an `m`-bit window. -/
def lowCoord (m r : ℕ) (z : Fin (2 ^ m)) : Fin (2 ^ (m - r)) :=
  ⟨(z : ℕ) % 2 ^ (m - r), Nat.mod_lt _ (by positivity)⟩

/-- The top `r` bits, kept inside the `m`-bit alphabet. -/
def hiCoord (m r : ℕ) (z : Fin (2 ^ m)) : Fin (2 ^ m) :=
  ⟨(z : ℕ) / 2 ^ (m - r), lt_of_le_of_lt (Nat.div_le_self _ _) z.isLt⟩

/-- The truncation applied coordinatewise. -/
def lowTuple {A : Type*} (m r : ℕ) (z : A → Fin (2 ^ m)) : A → Fin (2 ^ (m - r)) :=
  fun α => lowCoord m r (z α)

/-- **Truncation costs at most `|A|·r` bits.** -/
theorem H₂_lowTuple_ge {A : Type*} [Fintype A] [DecidableEq A] {m r : ℕ} (hr : r ≤ m)
    (L : FinLaw (A → Fin (2 ^ m))) :
    L.H₂ - (Fintype.card A : ℝ) * r ≤ (L.map (lowTuple m r)).H₂ := by
  sorry

/-! ### The tiled capacity bound, abstract and `t`-optimized -/

/-- `abs_avg_block_prob_tile_le` with the free parameter optimized: a deficit of `δ` bits per
coordinate controls every `ℓ`-block word to within `2√(log 2 · ℓδ/m)`. -/
theorem abs_avg_block_prob_tile_opt {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    {m ℓ : ℕ} (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ))
    {δ : ℝ} (hδ : 0 < δ)
    (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂) :
    |(∑ c : A × Fin (m / ℓ), (L.map (fullCoord m ℓ c)).prob {w})
        / (Fintype.card (A × Fin (m / ℓ)) : ℝ) - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / (m : ℝ)) := by
  sorry

/-- **The offset-`r` tiling obeys the same capacity bound**, with `m` replaced by `m − r`:
every one of the `ℓ` offset classes of the window is controlled. -/
theorem abs_avg_block_prob_offset_le {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    {m ℓ r : ℕ} (hℓ : 0 < ℓ) (hr : r + ℓ ≤ m) (L : FinLaw (A → Fin (2 ^ m)))
    (w : Fin (2 ^ ℓ)) {δ : ℝ} (hδ : 0 < δ)
    (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂) :
    |(∑ c : A × Fin ((m - r) / ℓ),
          ((L.map (lowTuple m r)).map (fullCoord (m - r) ℓ c)).prob {w})
        / (Fintype.card (A × Fin ((m - r) / ℓ)) : ℝ) - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - r)) := by
  sorry

end NormalNumbers.G4Entropy
