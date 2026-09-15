/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWTrunc

/-!
# The certified occurrence count at a **truncated** scale

`G4EntropyFullSeqW` renders `posAvg` of the band law *at the band's own top* as a count of
triples `(n, α, p)` (`posAvg_bandWLawTop_eq_count`, `posAvg_bandWLawTop_eq_digits`).  Nothing in
those proofs used `X' = wTop i`: they only need the truncated sample to be nonempty, which the
gate supplies.  This module restates them at a general gated `X' ≤ wTop i` and packages the
result with `abs_posAvg_bandWLaw_le` into the single estimate the mid-band sandwich consumes:

> `abs_occ_bandWtr_sub_le` : the density, among the `|bandWtr i X'|·|Atom|·(kk−ℓ+1)` triples, of
> those at which `v` occurs is within `2√(808 log 2·ℓ/√K)` of `2^{−ℓ}`.

The final lemma `pairCount_prod_eq` re-sums that count over the **product** collection
`bandWtr i X' ×ˢ univ` — the shape of the two flanks of `G4EntropyWTrunc`.
-/

open Finset

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The count and digit renderings at a truncated scale -/

open Classical in
/-- **The truncated band's count rendering** (`posAvg_bandWLawTop_eq_count` at a general gated
scale). -/
theorem posAvg_bandWLaw_eq_count (i X' ℓ : ℕ)
    (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') (x : ℝ) (w : Fin (2 ^ ℓ)) :
    posAvg (kk i) ℓ (bandWLaw i X' hg x) w
      = (∑ c : (gridAt i).Atom × Fin (kk i - ℓ + 1),
            (((bandWtr i X').filter fun n =>
              posAt (kk i) ℓ (c.2 : ℕ) (ZVec (gridAt i) (kk i) x n c.1) = w).card : ℝ))
        / (((bandWtr i X').card : ℝ)
            * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ))) := by
  classical
  have hp : ∀ c : (gridAt i).Atom × Fin (kk i - ℓ + 1),
      ((bandWLaw i X' hg x).map (fun z => posAt (kk i) ℓ (c.2 : ℕ) (z c.1))).prob {w}
        = (((bandWtr i X').filter fun n =>
              posAt (kk i) ℓ (c.2 : ℕ) (ZVec (gridAt i) (kk i) x n c.1) = w).card : ℝ)
          / ((bandWtr i X').card : ℝ) := by
    intro c
    rw [FinLaw.prob, Finset.sum_singleton]
    exact map_empirical_p (bandWtr_nonempty hg) _ _ w
  have hsum : (∑ c : (gridAt i).Atom × Fin (kk i - ℓ + 1),
        ((bandWLaw i X' hg x).map (fun z => posAt (kk i) ℓ (c.2 : ℕ) (z c.1))).prob {w})
      = (∑ c : (gridAt i).Atom × Fin (kk i - ℓ + 1),
          (((bandWtr i X').filter fun n =>
            posAt (kk i) ℓ (c.2 : ℕ) (ZVec (gridAt i) (kk i) x n c.1) = w).card : ℝ))
        / ((bandWtr i X').card : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun c _ => hp c
  rw [posAvg, hsum, div_div]

open Classical in
/-- **The truncated band's digit rendering.** -/
theorem posAvg_bandWLaw_eq_digits (i X' ℓ : ℕ)
    (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') (hℓm : ℓ ≤ kk i) (x : ℝ) (w : Fin (2 ^ ℓ)) :
    posAvg (kk i) ℓ (bandWLaw i X' hg x) w
      = (∑ c : (gridAt i).Atom × Fin (kk i - ℓ + 1),
            (((bandWtr i X').filter fun n =>
              blockVal (Int.fract x) (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ)) ℓ
                = (w : ℕ)).card : ℝ))
        / (((bandWtr i X').card : ℝ)
            * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ))) := by
  classical
  rw [posAvg_bandWLaw_eq_count i X' ℓ hg x w]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  have hZ : ∀ n : ℕ, ZVec (gridAt i) (kk i) x n c.1
      = ⟨blockVal (Int.fract x) (2 * kIdx (gridAt i) n c.1) (kk i), blockVal_lt _ _ _⟩ :=
    fun n => Fin.ext (ZSample_eq_blockVal (gridAt i) (kk i) x n c.1)
  have hfit : (c.2 : ℕ) + ℓ ≤ kk i := by
    have := c.2.isLt
    omega
  refine Finset.filter_congr fun n _ => ?_
  rw [hZ n, posAt_blockVal _ _ _ _ _ hfit]
  exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

/-! ### The packaged capture estimate -/

open Classical in
/-- **The truncated band's certified occurrence density.**  At every gated scale `X'` inside the
tile, the proportion of triples `(n, α, p)` with `n ∈ bandWtr i X'` at which `v` occurs in `G₄`'s
binary digits at `2·kIdx(n,α) + p` is within `2√(808 log 2·ℓ/√K)` of `2^{−|v|}`.

This is the estimate the mid-band sandwich applies at **both** flanks `cutLo i c` and
`cutHi i c`. -/
theorem abs_occ_bandWtr_sub_le (i X' : ℕ) (v : List ℕ)
    (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') (hhi : X' ≤ Xlo (KK (i + 1)))
    (hlen : 0 < v.length) (hℓm : 2 * v.length ≤ kk i)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) :
    |(∑ c : (gridAt i).Atom × Fin (kk i - v.length + 1),
          (((bandWtr i X').filter fun n =>
            OccursAt 2 (primeLambertAtBase 4) v
              (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card : ℝ))
        / (((bandWtr i X').card : ℝ)
            * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)))
      - 1 / (2 : ℝ) ^ v.length|
      ≤ 2 * Real.sqrt (808 * Real.log 2 * (v.length : ℝ) / Real.sqrt (KK i)) := by
  classical
  set w : Fin (2 ^ v.length) := ⟨wordVal v, wordVal_lt hv⟩ with hw
  have hle : v.length ≤ kk i := by omega
  have hren : posAvg (kk i) v.length (bandWLaw i X' hg (primeLambertAtBase 4)) w
      = (∑ c : (gridAt i).Atom × Fin (kk i - v.length + 1),
            (((bandWtr i X').filter fun n =>
              OccursAt 2 (primeLambertAtBase 4) v
                (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card : ℝ))
        / (((bandWtr i X').card : ℝ)
            * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ))) := by
    rw [posAvg_bandWLaw_eq_digits i X' v.length hg hle _ w]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 2
    refine Finset.filter_congr fun n _ => ?_
    exact blockVal_eq_wordVal_iff (y := primeLambertAtBase 4) hv
  rw [← hren]
  exact abs_posAvg_bandWLaw_le i X' v.length hg hhi hlen hℓm w

/-! ### The count, re-summed over a product collection -/

open Classical in
/-- **The triple count over any sample set is the pair sum of window counts.**  This is
`pairCountW_eq` with `bandW i` replaced by an arbitrary `S`; the proof never used the band. -/
theorem pairCount_prod_eq (i : ℕ) (S : Finset ℕ) (x : ℝ) (v : List ℕ) :
    ∑ c : (gridAt i).Atom × Fin (kk i - v.length + 1),
        (S.filter fun n =>
          OccursAt 2 x v (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card
      = ∑ z ∈ S ×ˢ (Finset.univ : Finset (gridAt i).Atom),
          winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) := by
  classical
  have hL : ∑ c : (gridAt i).Atom × Fin (kk i - v.length + 1),
        (S.filter fun n =>
          OccursAt 2 x v (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card
      = ∑ α : (gridAt i).Atom, ∑ p ∈ Finset.range (kk i - v.length + 1),
          ∑ n ∈ S,
            (if OccursAt 2 x v (2 * kIdx (gridAt i) n α + p) then 1 else 0) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun p =>
      ∑ n ∈ S, (if OccursAt 2 x v (2 * kIdx (gridAt i) n α + p) then 1 else 0))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.card_filter]
  have hR : ∑ z ∈ S ×ˢ (Finset.univ : Finset (gridAt i).Atom),
        winOccW i x v (2 * kIdx (gridAt i) z.1 z.2)
      = ∑ n ∈ S, ∑ α : (gridAt i).Atom,
          ∑ p ∈ Finset.range (kk i - v.length + 1),
            (if OccursAt 2 x v (2 * kIdx (gridAt i) n α + p) then 1 else 0) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun α _ => ?_
    rw [winOccW, Finset.card_filter]
  rw [hL, hR]
  rw [Finset.sum_congr rfl (fun (α : (gridAt i).Atom) _ =>
    Finset.sum_comm (s := Finset.range (kk i - v.length + 1)) (t := S)
      (f := fun p n => if OccursAt 2 x v (2 * kIdx (gridAt i) n α + p) then 1 else 0))]
  exact Finset.sum_comm

end NormalNumbers.G4.Sched
