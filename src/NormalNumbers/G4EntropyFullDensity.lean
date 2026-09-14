/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyFullSeq
import NormalNumbers.G4EntropyEnum

/-!
# The schedule-only read visits a **density-zero** set of digit positions

`G4EntropyFullSeq.isSampled_fullPos` says every position `fullPos j` is a sampled position;
`G4EntropyEnum.tendsto_density_isSampled` says the sampled positions have density zero.  This
module states the consequence about `fullPos` itself, which is the honest description of what
`fullReal` is:

    `|{j < L : j ∈ range fullPos}| / L → 0`     (`tendsto_density_fullPos`)

So `fullReal`'s digits are `G₄`'s digits along a set of density zero.  This is *not* a defect of
the construction — `G4EntropyMixture.wall_at_zero_deficit` shows no certified read can do better
— but it is what separates "a new normal number read off `G₄`" from "`G₄` is normal": the read
misses almost every digit, so `IsNormal 2 fullReal` carries no information about `IsNormal 2 G₄`.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

open Classical in
/-- **The schedule-only read visits a density-zero set of positions.** -/
theorem tendsto_density_fullPos :
    Tendsto (fun L => (((Finset.range L).filter (fun j => ∃ k, fullPos k = j)).card : ℝ)
        / (L : ℝ)) atTop (nhds 0) := by
  classical
  refine squeeze_zero (fun L => by positivity) (fun L => ?_) tendsto_density_isSampled
  have hsub : (Finset.range L).filter (fun j => ∃ k, fullPos k = j)
      ⊆ (Finset.range L).filter IsSampled := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    obtain ⟨k, hk⟩ := hj.2
    exact ⟨hj.1, hk ▸ isSampled_fullPos k⟩
  have hcard : (((Finset.range L).filter (fun j => ∃ k, fullPos k = j)).card : ℝ)
      ≤ (((Finset.range L).filter IsSampled).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact div_le_div_of_nonneg_right hcard (by positivity) |>.trans_eq rfl

end NormalNumbers.G4.Sched
