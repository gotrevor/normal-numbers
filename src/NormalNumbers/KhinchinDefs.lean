/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFDefs

/-!
# Frozen Khinchin definitions (layering split for route D′)

`khinchinK₀` and `KhinchinTypical` were originally introduced in `Headline.lean`
(JUDGE-frozen, 2026-08-23).  They are relocated here **byte-identical** (same
type, same body) so the Khinchin machinery (`Khinchin.lean`) can prove
`xstar_khinchinTypical` UPSTREAM of `Headline.lean`, letting `Headline.lean`
import it to discharge the Tier-2 headline without an import cycle.  The
statement content is unchanged — the JUDGE freeze is preserved; the anchors that
pin the `tprod`'s index alignment (`k ↦ k+1`) stay in `Headline.lean`.
-/

namespace NormalNumbers

/-- **Khinchin's constant** `K₀ = ∏_{a≥1} (1 + 1/(a(a+2)))^{log₂ a}
≈ 2.685…`, as a `tprod` over `k : ℕ` with digit value `a = k + 1`
(anchors in `Headline.lean` pin the alignment). -/
noncomputable def khinchinK₀ : ℝ :=
  ∏' k : ℕ, (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) ^ Real.logb 2 ((k : ℝ) + 1)

/-- Khinchin-typical: the geometric mean of the CF digits tends to `K₀`. -/
def KhinchinTypical (x : ℝ) : Prop :=
  Filter.Tendsto
    (fun n => (∏ i ∈ Finset.range n, (cfDigit x i : ℝ)) ^ (1 / (n : ℝ)))
    Filter.atTop (nhds khinchinK₀)

end NormalNumbers
