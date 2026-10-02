/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LiteratureCampbell
import NormalNumbers.JointLambertQuantitative

/-!
# Campbell's question on the binary digits of `E`, answered

`jointWords_quantitative` with the single base `{2}` puts any binary word at `≥ N^{1−o(1)}`
positions below `N` in the digits of `E₂ = Σ 1/(2ⁿ − 1)`, hence infinitely often.  Route:
`erdosBorweinE = CastingOut.erdosBorweinAtBase 2` (reindex `n ↦ n + 1`, the `n = 0` term is `0`);
the counted predicate `⌊2^L · orbit 2 E n⌋ = v` is "the word with value `v` starts at digit `n`";
an unbounded count gives occurrences past every `N`.

Frozen statement (do not edit; prove it): `campbellEQuestion_holds`.
-/

namespace NormalNumbers.Literature.Campbell

/-- **Every binary string occurs infinitely often in the base-2 expansion of `E`**, answering
Campbell, arXiv:2605.24160, §4. -/
theorem campbellEQuestion_holds : CampbellEQuestion := by
  sorry

end NormalNumbers.Literature.Campbell
