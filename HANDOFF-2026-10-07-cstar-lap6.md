# HANDOFF 2026-10-07 — c⋆ lap 6 (Newhouse route: everything but the core)

Branch `proof/uniformbad-threshold`, HEAD `1f5ef849` + this file. Tree clean (untracked old probes
kreg_meet.js, mureg.js, psi.js left as found).

## Done (all axiom-clean, in `UniformBadNewhouse.lean`)
* `gap_lemma` (Newhouse) — linked-pair descent + `finite_long_gaps` + minimal pair.
* `e15_facts` (E15 ⊆ E₂(4), gaps = windows, τ = 3) and general `fset_facts`
  (Fset b c, τ = (b^c − b^{c−1} − 2)/2: F₃(4) = 26, F₂(3) = 1).
* `cStar_le_four_of_newhouse`, `cStar_le_of_newhouse` (any c ≥ 3), `cStarLeThree_of_newhouse`.
* `Scheme.limit_thick` / `gap_eq` / `limit_sub_G`: Cantor schemes are thick.
* `thickCore_of_splitCore`: crux reduced to `SplitCore c τ` (local adaptive splits, good endpoints).
* Probe `scripts/cstar_models/clus.js` (cluster ratio ≤ 2.5 numerically).

## Open crux
`thickCore_four : ThickCore 4 (2/5)` (sorry) ⇐ `SplitCore 4 τ`, τ > 1/3.

## Next
1. State the flipped route: A = Fset 3 4 (τ 26) vs B ⊆ E15 handling base 2 + b ≥ 5 with τ_B > 1/26
   (wiring like `cStar_le_of_newhouse`, B must also avoid b = 6,7,…; powers of 3 free via A).
   Small τ_B means kept pieces ~4% of gap: only 2-out-of-2 deaths propagate.
2. Attack the flipped SplitCore: adaptive split points chosen in E15 avoiding enlarged b ≥ 5
   windows; discard clusters, don't bound them (worst-case clusters exist heuristically).
3. Headline `cStar_le_four` in UniformBadThreshold.lean can't import Newhouse: when the core
   lands, move the headline proof (never weaken the statement).
Directive note: DIRECTION forbids "thickness theorems (Falconer–Yavicoli constants)"; read as
F–Y countable theorems, not this pairwise Newhouse route. Review lap should confirm.
