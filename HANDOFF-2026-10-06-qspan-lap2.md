# HANDOFF 2026-10-06 — qspan lap 2 (branch proof/qspan) — CAMPAIGN DONE

Target `src/NormalNumbers/QSpanCriterion.lean` is sorry-free.  `#print axioms` on all six frozen
headlines (`span_jointDim_budget`, `isNormal_span_of_jointNormal`, `ae_isNormal_combo_iff`,
`ae_not_isNormal_combo_of_not`, `ae_not_qSpanNormal_fiveDigits`, `ae_jointDim_fiveDigits`):
propext, Classical.choice, Quot.sound.  Statements byte-identical to 4d1b1636.

## This lap
* `ae_jointDim_fiveDigits`: Borel–Cantelli per FST (`shortEv_le`: P(desc < 3n/5) ≤ n(2/3)^n),
  `countable_FST`, digit identification `digitPair_five`.
* `span_jointDim_budget` WITHOUT the Doty–Moser block-entropy characterization: Wall reduction to
  integer `(a,c)`; `run_chunks` (FST output = ≤|π|/L+1 chunks); `window_combo` (z-window =
  combination of x/y windows mod bᵗ up to carry |k| ≤ |a|+|c|); `normal_thin_cover` (normal
  sequence: windows in dictionaries V t cover ≤ δn); `zDict`/`card_zDict` dictionary;
  `core_bound` (∀ r ≥ 4, eventually every description has length ≥ (r−2)n/(2r)), L = rL' with
  L' from `exists_cube_lt_four_pow`.
* Note `span_jointDim_budget` holds for ANY integer (a,c), including (0,0) (then z = 0 is not
  normal, vacuous).

## Not done (out of scope, designated open)
* `QSpan.span_dimension_budget` (QSpanNormal.lean) still needs the subadditivity leaf
  (joint lower dim ≤ lower dim x + upper dim y).  The chunk machinery here is reusable for it.
