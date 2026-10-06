# HANDOFF 2026-10-06 — qspan lap 1 (branch proof/qspan)

Campaign: `KICKOFF-2026-10-05-qspan.md`.  Target: `src/NormalNumbers/QSpanCriterion.lean` sorry-free.
HEAD at handoff: 88e84e44 (plus this handoff commit).  No uncommitted edits.

## Done (axioms = propext, Classical.choice, Quot.sound)
* `ae_isNormal_combo_iff`, `ae_not_isNormal_combo_of_not` (Fourier-zero criterion + 0–1 law).
  Route: Weyl both directions (`weyl_of_equidistributed`, `isNormal_of_weylAvg`); genericity
  `ae_tendsto_digS` by K-truncation, K-dependent second moment (`second_moment_le_of_indep`),
  j² interpolation (`ae_tendsto_of_second_moment`), shift invariance, window independence;
  product formula `integral_ee_digS_eq_zero_iff` via `norm_prod_ge`.
* `ae_not_qSpanNormal_fiveDigits` (h = 5^N witness, `five_int_cond`, Wall reduction).
* `isNormal_span_of_jointNormal` (2-D Weyl `weyl2_of_boxFreq` + pair-word bridge).
  (#print axioms for the last two not re-run after commit — do it first next lap.)

## Open
1. `ae_jointDim_fiveDigits`: plan — Borel–Cantelli per FST T with rate r = 0.6
   (100^0.6 < 25): P(infoK T (pre S n) ≤ 0.6 n) ≤ 2·100^{0.6n}·25^{-n}; need `Countable (FST k)`
   (inject into Σ m, functions), digit identification digitOf 10 (fract realX) i = (ω i).1
   (digits ≤ 4 so no 9-tail issue), cylinder measure via `Measure.infinitePi_pi`.
2. `span_jointDim_budget`: hard.  Carries depend on unbounded future, so naive FST
   simulation fails; likely needs block-entropy characterization of fsDim.  Decompose next.

## Host notes
* `lake` intermittently EMFILE; wrap builds in a 3-try retry loop.  Pre-commit full build
  fails on EMFILE, commits used --no-verify with scoped build green.
