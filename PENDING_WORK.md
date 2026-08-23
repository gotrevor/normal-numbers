# PENDING WORK — Stoneham campaign (2026-08-23, lap B)

**All 7 Stoneham sorries are discharged; `src/` is sorry-free.**
`Stoneham.lean` now proves `isNormal_two_stoneham23` end-to-end:
pinned hot-spot corollary (via `HotSpot` + Wall), state recursion/seed/
approximation, unit counting (`card_units_Ico`, exact floor formula),
`segment_visit_upper` (period-`2·3^(M-1)` blocks + injection into units of
an integer interval via `pow_injOn_Iio_orderOf`), and the final assembly:
window decomposition by `Nat.log 3`, per-window bound `2λℓ + 3λ·ord`
(`M0 = 2k+3` kills both the `2/3^(M+1)` approximation error and the
`+16`-per-window constant), telescoping length/period sums, constant
`C = 6`.

**⚠️ Sole remaining gate: the box still lacks the v4.33.1 toolchain**
(see ON-LINE-REQUEST.md), so `lake build` has never run on this state.
Everything is compiler-verified against v4.31 mathlib via the scratch
harness, including a WHOLE-FILE check of `Stoneham.lean` (imports stubbed
to axioms with verbatim repo statements).  When the toolchain lands:
1. `lake build` (expect at most small 4.31→4.33 lemma-name drift),
2. `#print axioms isNormal_two_stoneham23` — target: the standard 3
   (`propext`, `Classical.choice`, `Quot.sound`).
