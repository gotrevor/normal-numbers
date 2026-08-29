# Handoff: lane-2 batch-2 target 3 DONE — β = 26 → 9, run stopping

**Date**: 2026-08-29 · **Branch**: master · **HEAD**: 3cc6327 · scoped run
(`sorry-free:src/NormalNumbers/LnTwoExpSepSharp.lean`), target met, `box done
--green` accepted.

## ✅ Result

`lnTwoExpSep_sharp : ∃ N₀, LnTwoExpSep 9 N₀` proved sorry-free in
`src/NormalNumbers/LnTwoExpSepSharp.lean`; `#print axioms` = `[propext,
Classical.choice, Quot.sound]`. Full `lake build` green (8787 jobs, pre-commit
verified twice). Landed modules untouched (ADDITIVE ONLY held).

Key content (details in the module docstring):
- height `Σ_k C(ℓ,k)C(ℓ+k,ℓ) ≤ 6^ℓ` via `C(ℓ+k,ℓ) ≤ 2^{ℓ+k}` + binomial —
  kills the `(ℓ+1)·8^ℓ` crude bound;
- kernel cap `y(1−y)/(1+y) ≤ 429/2500` on `[0,1]` (disc `−959 < 0`) — the
  decisive sharpening: ratio constraint `ℓ/n > 1.842` instead of `3.11`;
- lower bound `(1/50)(6/35)^ℓ` on `[2/5, 3/7]` (quadratic roots exactly at
  the endpoints); the `6^ℓ` height cancels, zero-case base exactly `35`;
- index `ℓ = 15n/8 + 1`; eventual inequalities in 8th-power form against the
  master limit `r^n·e^{16√(2n)log(2n)} → 0`; integer certificates
  `2⁸·429¹⁵ < 625¹⁵`, `24¹⁵ < 2⁷²`, `35¹⁵ < 2⁸⁰` (all `norm_num`).

`β = 8` is refuted for this method while only `lcm(1..ℓ) ≤ 4^ℓ` is known
(needs `c ≤ 1.75 < 1.842`); a PNT-strength `lcm ≤ e^{(1+ε)ℓ}` would give
`β ≈ 5` — recorded as the natural future sharpening.

## 🎬 Next (for a future lane-2 batch)

1. Discharge frozen node `PiSqBBP` (real-analytic proof of BBP Formula 29).
2. Optional: `lnTwoRun_le_sharp` corollary (9n run cap) wiring
   `lnTwoExpSep_sharp` into `run_le_of_expSep` — one-liner mirroring
   `lnTwoRun_le_unconditional`.
3. Optional: PNT-strength `lcmUpto` bound → β ≈ 5.

Brief v2 `## Progress` has the full target-3 entry.
