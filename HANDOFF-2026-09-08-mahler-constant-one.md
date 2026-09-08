# HANDOFF 2026-09-08 — the universal Mahler constant is `1`, in Lean 🧮

**Branch** `wip/adder-tower-c9` · **Build** 🟢 green (8875 jobs) · trust triple on
all headlines.  Three untracked HOST files (`docs/mahler-universal-constant-is-one-2026-09-07.md`,
`experiments/mahler_delta_star*.py`) are not mine — leave them.

## Done this lap

`MahlerLowerBoundSmooth.lean` (new):
- `mahler_lower_bound_smooth`: `t ∣ g^j`, `t < g` ⟹ `M(g,k) ≥ t(gᵏ−1)`.
  Lifts the divisor bound (`j = 1`) to every `g`-smooth `t < g`.
- `mahler_lower_bound_630` (`≥ 393125 = 0.9905·630²`),
  `mahler_lower_bound_26250` (`≥ 688878756 = 0.99973·26250²`).
- `mahler_constant_one_sharp`: ∀ `k ≥ 1`, `ε > 0`, `L`, ∃ `g ≥ L` with
  `M(g,k) ≥ (1−ε)g^(k+1)`.  Dirichlet on `log 3/log 2`.  With
  `mahler_multiplier_lt`: `sup_g M(g,k)/g^(k+1) = 1`, not attained.

The kickoff's `g^(k+1)/4` objective: `k = 1` done last run (`MahlerQuarter`),
`k ≥ 2` refuted by exact `M(7,2) = 176` (see `PENDING_WORK.md`).  The host's
2026-09-07 doc closed the universal-constant question numerically; this lap
put it in the kernel.

## Lap 3 (same run): prime lower side dissected

`MahlerPrimeLowerBound.lean` gains `M(17,1) ≥ 63`, `M(31,1) ≥ 224` (exact).
All census bursts are `B = p^j κ − 4 S_j`; the last digit is `2(u − r)`, the
middle digits `p − 2r − 1`, and only the top `κ` is prime-specific — there is
no uniform `κ` (fails at `p = 19, 29` for every `κ < p²`).  Full analysis,
refuted sub-approaches and the two next attacks are in `PENDING_WORK.md` §top.

## Next lap — `PENDING_WORK.md` §top

1. Prime-base LOWER side, general `p`: `M(p,1) ≥ p²/4 − O(p)` from the
   census witnesses (`a ≠ 0` background family) — the missing half of the
   DIRECTIVE's crux now that the upper side is at `1/4`.
2. Else the escape engine (`AdderEscape.lean`, tail intervals → carry
   soundness → `M(7,2) ≥ 176`).
