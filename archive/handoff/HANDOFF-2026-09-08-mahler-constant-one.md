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

## Lap 4: the `κ ≡ −8/3 (mod p)` law; `M(59,1) ≥ 840` beyond the census

The tuned top always satisfies `κ ≡ −8/3 (mod p)`; with `λ` tuned it is exact
at `59` too (`mahler_lower_bound_base59`, `840 = ⌊59/2⌋² − 1`), but the ratio
decays at most primes (`< 0.01` by `p ≈ 100`), so the `j = 2` burst family is
NOT uniformly quadratic.  General prime lower bound still open; see
`PENDING_WORK.md` §top for the two next attacks.

## Lap 5: period-2 backgrounds, `M(19,1) ≥ 80` exact

`MahlerLowerBoundPeriod2.lean` (new): `mahler_lower_bound_bg2_digit` runs the
existing single-digit certificate in base `g²` and transports it to base `g`
via `digitOf_pow_digitAt`; `mahler_lower_bound_base19` (`≥ 80`, census exact)
from background `1/10 = 1/(Q+1)`.  Prime table now exact at `5, 7, 13, 19, 23,
31`, one short at `11, 17`.  Working tree: only the three untracked HOST files.

## Lap 6: the escape engine is a theorem

`AdderEscapeCert.lean` (new, trust triple): `escape_mahler_lower_bound` — a
decidable automaton certificate (`Valid`) + `WitnessPair` ⟹ Mahler lower
bound, block never occurring.  Next brick is the `(7,2)` instance, see
`PENDING_WORK.md` §top.

## Next lap — `PENDING_WORK.md` §top

1. Prime-base LOWER side, general `p`: `M(p,1) ≥ p²/4 − O(p)` from the
   census witnesses (`a ≠ 0` background family) — the missing half of the
   DIRECTIVE's crux now that the upper side is at `1/4`.
2. Else the escape engine (`AdderEscape.lean`, tail intervals → carry
   soundness → `M(7,2) ≥ 176`).
