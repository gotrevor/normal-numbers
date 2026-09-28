# HANDOFF c3-mrt 2026-09-25 lap83 — `UniformResonantMass` is a THEOREM

**Read first:** `DIRECTION.md` → CURRENT DIRECTIVE (OUTRANKS this file).
Branch `wip/c3-mrt`.  New tip: `NormalNumbers.C3MrtUniformMass`.

## BUILD HYGIENE

    lake build                                   # 9257 jobs (root)
    lake build NormalNumbers.C3MrtUniformMass    # THE TIP

Chain: `… → C3MrtNoExc → C3MrtTTPretentious → C3MrtWindowMass → C3MrtUniformMass`.

## What laps 81–83 did

**The lap-80 NEXT list is COMPLETE.**  `uniformResonantMass_holds : UniformResonantMass`
is proved and `#print axioms` clean.  The one named analytic input of the archimedean
certificate is gone.

Three stages, all in `C3MrtUniformMass.lean`:

1. **`sharp_window_mass_le`** (lap 81) — one resonance window, cut into HALF-unit blocks
   `j = ⌊2 log p⌋`.  Half-units (not unit) because `interval_mass_le` wants a STRICT lower
   endpoint: `a₀ = max(a, j/2 − 1/2)` and length `min(L,1)` then fit any fibre.  Bound
   `32L/a + 7·10⁶ exp(−a/16)exp(−A/16)`; `j₀ ≥ 2max(a,A) − 1 ≥ a + A − 1` splits the decay
   between the window height (summed over `m`) and the cutoff (killing `|t|`).
2. **`resonant_big_mass_le`** (lap 82) — fibre by `windowIndexW` over `Icc (−K) K`, then
   `sum_Icc_symm_le` + `sum_inv_gap_le` (main, `64δ/(γ_m − δ)`) and `sum_exp_neg_le` at
   `c = π/(32|t|)` (error).  The `m = 0` window is handled by `γ_0 − δ ≥ δ`, and
   `γ_m − δ ≥ (π/2)|m|` needs `m`'s INTEGRALITY (`|m| = 0 ∨ |m| ≥ 1`).
3. **`uniformResonantMass_holds`** (lap 83) — cutoff `A = 16 log(2·10⁸(2+|t|))` makes the
   Brun–Titchmarsh error `≤ 1`; `log K ≤ log 8 + log(2+|t|) + log log Y`; the primes below
   the cutoff cost `log(A+1) + mertensBound`, absorbed by `log_le_mul_sub` at slope `7δ/8`.
   Budget: `128·(2/3) = 85.34` (using only `π > 3`) `+ 14 = 99.34 < 100`.  `t = 0` is
   separate (`resonantMass_zero`: nothing resonates, `|arg z| ≥ 2δ`).

**Unconditional corollaries** (same file): `ttNonPretentious_zOmegaNat`,
`logToNaturalCorrelationNZ_two_of_noExc'`, and **`depthAvg_two_tendsto_of_noExc`** — the
`D = 2` natural-density depth rung from `TwoPointNaturalCorrelationNoExc` and
`ProgressionLogRung 2` ALONE.

### Lean friction worth remembering
* `linarith`/`nlinarith`/`norm_cast` preprocess the WHOLE context: once a hypothesis carrying
  a large `Finset.filter` sum is in scope they blow the heartbeat budget.  Prove every numeric
  side fact BEFORE introducing such hypotheses, and finish with term proofs.
* `set x := e with h` keeps the body; `clear_value` after the definitional facts are proved is
  what stops `positivity`/`isDefEq` from unfolding `⌈exp A⌉₊` etc.
* `set_option maxHeartbeats` goes BEFORE the docstring, not between docstring and `theorem`.

## NEXT

1. `TwoPointNaturalCorrelationNoExc` is now the SOLE named open input of the `D = 2` layer
   (besides `ProgressionLogRung 2`).  Re-audit `STATUS.md` / the audit surface to say so.
2. Then the generational `K ≥ 3` item.

## Still refuted — DO NOT RETRY

Everything in lap 80's list, unchanged.
