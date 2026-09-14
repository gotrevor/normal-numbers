# HANDOFF — entropy session wrap, laps 61–118, 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  **HEAD** `e2c00fe`.  Working tree **clean**.
`lake build` 🟢 **8995 jobs**.  Every new module sorry-free; no `axiom` introduced; no
pre-expedition G4/G5 file edited.  Every endpoint prints
`[propext, Classical.choice, Quot.sound]`.

## The session in three lines

1. **A wall**: normality is unreachable for *any* read of `G₄`'s sampled digits built from
   certified granules — and the wall does not depend on the entropy quality at all.
2. **A discovery**: `Q ∣ P₀`, so every two sampled windows coincide or are disjoint.
3. **A headline**: `G₄`'s digits along a **schedule-only, strictly increasing** position map
   carry every binary word at its correct frequency — the strongest form the wall permits.

## Part I — the wall (laps 61–63, 92)

```
G4EntropyGoodAtoms   card_good_ge, exists_good_coord(_deficit)
G4EntropyGranule     granule_exceeds_previous_scale
G4EntropyMixture     FinLaw.H₂_mix_le, H₂_empirical_window_restrict_ge,
                     certified_granule_exceeds_previous_scale, wall_at_zero_deficit
```
> Any sub-collection of scale `i+1`'s sample times whose derived capture bound is **not vacuous**
> already reads more digits than scale `i` produced in total — at **every** `δ ≥ 0`, including
> `δ = 0`.

Cause: `X(K) = 2^{100·2^{m(K)}}`, `m(K) ≥ K³` — the ladder's growth, not the estimate.  Subsumes
lap 54's `chunks_insufficient`, whose atom-count mechanism lap 61 showed was not the obstruction.

## Part II — the `G₄`-dependent band read (laps 64–91)

`G4EntropyAtomFreq`, `G4EntropyWindows`, `G4EntropyBand`, `G4EntropyBandFreq`,
`G4EntropyBandSeq`, `G4EntropyBandPrefix`:
`exists_good_atom`/`tendsto_goodAtom_occursCount` (one atom per scale suffices),
`window_gap_same_atom`, `band_gap`, `abs_posAvg_bandLaw_le`, **`bandPos_strictMono`**,
**`tendsto_bandRead_freq`**, `bandReal`, and the mid-band refinements
`tendsto_midRead_freq`, `abs_midRead_freq_sub_le(′)`, `tendsto_midRead_freq_of_depth`,
`abs_freq_sub_freq_mid`.

⚠️ Corrected mid-session (commit `36f46b2`): the good cutoffs are **not** a density-one set —
the bad initial portion of band `i` dwarfs every cutoff below it, so the bad set has lower
density `0` and **upper density `1`**.  That is the wall seen from the cutoff side.

## Part III — the schedule-only headline (laps 93–118)

**`Q ∣ P₀`** (`G4EntropyWindows.Q_dvd_freezeQ`, `Q_dvd_P₀`, lap 95): `shiftG_eq` makes two
different atoms' shifts congruent mod `Q` at the same layer, and `freezeQ` contains their
distance.  Hence `kIdx_congr_Q` and **`windows_eq_or_disjoint`**.

```
G4EntropyWindows   shared_idx_apart … card_Atom_sq_le_d, card_multi_atom_le_real
G4EntropyBand      bandT (an n-ONLY band threshold), card_bandT_ge'
G4EntropyBandFull  bandTLaw, H₂_bandTLaw_ge, abs_posAvg_bandTLaw_le,
                   tendsto_bandT_occursCount
G4EntropyFullSeq   winStarts, fnth, fL/fT/fgrp, **fullPos_strictMono**,
                   fullDig, the count bridge, pairCount_eq, overhang_frac_le,
                   G4Entropy.read_freq_error_bound, abs_fullRead_sub_bandRatio_le,
                   **tendsto_fullRead_freq**, fullReal, isDisjunctive_fullReal,
                   irrational_fullReal, isSampled_fullPos
```

> **`tendsto_fullRead_freq`** — for every finite binary word `v`,
> `winCount (fullDig G₄) v (fT (i+1)) / fT (i+1) → 2^{−|v|}`, with `fullPos` strictly monotone
> and defined from the **base-four schedule alone**.

Where it sits: lap 52 gave normality with a *non-injective* map; laps 56–60 a strictly increasing
map with only *disjunctivity*; laps 76–89 a strictly increasing map with correct frequencies but
*`G₄`-dependent*.  This is strictly increasing **and** schedule-only **and** frequency-correct.

## Next steps (for the next lap)

1. **Port the mid-band refinements to `fullPos`.**  Laps 84–89 (`abs_midRead_freq_sub_le`,
   `tendsto_midRead_freq_of_depth`, `abs_freq_sub_freq_mid`) are stated for `bandPos`; the same
   estimates hold for `fullPos` with the multiplicity term carried through
   (`overhang_frac_le` is already in the right form).
2. **The `fullReal` analogue of lap 90's density-zero non-vacuity** is `isSampled_fullPos`
   (done); what is left is stating it as a density statement about `fullPos` itself.
3. **Beyond the wall** is a *schedule* question, not an entropy one: `X(K)` is fixed by
   `G4ScheduleFar`'s far-tail control, and `wall_at_zero_deficit` shows the entropy side is
   exhausted.  Out of this expedition's read-only G4 footprint.

## Hygiene notes for the next session

* Several proofs needed `set … ; clear_value` or a fully abstract helper lemma
  (`read_freq_error_bound`) to keep the elaborator away from the astronomically large closed
  terms (`X`, `gridQ`, `P₀`).  Three assembly attempts died on `whnf`/`isDefEq` timeouts before
  the abstract-lemma design worked; prefer it from the start.
* `simp` on goals mentioning `gridDm`/`X`/`gridQ` can OOM the compiler (exit 137) — rewrite with
  explicit lemmas instead.
* Builds of `G4EntropyBand`/`G4EntropyFullSeq` take ~80–120 s; run `lake build` in the
  background and poll rather than inline.
