# HANDOFF — entropy grind lap 36 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  `lake build` green, **8970 jobs**.  `G4EntropyOffset.lean`
sorry-free, `#print axioms` clean.  No pre-expedition file edited.

## The result: every position, not one tiling

```
abs_posAvg_sub_le    (0 < ℓ ≤ m, per-coordinate deficit δ)
  | posAvg m ℓ L w − 2^{−ℓ} |  ≤  2 √(log 2 · ℓ δ / (m − ℓ + 1))

posAvg m ℓ L w = avg over (α, p) with p < m − ℓ + 1 of Pr[ the ℓ-block at position p = w ]
```

Laps 29–32 controlled `w` among the `⌊m/ℓ⌋` blocks of **one** aligned tiling.  This controls it
at **every** one of the `m − ℓ + 1` positions of the window, averaged — the quantity normality
is actually built from — with the *same* bound to within `1 + o(1)`.  Nothing is lost:
the `m` in the denominator becomes `m − ℓ + 1`.

## How

1. `H₂_lowTuple_ge` (lap 35): dropping the top `r` bits costs `≤ |A|·r` bits, and the maximum
   drops by exactly `|A|·r`, so the truncated law has the **same** deficit on `m − r` bits.
2. `abs_avg_block_prob_offset_le` (lap 35): hence the aligned tiling of the truncated window —
   which is the offset-`r` tiling of the original — obeys the capacity bound with `m ↦ m − r`.
3. `fullCoord_lowTuple_eq` (this lap): the offset-`r` block `j` of the truncated window *is*
   the position-`(r + jℓ)` block of the original (`mod_div_mod_eq`: truncating below the block
   of interest changes nothing).
4. `posEquiv` (this lap): `(r, j) ↦ r + jℓ` is a **bijection** from `{r < ℓ, j < (m−r)/ℓ}` onto
   `{p : p + ℓ ≤ m}` (inverse `p ↦ (p % ℓ, p / ℓ)`), so the offset classes tile the positions
   exactly — each position counted once.
5. `sum_offset_eq_sum_pos` + a weighted-average step (offset classes with no full block have
   both sum and count zero, so they are harmless): `|∑_r S_r − c ∑_r N_r| ≤ B ∑_r N_r`, and
   `∑_r N_r = |A|(m − ℓ + 1)` follows from the same bijection with `f ≡ 1`.

Supporting: `FinLaw.prob_singleton_map_map` (two-step pushforwards collapse on singletons —
needed because the offset statement is about `(L.map lowTuple).map fullCoord` while the position
statement is about `L.map posAt`).

## Next bounded test

Render `abs_posAvg_sub_le` at the schedule, mirroring `G4EntropyTiling`'s last three theorems:

1. `posFreq i ℓ x w := posAvg (kk i) ℓ (jointLawAt i x) w`, then
   `abs_posFreq_sub_le_of_deficit` and the `E0`/`entropy_E1` instances — mechanical, the
   deficit hypothesis is verbatim the one `abs_blockFreqT_sub_le_of_deficit` takes.
2. The digit rendering: `posAt (kk i) ℓ p (Z^x_i α)` is the `ℓ` binary digits of `x` at
   positions `2·kIdx + p …`, which is `G4EntropyRender.blkAt_blockVal_min` with `j ↦ p`
   (that lemma is stated for `blkAt m ℓ j`, i.e. `posAt m ℓ (jℓ)`; the general-`p` version is
   the same proof with `(j+1)*ℓ` replaced by `p + ℓ`).
3. Then `tendsto_occursCountP_primeLambertFour`: **every** finite binary word occurs with
   frequency `2^{−|w|}` among *all* positions of the sampled windows of `G₄` — strictly
   stronger than lap 31's aligned version and the exact statement `isDisjunctive_two` uses.
