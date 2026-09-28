# HANDOFF — review lap 122: the **mid-band prefix** sandwich, three modules in

**Branch** `wip/g4-entropy`.  **HEAD** `240ce17`.  Working tree **clean**.
`lake build` 🟢 **9015 jobs**.  `src/` carries exactly **two** `sorry`s, both pre-expedition and
off-path (`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_drift_one_background`);
the expedition's part of `src/` stays sorry-free.  Every new endpoint prints
`[propext, Classical.choice, Quot.sound]`.

## What this lap did

**Altitude pass first** (`1fb4a2f`).  Lap 119's four mandated steps are all DONE, so the
directive owed a successor.  `DIRECTION.md`'s **CURRENT DIRECTIVE** (set 2026-09-15, review lap
122) now names the single remaining obligation — **MID-BAND PREFIX CONTROL** — and its four
ordered items.  `STATUS.md` and `PENDING_WORK.md`'s ACTIVE section were refreshed against real
`#print axioms` output.  *Grind laps: read that directive, do not edit it.*

**The finding that sets the route.**  `IsNormalSequence 2` quantifies over *all* `n`.  The read
consumes band `i`'s distinct window starts **in increasing order**, so a read index cuts the band
at a **position** threshold `c`.  A start is `2·kIdx (gridAt i) n α` with
`d_α·kIdx(n,α) ≤ n < d_α·(kIdx(n,α)+1)`, so `2·kIdx(n,α) ≤ c` means `n ≲ c·d_α/2` — an
**atom-dependent** scale cut, *not* a truncated sample.  That is exactly why
`abs_posAvg_bandWLaw_le` does not apply verbatim to a mid-band prefix.  The fix: the grid's
multipliers agree to within `1 + 1/K` (`gridOf.mul_d_le_mul_d`), so the consumed set is bracketed
between two **honest** truncations, at a relative cost `O(1/K)` — negligible against the capture
error `2√(808 log 2·ℓ/√K) = O(K^{−1/4})` already carried.

## What landed (all sorry-free, trust triple)

### `G4EntropyWSandwich.lean` (new, `64d8360`)
| declaration | content |
|---|---|
| `refAtom`, `dRef`, `KK_mul_dRef_le`, `KK_mul_d_le` | the reference multiplier and the `1 + 1/K` spread |
| `cutLo i c = K·d_ref·c/(2(K+1))`, `cutHi i c = (K+1)·d_ref·(c+4)/(2K) + 1` | the two flanks |
| **`two_kIdx_le_of_lt_cutLo`** | below `cutLo`, EVERY atom's window is consumed |
| **`lt_cutHi_of_two_kIdx_le`** | a sample time consumed at SOME atom lies below `cutHi` |
| `cutLo_le_cutHi`, `flank_gap` | `cutHi ≤ cutLo·(1 + 3/K) + 4·d_ref + 5` (stated × `2K²`) |
| `card_bandWtr_add`, `card_bandWtr_{le,ge}_real` | `bandWtr i X' = PKtr i X' − PKtr i (wFloor i)`, so its count is `(X'−wFloor)/P₀ ± 2` |
| `KK_le_Xlo`, `KK_mul_P₀_le_Xlo`, `KK_mul_{P₀,dRef}_le_wFloor` | `P₀` and `d_ref` are both `≤ wFloor/K` |
| **`card_flank_ratio`** | `K·|bandWtr (cutHi i c)| ≤ (K+16)·|bandWtr (cutLo i c)|`, under the gate `8·wFloor i ≤ cutLo i c` |
| `bandWtr_cutLo_subset_bandW`, `mem_bandWtr_cutHi` | the inclusions on the band |

**Route trigger E-T11 did NOT fire**: the bracket exists, in-kernel.

### `G4EntropyWPrefix.lean` (new, `ef09f39`)
`fnthW_surj`, `fnthW_mono'`, `fnthW_le_iff`; `startsLe i c = (winStartsW i).filter (· ≤ c)`,
`aLe`, `idxLe`, `idxLe_eq_range` (a down-set of `range N` is a `range`), and the bridge

> **`startsLe_eq_image`** : `startsLe i c = image (fnthW i) (range (aLe i c))` — the starts a read
> index consumes are an **initial segment**, which joins the read-index view to the
> position-threshold view.

Then `fullGoodWPre`, `fullGoodWPre_eq`, and the prefix count bounds
`fullW_band_prefix_winCount_bounds` / `fullW_prefix_winCount_bounds`:
`fullGoodWPre i a x v ≤ winCount (fullDigW x) v (fTW i + a·kk i) ≤ fullGoodWPre i a x v + fTW i + a·|v|`.

### `G4EntropyWTrunc.lean` (new, `240ce17`)
The multiplicity bridge **generic in the pair collection**: `startsOf`, `sum_pairs_eq_gen`,
`card_startsOf_le`, `sum_pairs_sub_le_gen`, `overhang_gen_le` (`T ⊆ bandWPairs i` ⇒
`T.card − |startsOf i T| ≤ |badWPairs i|` — a window shared inside `T` is shared inside the whole
band), `overhang_gen_le_real`.  `card_badWPairs_le_real` was *extracted* from
`overhangW_le_real` in `G4EntropyFullSeqW` (statement unchanged) to carry it.

Then `pairsLe i c := (bandWPairs i).filter (2·kIdx · ≤ c)` with

```
startsOf_pairsLe            startsOf i (pairsLe i c) = startsLe i c
prod_cutLo_subset_pairsLe   bandWtr i (cutLo i c) ×ˢ univ ⊆ pairsLe i c   (needs cutLo ≤ wTop i)
pairsLe_subset_prod_cutHi   pairsLe i c ⊆ bandWtr i (cutHi i c) ×ˢ univ
```

Both flanks are **product** collections — the shape `abs_posAvg_bandWLaw_le` certifies — while
`pairsLe` itself is not.  That gap is the whole difficulty of mid-band control, and it is now
bridged.

## Next lap — in order

1. **The certified count at a truncated scale.**  `posAvg_bandWLawTop_eq_count` /
   `_eq_digits` in `G4EntropyFullSeqW` are proved for `bandWLawTop i = bandWLaw i (wTop i) _`, but
   their proofs are `X'`-generic in content (the only inputs are `bandWtr_nonempty hg` and the
   definition).  Restate them at a general gated `X' ≤ wTop i`, then package
   > `abs_occ_bandWtr_sub_le i X' v hg hhi` : `|(Σ_c |{n ∈ bandWtr i X' : OccursAt …}|)
   >   / (|bandWtr i X'|·|Atom|·(kk−ℓ+1)) − 2^{−ℓ}| ≤ 2√(808 log 2·ℓ/√K)`.
2. **The sum sandwich.**  `Σ_{bandWtr (cutLo) ×ˢ univ} ≤ Σ_{pairsLe i c} ≤ Σ_{bandWtr (cutHi) ×ˢ univ}`
   by `Finset.sum_le_sum_of_subset_of_nonneg` on the two inclusions, and
   `∑ z ∈ S ×ˢ univ, winOccW i x v (2·kIdx z.1 z.2) = ∑_{c : Atom × Fin (kk−ℓ+1)}
   |{n ∈ S : OccursAt … }|` by `Finset.sum_product` + swapping (mirror `pairCountW_eq`).
   Combine with 1 and `card_flank_ratio` to get the prefix ratio within
   `ε_i + O(1/K) + overhang/…` of `2^{−ℓ}`.  The arithmetic is written out in `PENDING_WORK.md`.
3. **`head_frac_tiny`** — cutoffs `c` with `cutLo i c` below the gate `8·wFloor i`: bound band `i`'s
   read trivially and absorb into `fTW i` via `fLW (i−1) ≥ |bandW (i−1)|·kk (i−1)` and
   `wTop (i−1) = Xlo (KK i)` (the `Xlo (KK i)` cancels).  Imitate
   `granuleW_exceeds_previous_scale`.
4. **The squeeze and the endpoint.**  `winCount` is monotone in `n`, so control at the cutoffs
   `fTW i + a·kk i` suffices (the partial window costs `kk i`, and `kk i / fTW i → 0` by
   `fTW_kk_le`).  Then `IsNormalSequence 2 (fullDigW …)`, `properDigits_fullDigW`, `fullRealW`,
   and `Bridge.isNormal_realOfDigits` → **`IsNormal 2 fullRealW`**.
   (`exists_matchesAt_fullDigW` still needs a wide non-vacuity witness.)

## Hygiene (carried + new)

* `wLo`/`wFloor`/`wTop`/`wPosTop` are **globally irreducible** — use `wLo_eq`/`wFloor_eq`/
  `wTop_eq`/`wPosTop_eq` (and the new `wFloor_eq'`), never `rfl` or `show`.
* `omega` cannot multiply two variables.  Chain `Nat.mul_le_mul_*` in a `calc` and finish with
  `Nat.lt_of_mul_lt_mul_left`; feed `omega` only statements whose nonlinear parts are single atoms.
* `Nat.div_add_mod` + `Nat.mod_lt` + `omega` is the reliable way to get both sides of a `Nat`
  division bound (used for `cutLo`/`cutHi`).
* For `linarith`/`nlinarith` on the flank arithmetic, supply the products as named `have`s
  (`(k−1)*L ≥ 0`, `(k−1)*k*a ≥ 0`, `(k−1)*(3k+1) ≥ 0`); nonlinear monomials are treated as atoms.
* `Finset.card_image_of_injOn` hands you membership in the **coercion** `↑s`; open with
  `simp only [Finset.mem_coe, …]`.
* `Finset.sum_image` wants its injectivity side-goal as a standalone `have` before the `rw`.

## Do not re-derive

`DIRECTION.md`'s CURRENT DIRECTIVE (review lap 122) forbids re-litigating the scale gap or the
head obstruction (retired by `entropy_E1_tile` and the wide band), lowering the band floor instead
of widening the band, and touching `fullReal`/`fullPos`/`bandT`.  `density_antitone` stays
withdrawn.
