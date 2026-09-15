# HANDOFF — lap 121: the **wide band**, and `tendsto_fullWRead_freq`

**Branch** `wip/g4-entropy`.  **HEAD** `bf4f230`.  Working tree **clean**.
`lake build` 🟢 **9012 jobs**.  No new `sorry`; the expedition's part of `src/` stays sorry-free.
`tendsto_fullWRead_freq` and `fullPosW_strictMono` print `[propext, Classical.choice, Quot.sound]`.

## The crux advance this lap

Lap 120 raised the band floor to `bandLoH i = 2·Xlo (KK i)`, which deleted the *uncertified*
head.  This lap diagnosed what that leaves and fixed it.

**The head-RATIO problem.**  At a cutoff `X'` just above the floor, the visited part of the
sample is a vanishing fraction of the certified truncation `PKtr i X'`, so the restriction price
is unpayable.  And it is **not** absorbable by the trivial bound: band `i`'s floor
`≈ Xlo (KK i) = 2^{50·2^{m_i}}` already contains `2^{48·2^{m_i}}` sample times, while band `i−1`,
topping out at `X (KK (i−1))`, contains only `2^{98·2^{m_{i−1}}}` — a tower fewer.  Lowering the
floor only moves the problem; the head is always a constant fraction of the band's own scale.

**The fix: widen the PREVIOUS band, don't lower the floor.**  `entropy_E1_tile` (lap 120)
certifies grid level `KK i` at *every* outer scale in `[Xlo (KK i), Xlo (KK (i+1))]`, so band `i`
may run to `wTop i := Xlo (KK (i+1))` instead of stopping at `X (KK i) = Xlo (KK i)²`.
Consecutive bands then span the **same** scale, and band `i+1`'s head measures against band `i`'s
*whole* read:

> ratio ≈ `8·gridDm_{i+1}·c_{i+1}/c_i ≈ 2^{2·2^{21·K²}} · 2^{−2·2^{m}}`, with `c_i =
> |Atom_i|·kk_i/P₀^{(i)}` — astronomically small, because `m ≥ K³ ≫ 21K²`.

The denser lower band drowns the sparser upper band's head.  This is the step the one-dimensional
ladder could not take and the `(K, j)` march makes free.

## What landed (all sorry-free)

### `G4EntropyBandWide.lean` (new)
| declaration | content |
|---|---|
| `deficit_primeLambertFour_wide` | E1 in `|Atom|` form at **every** scale of the tile |
| `wLo i = 4·Xlo (KK i)`, `wFloor i = gridDm·wLo i`, `wTop i = Xlo (KK (i+1))`, `wPosTop i = 2·wTop i + kk i` | the wide band's geometry |
| `Xlo_sq`, `eighteen_X_le_wTop`, `wgate_wTop` | the gate `4·wFloor + 4·P₀ ≤ X'` holds at the band's own top |
| `kk_lt_Xlo`, `wPosTop_le_wLo_succ` | the bands' POSITION ranges stay ordered — what the floor multiple `4` buys |
| `bandWtr`, `card_bandWtr_ge`, `bandWtr_nonempty` | the truncated wide band keeps half the truncated sample above the gate |
| `bandWLaw`, `H₂_bandWLaw_ge`, `abs_posAvg_bandWLaw_le` | `101√K` deficit and `2√(808 log2·ℓ/√K)` capture at every gated cutoff of the tile |
| `bandW`, `wLo_le_pos_of_mem_bandWtr`, `pos_lt_wPosTop`, `windows_eq_or_disjoint_at` | the band and its window geometry |
| `wTop_growth`, `card_PKtr_le`, `granuleW_exceeds_previous_scale` | the granularity wall at the tile tops |
| `P₀_le_sub_of_mem_at`, `window_gap_same_atom_at` | same-atom window gaps at a truncated scale |
| `card_collide_pair_le_at`, `card_multi_atom_le_at`, `card_multi_atom_le_real_at` | the collision chain, scale-generic (the wide band runs past `X (KK i)`, so the old statements do not apply) |

### `G4EntropyFullSeqW.lean` (new)
`G4EntropyFullSeq`'s whole construction re-run over `bandW`: `winStartsW`, `fnthW`, `fLW`,
`fTW`, `fgrpW`, **`fullPosW`** (strictly increasing), `fullDigW`, `matchesAt_fullDigW_iff`,
`fullGoodW`, `fullW_winCount_bounds`, the multiplicity bridge (`sum_pairsW_*`), the overhang
(`overhangW_*`), the band-dwarfs chain (`fLW_step`, `fTW_kk_le`), `pairCountW_eq`,
`tendsto_fTW_atTop`, the certified frequency (`bandWLawTop`, `posAvg_bandWLawTop_eq_*`,
`tendsto_bandW_occursCount`), and finally `bandWRatio`,
`abs_fullWRead_sub_bandWRatio_le`, **`tendsto_fullWRead_freq`**.

`read_freq_error_bound` is reused unchanged (it is pure real arithmetic).

## Next lap — in order

1. **Mid-band prefix control.**  This is now the only remaining gap, and the design above says it
   closes.  For a read index `a` inside band `i`, let `X'` be a cutoff separating the first `a`
   window starts from the rest (the `a`-th sample time, +1).  Two regimes:
   * **gated** (`4·wFloor i + 4·P₀ ≤ X'`): `abs_posAvg_bandWLaw_le i X'` applies **with no
     restriction price**, and `abs_fullWRead_sub_bandWRatio_le`'s argument runs verbatim with
     `bandWtr i X'` in place of `bandW i`.  Needed: the order-isomorphism between "first `a`
     window starts" and "sample times `< X'`" — `G4EntropyMultiplierSpread.kIdx_cross` is the
     per-atom bracket that makes one `X'` work for all atoms.
   * **ungated** (`X' < 4·wFloor i + 4·P₀ ≈ 16·gridDm_i·Xlo (KK i)`): bound the read trivially and
     absorb it into `fTW i`.  The lemma to prove is the head-fraction estimate
     `head_frac_tiny`: `(16·gridDm_i·Xlo (KK i)/P₀^{(i)})·|Atom_i|·kk_i ≤ ε_i · fTW i`, using
     `fLW (i−1) ≈ (wTop (i−1) = Xlo (KK i))·c_{i−1}` — i.e. exactly the ratio computed above.
     `wTop_growth` and `granuleW_exceeds_previous_scale` are the shape to imitate.
2. **`IsNormalSequence 2 (fullDigW …)`** from 1 + `tendsto_fullWRead_freq`, then
   `Bridge.isNormal_realOfDigits` → **`IsNormal 2 fullRealW`**.
   `properDigits_fullDigW` / `fullRealW` still need porting from `G4EntropyFullSeq`'s last
   section (lines 1251–1326); `exists_matchesAt_fullDigW` needs a wide non-vacuity witness.

## Deliberately not ported

`isSampled_fullPos`.  `IsSampled` is pinned to `sampledPos … (X (KK i))`, and the wide read
visits positions coming from sample times above `X (KK i)`.  It is a density remark (the read
skips almost every digit of `G₄`), not an input to normality.  To restore it, widen
`sampledPosAt` to `sampledPos (gridAt i) (wTop i) (kk i)`.

## Hygiene notes (new this lap)

* A **`Prop`-valued `def` for the gate** (`def WGate i X' : Prop := 4·wFloor i + 4·P₀ ≤ X'`) put a
  term whose `whnf` walks into `Xlo`'s tower into the local context of every downstream proof —
  and made even `positivity` on `0 ≤ 808·log 2·ℓ` diverge at **4M** heartbeats.  Write such gates
  out as plain inequalities.
* `attribute [local irreducible]` does **not** cross module boundaries.  `wLo`/`wFloor`/`wTop`/
  `wPosTop` are therefore **globally** irreducible (a global reducibility attribute may only be
  set in the defining module — which is why `Xlo`, defined in `G4EntropyE0Down`, stays `local`
  in `G4EntropyBandWide`).  Without this, every tactic in `G4EntropyFullSeqW` diverges.
* Marking a def irreducible kills its `rfl` equation lemmas: prove `wLo_eq`, `wFloor_eq`,
  `wTop_eq`, `wPosTop_eq` **before** the `attribute` line and use them downstream.
* `omega` will not identify `m (KK (i + 2))` with `m (KK (i + 1 + 1))` — they are distinct atoms.
  Spell the index one way throughout.

## Do not re-derive

`DIRECTION.md`'s CURRENT DIRECTIVE (review lap 119) still forbids re-litigating the scale gap.
`density_antitone` is withdrawn.  `fullReal`, `fullPos` and their theorems are untouched, per the
19:06 override.
