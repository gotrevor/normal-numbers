# HANDOFF twopoint — SESSION WRAP 2 (laps 11–23), 2026-09-24

Branch `wip/twopoint-avg`.  HEAD: `f45edce`.  Working tree clean; every lap committed green
(pre-commit runs `lake build`).  All new declarations `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).

## What this run did

Continued `KICKOFF-2026-09-24-twopoint-bet.md` from the laps 1–10 wrap.  Laps 1–10 had proved the
Kátai/BSZ inequality (`katai_master`) and found that the repo's cited `KataiOrthogonalityAvg`
overstates the literature.  This run (a) removed the last cited hypothesis from the C1 chain,
(b) unfolded the surviving leaf into arithmetic, and (c) priced four attacks on it.

### The chain now
**`conjC1_of_delange_twoPointGram`** (`TwoPointGramArith.lean`): `ConjC1` from Delange's theorem
plus ONE arithmetic leaf.  The entire Kátai/BSZ step is a theorem, not a hypothesis.

The leaf, fully unfolded:
> ∃ `w(N) → ∞` with `w(N)² ≤ N`:
> `Σ_{p≠q≤w(N)} ‖Σ_{m ≤ min(⌊N/p⌋,⌊N/q⌋)} ζ^{ω(pm+1)} conj ζ^{ω(qm+1)} W_{p,q}(m)‖ = o(N·L(w N)²)`.

### New files (all in `src/`, imports added to `src/NormalNumbers.lean`)
| lap | file | content |
|---|---|---|
| 11 | `TwoPointGramChain.lean` | `katai_normalise`, **`katai_mean_sq`** (Kátai step in mean-square form, a THEOREM), `PairGramSmallGrowing`, **`conjC1_of_delange_pairGramSmall`** |
| 12 | `TwoPointGramArith.lean` | `csGram_kataiTrunc`, **`kataiPairGram_eq`**, `twoPointPairGramSmall_iff`, **`conjC1_of_delange_twoPointGram`** |
| 13 | `TwoPointGramBudget.lean` | `twoPointGramSum_le` (trivial bound), `maxRecipSum_ge`, **`tendsto_maxRecipSum_div_sq`** (`M(w)/L(w)² → ∞`) |
| 14 | `TwoPointGramMarkov.lean` | `card_badPairs_mul_le`, `card_badPairs_div_tendsto` |
| 15 | `TwoPointGramL2.lean` | `kataiPairGram_sq_le`, `kataiPairGram_le_of_l2`, `tendsto_l2_budget_ratio` |
| 16 | `TwoPointGramFrobenius.lean` | `sum4_comm`, **`gram_frobenius`** (fourth-moment identity), `kataiPairGramSq_eq` |
| 17 | `TwoPointGramDiag.lean` | `kataiCount`, `sum_kataiCount_sq`, **`kataiPairGramSq_split`** (exact) |
| 18 | `TwoPointGramForced.lean` | `maxRecipSum_le_two_card` (`M(w) ≤ 2π(w)`), **`fourthMoment_offDiag_ge`** (`≥ N²/8`) |
| 19 | `TwoPointGramSufficient.lean` | **`gramBudget_of_uniform_saving`** (per-pair saving `L(w)²/(2π(w))` suffices) |
| 20 | `TwoPointDeficit.lean` | **`sum_unimodular_deficit`** (`‖Σf‖² = |S|² − ½Σ‖f(m)−f(m')‖²`), `twoPointTruncSum_saving` |
| 21 | `TwoPointPairing.lean` | `norm_sum_le_of_rotation`, `twoPointTruncSum_pairing` |
| 22 | `TwoPointPairingRigidity.lean` | `pairing_shift`, **`no_elementary_pairing`** |
| 23 | `TwoPointBlockRotation.lean` | **`norm_sum_le_of_rotation_pointwise`**, `norm_one_add_lt_two`, `twoPointTruncSum_blockRotation` |

### Scoreboard on the leaf (all kernel-grounded)
| route | status |
|---|---|
| trivial per-pair estimates | insufficient by an unbounded factor (13) |
| `ℓ¹` averaging over multipliers | no gain — budget `L(w)²`, mass `M(w) ≫ L(w)²` (13) |
| `ℓ²` / fourth moment | demands exact evaluation of a `≥ N²/8` quantity to vanishing relative error (15–18) |
| rotation pairing with *constant* `z` | rigid: forces `σ = id` (22) |
| rotation pairing with *pointwise* gap | **OPEN AND LIVE** — reduces to a sieve statement (23) |

### Placement against the literature (laps 13–14)
The leaf is **not equivalent to fixed-pair natural-density two-point Elliott** in either
direction: per-pair decorrelation does not imply it (the budget is too small), and it does not
imply per-pair decorrelation (the inherited bound `o(N·L²)` is vacuous).  It is a dilation-average
statement — MRT-shaped, not Tao-2016-shaped.

### Corrections made in-run
- Lap 19 corrected laps 17–18's word "refuted": what is proved is that those are refuted *as
  estimation strategies*, not that no bound exists.
- Lap 23 corrected lap 21/22: the fixed-`z` constancy requirement was an artefact of the lemma
  statement; a pointwise gap suffices, so lap 22's rigidity is not an obstruction.

## Next session — start here

**Lap 24, the live thread.**  With `σ(m) = rm + k`, `r = pk+1` (`pairing_shift`), the pointwise
rotation is `Z(m) = ζ^{1 − Δ_q(m)}·(weight ratio)`, `Δ_q(m) = ω(r(qm+1)+(q−p)k) − ω(qm+1)`.
Two sub-bricks, in order:
1. **The weight ratio.**  Compute `peelWeight b p q t (σ m) / peelWeight b p q t m`
   (`PairDecoupleOneDigit.lean`: `peelWeight = phase (t/b · shiftPairTail b p q 1 1 ·)`).  It is
   the only non-`ω` piece; bounding it into an arc on a positive-density set gives the gap.
2. **`Δ_q` misses a residue.**  Weakest usable form: `∃ c > 0, α > 0` and a density-`α` set with
   `ω(r(qm+1)+(q−p)k) ≠ ω(qm+1) + 1`.  Cheap candidate: restrict to `m` with `r ∣ qm+1`
   (density `1/r`, nonempty since `gcd(r,q)=1`).

Then `twoPointTruncSum_blockRotation` + `gramBudget_of_uniform_saving` close the leaf.

**Rules honoured.**  `twoPointWeightedAvg_all` never deleted, renamed or weakened.  No edits to
`PairDecouple*.lean`, `SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`,
other KICKOFFs.  All new code in `src/NormalNumbers/TwoPoint*.lean`.  `src/` sorry count unchanged
from session start.

## Confidence at wrap
- `twoPointWeightedAvg_all` TRUE: **88%**.
- `twoPointGramSum` leaf TRUE: **80%**; provable with known techniques: **10%**.
- The pointwise-rotation route yields the per-pair saving: **30%**.
