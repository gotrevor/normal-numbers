# HANDOFF — entropy lap 48 (the ℓ^∞ question, settled negatively), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8978 jobs**.  `src/` sorry-free.  No `axiom`.

## 0. The lap in one line

The strengthening the lap-47 handoff named as the open crux — a **pointwise (`ℓ^∞`)** `t`-wise
bound, valid at each *fixed* position vector rather than on average — is **refuted at the
abstract layer, with a witness meeting the exact premise**.

## 1. What was proved — `G4EntropyPointwise.lean` (new module)

```
lowBox A m                          the box ∏_α lowHalf m
mem_lowBox / card_lowBox / lowBox_nonempty
H₂_uniformOn_lowBox (1 ≤ m)         H₂ = |A|·(m − 1)          — deficit exactly |A|
posAt_one_zero_of_mem_lowHalf       a low-half block's leading bit is 0
exists_deficit_law_pointwise_zero   ∃ L,  m|A| − |A| ≤ H₂ L  ∧
                                      ∀ b, (L.map (pvPat m 1 t blk b 0)).prob {1…1} = 0
no_pointwise_bound_from_deficit     the same with any Δ ≥ |A|, stated as
                                      |prob − 2^{−t}| = 2^{−t}  (maximal deviation)
```

The witness is the uniform law on the box in which **every window's leading bit is forced to
`0`** and everything else is uniform.  Its entropy deficit is `|A|` bits — *one per window* —
which is far **less** than the schedule's `Δ = 50√K·|Atom|`, so the witness satisfies the exact
hypothesis of `abs_avg_patCoord_prob_opt`, `abs_avg_patPos_prob_opt`, `abs_uniPatFreq_sub_le`
and `abs_uniPosFreq_sub_le` with room to spare.  Yet at the fixed position vector `pv ≡ 0` the
all-ones pattern has probability `0` in **every** block simultaneously — the largest deviation
from `2^{−t}` there is.

## 2. Which bottleneck moved

This closes the question, not just narrows it.  The averaging over positions in the whole joint
ladder is **necessary**: no sharpening of the Hellinger/Pinsker estimates can produce an `o(1)`
bound at a fixed position vector, because the premise those theorems are proved from is
consistent with the maximal deviation there.  The ladder

| lap | positions | form |
|---|---|---|
| 38 | one common aligned position | `ℓ¹` |
| 41 | a fixed offset vector, aligned shifts | `ℓ¹` |
| 45 | all aligned vectors, averaged | `ℓ¹` |
| 47 | all vectors, averaged — no alignment | `ℓ¹` |
| 48 | **any fixed vector** | **impossible from the deficit premise** |

is therefore **complete**: lap 47 is the strongest statement of its kind that this arithmetic
supports, and lap 48 says why.

This is the `t`-wise, joint-law form of `entropy_rate_not_control_bit` (`G4EntropyControl`,
brief §5), which made the same point for one window and one bit.  §5's answer — "entropy
controls richness, not frequency" — now has its joint counterpart.

## 3. The next bounded test

Per trigger **E-T7** the next altitude lap owes a successor target.  With the joint ladder
complete and normality closed (lap 37/39), the honest candidates are:

1. **A genuinely different functional of the joint law.**  Everything so far reads *fixed-length
   pattern frequencies*.  The information-set lemma (`FinLaw.prob_infoSet_ge` /
   `card_infoSet_le`) controls the *support*, and nothing in the campaign has yet used it
   jointly: a `t`-wise richness statement ("the `t` sampled windows jointly take at least
   `2^{(1−δ/2)tm}` values on most of the mass") would be a new kind of endpoint, and it is
   **not** refuted by lap 48's witness (the box law has full richness in the remaining bits).
2. **Sharpen the constant** in the ladder — of no mathematical interest.
3. Close the campaign: brief §8's outcome has been satisfied since lap 31.

Candidate 1 is the only one that advances anything.

## Claim limits (unchanged)

Nothing here is a statement about the normality of `G₄`.  Lap 48's refutation is about the
abstract capacity premise; it does not assert that `G₄` itself has a determined sampled bit.
