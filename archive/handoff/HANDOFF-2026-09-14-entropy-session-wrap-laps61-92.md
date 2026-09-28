# HANDOFF — entropy session wrap, laps 61–92, 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  Working tree clean.  `lake build` 🟢 **8993 jobs**.
Every new module sorry-free; no `axiom` introduced; no pre-expedition G4/G5 file edited.
Every endpoint below prints `[propext, Classical.choice, Quot.sound]`.

## The session in two lines

Laps 61–63 **proved a wall** that closes normality for every read of `G₄`'s sampled digits
built from certified granules — and lap 92 shows the wall does not depend on the entropy
quality at all.  Laps 64–92 then **built the strongest object the wall leaves standing** and
proved it correct: a strictly increasing, schedule-and-good-atom-defined position map along
which every binary word has its correct frequency at every cutoff except an initial, relatively
vanishing, portion of each scale band.

## Part I — the wall

| declaration | content |
|---|---|
| `G4EntropyGoodAtoms.card_good_ge` | ≥ (1−ρ)\|A\| atoms are good **one at a time** (Markov on per-coordinate deficits) |
| `G4EntropyGoodAtoms.exists_good_coord(_deficit)` | one coordinate good for **every** word of **every** length |
| `G4EntropyGranule.granule_exceeds_previous_scale` | `\|Atom_i\|·\|P_i\|·m_i < \|P_{i+1}\|` |
| `G4EntropyMixture.FinLaw.H₂_mix_le` | `H₂(mix) ≤ σH₁+(1−σ)H₂+1` (the bit is `Real.binEntropy σ`) |
| `G4EntropyMixture.H₂_empirical_window_restrict_ge` | restricting the **sample times** costs `(δ+1)/σ` |
| `G4EntropyMixture.certified_granule_exceeds_previous_scale` | **the wall** |
| `G4EntropyMixture.wall_at_zero_deficit` | …and it holds at `δ = 0` |

> Any sub-collection `S` of scale `i+1`'s sample times whose derived capture bound is **not
> vacuous** satisfies `|Atom_i|·|P_{K_i}|·m_i < |S|·m_{i+1}`.

Reading: the smallest granule the capture inequality can certify at scale `i+1` already contains
more digits than scale `i` produced in total, so the history is wiped out at every new scale and
prefix frequencies cannot converge.  Lap 54's `chunks_insufficient` used the atom count; that was
not the obstruction (lap 61 shrinks the granule to one atom).  The obstruction is
`X(K) = 2^{100·2^{m(K)}}` with `m(K) ≥ K³`.

## Part II — the band read

| declaration | content |
|---|---|
| `G4EntropyAtomFreq.exists_good_atom`, `goodAtom`, `tendsto_goodAtom_occursCount` | **one** atom per scale carries every word at its correct density |
| `G4EntropyWindows.window_gap_same_atom` | at a fixed atom the windows are pairwise disjoint, with a full window's margin |
| `G4EntropyBand.band_gap(_strong)`, `bandS`, `card_bandS_ge'` | ordered bands; dropping the windows below the previous ceiling costs ≤ half the sample |
| `G4EntropyBandFreq.abs_posAvg_bandLaw_le`, `tendsto_band_occursCount` | the band restriction keeps the certification (`σ ≥ ½` costs a factor 2) |
| `G4EntropyBandSeq.bandPos_strictMono` | **a genuine subsequence of `G₄`'s digit positions** |
| `G4EntropyBandSeq.tendsto_bandRead_freq` | **the headline**: `winCount (bandDig G₄) v (bT (i+1)) / bT (i+1) → 2^{−\|v\|}` |
| `G4EntropyBandSeq.bandReal`, `isDisjunctive_bandReal`, `irrational_bandReal`, `isSampled_bandPos` | the real, and its non-vacuity (density-zero positions) |
| `G4EntropyBandPrefix.tendsto_midRead_freq`, `abs_midRead_freq_sub_le(′)`, `tendsto_midRead_freq_of_depth`, `abs_freq_sub_freq_mid` | the same limit at **every** cutoff beyond a vanishing fraction of each band |

Where this sits: the repo had *either* normality along a **non-injective** position map
(`isNormal_realOfDigits_samplePos`, lap 52) *or* a strictly increasing map carrying only
**disjunctivity** (`isDisjunctive_enumReal`, laps 56–60).  This is strictly between them.

## ⚠️ One overclaim caught and corrected (commit `36f46b2`)

The good cutoffs are **not** a density-one set, and the docstrings no longer say so.  The bad
initial portion of band `i` has length `≈ θ_i·m_i` while everything before band `i` has length
`bT i ≤ 4|bandS i|`, which is far smaller — so at a cutoff sitting inside the bad portion, the
bad cutoffs below it are *most* of them.  The bad set has lower density `0`, upper density `1`.
That is the wall seen from the cutoff side, and exactly why this is not normality.

## Claim limits

Nothing in laps 61–92 is a statement about the normality of `G₄` itself, which stays closed on
this mechanism (lap 37).  `bandReal` is built *from* `G₄`'s digits along a density-zero set of
positions and is not `G₄`.  `bandPos` is defined from the schedule **and** the per-scale choice
of a good atom, which depends on `G₄`'s own entropy data — it is explicit but, unlike lap 52's
`samplePos`, not schedule-only.

## Next bounded tests

1. **x-freeness.**  Can the good atom be replaced by a schedule-only choice?  Reading *all*
   atoms' windows in a band is schedule-only but loses disjointness: a greedy disjoint subfamily
   is schedule-only too, and is certified iff the discarded fraction is small — so the question
   reduces to bounding **cross-atom collisions** `|2·kIdx(n,α) − 2·kIdx(n',β)| < m_K`.  A first
   estimate (in-session, not formalized) suggests collisions are *not* rare, because the
   colliding pairs sit on the lines `u·d_β − u'·d_α = D` with `|D| ≲ d_α d_β`; worth a probe.
2. **The schedule, not the estimate.**  `wall_at_zero_deficit` says the entropy side is
   exhausted.  The only way past is a ladder with `X(K)` growing polynomially rather than as
   `2^{2^{K³}}`; `X` is fixed by `G4ScheduleFar`'s far-tail control, so this is a question about
   the *schedule*, and is outside this expedition's read-only G4 footprint.
