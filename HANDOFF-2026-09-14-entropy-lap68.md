# HANDOFF — entropy laps 66–68, 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8989 jobs**.  Sorry-free, every endpoint
`[propext, Classical.choice, Quot.sound]`.

## The single-atom line

Laps 61–63 closed the certified-granule route to normality.  Laps 66–68 build what the closure
leaves standing: **the frequency theorem no longer needs the average over atoms.**

```
G4EntropyGoodAtoms.lean
  exists_good_coord (lap 66)   one coordinate outside badCoords carries the capture bound for
                               EVERY word of EVERY length — coordDeficit mentions neither

G4EntropyAtomFreq.lean (laps 67–68)
  coordAvg_eq_count            coordAvg = the (n,p)-density at a FIXED atom
  coordAvg_eq_digits           …in G₄'s binary digits at 2·kIdx(n,α)+p
  atomDeficit i = 100√K        entropy_E1's 50√K at ρ = 1/2
  exists_good_atom             at every scale, ONE atom good for every word of every length
  goodAtom i                   that atom, chosen before any word is named
  abs_coordAvg_goodAtom_le     |coordAvg − 2^{−ℓ}| ≤ 2√(800 log2·ℓ/√K)
  tendsto_goodAtom_occursCount **the endpoint**
```

> For every finite binary word `v`,
> `#{(n,p) : OccursAt 2 G₄ v (2·kIdx(n, goodAtom i) + p)} / (|P_K|·(m_K−|v|+1)) → 2^{−|v|}`.

`tendsto_occursCountP_primeLambertFour` is this statement averaged over all `|Atom_K| =
(K²+1)^K` atoms.  Here the atom is a single one, fixed per scale, chosen with no reference to
the word.

## Why the pair (66–68) + (65) matters

`window_gap_same_atom` (lap 65): at a fixed atom the windows are **pairwise disjoint**, with a
margin of a full window length.  So `goodAtom i`'s window family is simultaneously

* **certified** — its own statistics obey the capture bound without averaging, and
* **geometrically clean** — reading it in position order is literally the concatenation of its
  window contents, with no multiplicity bookkeeping.

That is exactly the input a subsequence construction consumes, and it is now available at every
scale.  What it still cannot do is cross scales: `certified_granule_exceeds_previous_scale`
(lap 63) says the first certified granule of scale `i+1` outweighs everything before it.

## Next bounded tests

1. **Band the good atom.**  Read `goodAtom i`'s windows only in `[2X(K_{i−1}), 2X(K_i))` — a
   sample-time restriction of relative size `≈ 1`, so still certified (lap 63's cost formula
   with `σ ≈ 1`).  The bands are then ordered, and the read sequence is a concatenation of
   disjoint, individually certified blocks.
2. **The cutoff subsequence.**  At the end of band `i` the accumulated content is band `i`
   (certified) plus a negligible history, so the prefix frequency at those cutoffs → `2^{−ℓ}`.
   Endpoint: *a strictly increasing position map along which `G₄`'s digits have the correct word
   frequencies along a subsequence of prefix lengths* — the strongest statement lap 63 permits,
   and strictly between `isDisjunctive_enumReal` (laps 56–60) and
   `isNormal_realOfDigits_samplePos` (lap 52, non-injective map).
