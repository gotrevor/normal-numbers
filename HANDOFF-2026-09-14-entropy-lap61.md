# HANDOFF — entropy lap 61, 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8985 jobs**.  New module
`src/NormalNumbers/G4EntropyGoodAtoms.lean`, sorry-free, all endpoints
`[propext, Classical.choice, Quot.sound]`.

## What was proved

**The affirmative dual of `chunks_insufficient`: most single coordinates are individually good.**

```
FinLaw.coordDeficit L α          m − H₂(the law of the window at the single atom α)
FinLaw.coordDeficit_nonneg       each coordinate carries at most m bits
FinLaw.sum_coordDeficit_le       Σ_α coordDeficit ≤ δ·|A|            (subadditivity)
FinLaw.badCoords L δ'            {α : coordDeficit L α > δ'}
FinLaw.card_badCoords_le         |badCoords δ'|·δ' ≤ δ·|A|            (Markov)
soloLaw / H₂_soloLaw             one coordinate, presented as a one-element family
coordAvg m ℓ L α w               that ONE window's ℓ-word frequency, over all its positions
abs_coordAvg_sub_le              coordDeficit ≤ δ' ⟹ |coordAvg − 2^{−ℓ}| ≤ 2√(log2·ℓδ'/(m−ℓ+1))
card_good_ge                     ≥ (1−ρ)|A| atoms are good ONE AT A TIME, at price √(δ/ρ)
Sched.card_goodAtoms_ge          the scale-i instance, any x supplying a deficit
Sched.deficit_primeLambertFour   entropy_E1 in per-window shape, δ = 50√K
Sched.card_goodAtoms_primeLambertFour_ge   the G₄ instance
```

## Why this is the crux move, not scaffolding

Lap 54 (`chunks_insufficient`) refuted the route that splits a scale into *arbitrary* chunks:
an arbitrary sub-collection of relative size `ρ` costs `√(1/ρ)` and there are never enough
certifiable chunks.  Everything since has been blocked by the same shape — the enumeration
`sampleEnum` reads, at any cutoff `L`, an uncontrolled *prefix* of each active scale's window
collection, and a prefix is an arbitrary sub-collection.

`card_good_ge` breaks the symmetry: the deficit does not only control the average over
coordinates, it forces all but a `ρ`-fraction of the coordinates to be good **on their own**.
So a selection route no longer needs a certified chunking — it needs only to read the windows
of the good atoms, and the good set is explicit (`(badCoords L (δ/ρ))ᶜ`).

This is consistent with `no_pointwise_bound_from_deficit` (lap 48): that rules out a bound at a
*fixed position inside* a window; here every position of the window is still averaged, only the
atom is pinned.

## Where it does and does not go

* It does **not** by itself give normality of `realOfDigits 2 enumDigits`: the good set depends
  on `x = G₄` (it is defined by `G₄`'s own entropy deficit), so a position map built from it is
  explicit but no longer *schedule-only*, and the good atoms' windows at one scale still have to
  dominate the prefix of everything below.
* It is the missing ingredient for any **selection** route: pick, at each scale, the good atoms
  and read only their windows.

## Next bounded tests

1. `posAvg m ℓ L w = (1/|A|)·Σ_α coordAvg m ℓ L α w` — the consistency bridge showing
   `coordAvg` refines the repo's already-controlled `posAvg`.  (Started; the two-step
   pushforward collapses by `prob_singleton_map_map`.)
2. Are the good atoms' windows *geometrically* usable: for a fixed atom `α`, the sampled
   positions `2·kIdx(n,α)+p` over `n ∈ P_K` with consecutive `kIdx` **overlap** (shift 2,
   length `m = 40000+i`), so one atom's sampled set is essentially one long interval of `G₄`'s
   digits.  If so, `coordAvg` is exactly the word frequency in that interval, and the
   enumeration restricted to good atoms reads a concatenation of *individually good* blocks —
   the classical input to a normality proof.
