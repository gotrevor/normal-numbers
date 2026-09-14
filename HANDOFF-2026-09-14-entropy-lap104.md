# HANDOFF — entropy laps 93–104, 2026-09-14, Opus — the x-free upgrade, mid-flight

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8994 jobs**.  Sorry-free; every endpoint
`[propext, Classical.choice, Quot.sound]`.

## The discovery (laps 93–95)

**`Q ∣ P₀`** — `G4EntropyWindows.Q_dvd_freezeQ`, `Q_dvd_P₀`.

`shiftG_eq` gives `ρ_{α,j} = j + Q·(…)`, so two *different* atoms at the *same* layer have
shifts congruent mod `Q`; `freezeQ` contains their distance as a factor; hence `Q ∣ freezeQ ∣ P₀`.

Consequences: every sample time is congruent mod `Q`, hence **all** orbit indices of **all**
atoms at **all** sample times are congruent mod `Q` (`kIdx_congr_Q`), and `Q = (U+K+N+2)!`
dwarfs `m_K`, so

> **`windows_eq_or_disjoint`** — every two sampled windows coincide or are disjoint.

That removes the obstruction to a **schedule-only** (x-free) band read: the sampled position set
is a disjoint union of windows.

## The multiplicity toolkit (laps 96–101)

Reading the position *set* counts each window once, while the entropy statistic counts each
`(n,α)` pair once; the gap is the window multiplicity.

```
ActiveIdx, shared_idx_apart   two atoms' shared indices are P₀ apart (P₀ ∣ d_α g, P₀ ∣ d_β g,
                              coprime_d ⟹ P₀ ∣ g)
card_shared_le                ≤ M/P₀ + 1 below M
card_collide_pair_le          per atom pair: ≤ (X/d_α + 1)/P₀ + 1
card_multi_atom_le            per atom: ≤ |Atom|·that
card_Atom_sq_le_d             |Atom|² ≤ d_α   (B ≥ (K²+1)², gridUmax ≥ B^K, ≤ Q ≤ d)
card_multi_atom_le_real       collision fraction ≤ 2/|Atom| + 2|Atom|/|P_K| → 0
```

## The x-free certification (laps 102–104)

```
G4EntropyBand.bandT i         {n ∈ P_K : gridDm·bandLo i ≤ n} — an n-ONLY threshold, so the
                              band restriction is a pure sample-time restriction
bandLo_le_pos_of_mem_bandT    …and it puts EVERY atom's window above the floor
bandT_zero, bandT_nonempty, card_bandT_ge'      still at least half the sample

G4EntropyBandFull.bandTLaw    the joint law restricted to bandT
H₂_vector_le                  the m·|A|-bit ceiling for window vectors
H₂_bandTLaw_ge                per-window deficit 50√K → 101√K  (σ ≥ ½: factor 2 plus one bit)
abs_posAvg_bandTLaw_le        |freq − 2^{−ℓ}| ≤ 2√(808 log2·ℓ/√K)
posAvg_bandTLaw_eq_count/_digits
tendsto_bandT_occursCount     **the limit, with no good atom anywhere**
```

## What remains for the x-free read (the next objective)

The certification and the geometry are both in hand; what is left is the assembly, mirroring
laps 76–89 with "one good atom" replaced by "the whole sample":

1. **The position set** `⋃_{n ∈ bandT i} ⋃_α [2·kIdx(n,α), 2·kIdx(n,α)+m_i)` and its increasing
   enumeration — schedule-only, and by `windows_eq_or_disjoint` a disjoint union of windows.
2. **The block decomposition** by *distinct* window starts (a Finset of `k`s, sorted).
3. **The count bridge**: the read count over distinct windows versus `tendsto_bandT_occursCount`'s
   count over `(n,α,p)` triples — the two weightings differ by the multiplicity, and
   `card_multi_atom_le_real` bounds that by a vanishing fraction.
4. **The cutoff limit**: as in `tendsto_bandRead_freq`, using `bT_kk_le`-style domination.

The payoff is the campaign's best possible endpoint: a **schedule-only, strictly increasing**
position map along which `G₄`'s digits carry every binary word at its correct frequency — the
lap-51 objective's x-freeness and E-T8's strict monotonicity at once, saturating the lap-63 wall.
