# HANDOFF — entropy laps 93–117, 2026-09-14, Opus — the schedule-only headline

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8995 jobs**.  Sorry-free; every endpoint
`[propext, Classical.choice, Quot.sound]`.

## The result

> **`Sched.tendsto_fullRead_freq`** — for every finite binary word `v`,
> `winCount (fullDig G₄) v (fT (i+1)) / fT (i+1) → 2^{−|v|}`,
> with **`Sched.fullPos_strictMono`**.

`fullPos` is defined from the **base-four schedule alone** — the band thresholds `bandT` and the
distinct window starts `winStarts`.  Nothing in it mentions `G₄`.  So this is the lap-51
objective's *x-freeness* and `E-T8`'s *strict monotonicity* at once, and by
`certified_granule_exceeds_previous_scale` it is the strongest form available on this mechanism.

`fullReal`, `isDisjunctive_fullReal`, `irrational_fullReal` package it as a real.

## What made it possible: `Q ∣ P₀` (lap 95)

`shiftG_eq` gives `ρ_{α,j} = j + Q·(…)`, so two *different* atoms at the *same* layer have shifts
congruent mod `Q`, and `freezeQ` contains their distance as a factor.  Hence `Q ∣ freezeQ ∣ P₀`,
every sample time is congruent mod `Q`, and therefore **all** orbit indices of **all** atoms at
**all** sample times are congruent mod `Q` (`kIdx_congr_Q`).  Since `Q = (U+K+N+2)!` dwarfs
`m_K`:

> **`windows_eq_or_disjoint`** — every two sampled windows coincide or are disjoint.

That is what lets the read take the *whole* sample's windows in a band, in position order, with
no reference to `G₄` — where the lap-76 read had to pick one *good atom* per scale.

## The four obstacles, and how each fell

| obstacle | resolution |
|---|---|
| the band floor is atom-dependent, so the restriction is not a sample-time restriction | `bandT` (lap 102): `gridDm·bandLo i ≤ n` is an `n`-only condition that puts *every* atom's window above the floor, and still keeps half the sample |
| the restricted *joint* law must stay certified | `H₂_vector_le` + `H₂_bandTLaw_ge` (lap 103): the `m|A|`-bit ceiling, `σ ≥ ½` costs a factor 2 plus one bit, deficit `50√K → 101√K` |
| the read counts each window once, the entropy statistic counts each `(n,α)` pair once | the multiplicity bridge: `shared_idx_apart` (P₀-separation from `coprime_d`), `card_Atom_sq_le_d`, `card_multi_atom_le_real`, `overhang_le`, `overhang_frac_le` — the overhang is an `8/|Atom|` fraction |
| the arithmetic assembly died three times on `whnf` timeouts over the astronomically large closed terms | `read_freq_error_bound` (lap 114): the same algebra over **opaque reals**, applied once |

## Where this sits in the campaign

* lap 52 — normality, **non-injective** position map, schedule-only.
* laps 56–60 — strictly increasing map, **disjunctivity** only.
* laps 76–89 — strictly increasing map with correct frequencies, but the map depends on `G₄`.
* **laps 93–117 — strictly increasing *and* schedule-only, with correct frequencies.**

The remaining gap to normality is exactly the one the wall forbids: the limit over *all* prefix
lengths, not just the band cutoffs.  `abs_midRead_freq_sub_le'` (lap 88) shows how far into each
band the correct frequency reaches; the initial portion of each band is unreachable, and its
being unreachable *is* `certified_granule_exceeds_previous_scale`.

## Next bounded tests

1. Port laps 84–89 (mid-band cutoffs, `tendsto_midRead_freq_of_depth`, arbitrary cutoffs) from
   `bandPos` to `fullPos` — the same estimates, now with the multiplicity term carried through.
2. `fullPos`'s positions are all sampled (`isSampled` of every value), so the density-zero
   non-vacuity of lap 90 should transfer verbatim.
