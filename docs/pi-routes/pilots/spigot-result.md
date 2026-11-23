# Spigot pilot result

Module: `src/NormalNumbers/PiDisjunctiveRoutes/RoundTwoSpigot.lean`.

## Results (all proved, no sorry)

- `spigotStep_two_alternating`: for any state with `0 < p`, `q = 3r`, `8p < r`,
  two `spigotStep`s emit `0` then `1` without refining; net `(p,r,q) ↦ (4p,r,q)`.
  This is the reusable mechanism.
- `iterate_alternatingSeed`: closed form of `iterateSpigot (2k) (alternatingSeed L)`
  for `k ≤ L`.
- `positiveWidthAlternatingPrefix : PositiveWidthAlternatingPrefix` (frozen target).
- `no_index_uniform_waiting_bound`: for every `B` there is a state with `n = 0`,
  `0 < p`, `0 < q` whose first `2B` steps read nothing and whose output avoids
  both `[0,0]` and `[1,1]`.
- `no_index_only_emit_rank`: no `f : ℕ → ℕ` bounds the number of consecutive
  non-reading steps by a function of the input index alone, over states with
  `0 < p`, `0 < q`.  This is the precise rank family excluded.
- `zeroWidth_twoCycle`: auxiliary `p = 0` control, an exact two-cycle.

## Scope

Nothing here concerns `spigotInitial`: the seeds are not claimed reachable, and
`SpigotEscapeBudget` is untouched.  The width `p/q` is positive but tiny
(`4^k / (3·4^(L+1))`); the family exploits that the enclosure center sits
exactly at the alternating point `r/q = 1/3 = 0.0101…₂`.

## What a pi-specific ranking invariant must exclude

Any ranking must use more than `n`: it must see either the width `p/q` relative
to the index (here `p/q ≈ 4^{-(L+1-k)}` at `n = 0`, far narrower than any state
reachable at index 0 from `spigotInitial`, whose width at `n` is governed by
`n!/(2n+1)!!·2^{emitted}`), or the center's distance to dyadic-rational-with-
periodic-expansion points like `1/3`.  The candidate independent arithmetic
condition is a width lower bound `p·2^{-out} ≥ c(n)·q` tied to emission count;
it was not proved for the true recurrence in this lap (open).

## Prospective Maze entry

- Route: index-only waiting bounds / word-search budgets uniform over valid
  positive-width spigot states.  Aliases: "read-free emit bound", "n-ranked
  escape".
- Crux: `no_index_only_emit_rank` (proved).
- Reopen only with an invariant using width-vs-emission-count or center
  arithmetic that is proved for states reachable from `spigotInitial` by
  independently checkable conditions (not "reachable" itself).
