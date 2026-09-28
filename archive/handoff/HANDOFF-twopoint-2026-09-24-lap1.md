# HANDOFF twopoint lap 1 — the fixed-`w` worry is DECIDED (refuted at quantifier level)

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointWorry.lean` (imported).

## Crux
`twoPointWeightedAvg_all` (`TwoPointBet.lean`), still `sorry`.  Kickoff item 1 was to decide
Ren's ≈65% worry that `TwoPointWeightedAvg` is a repackaging of natural-density two-point
Elliott, because `w` is quantified before `N`.

## Advance this lap
The worry's argument is **false**, and that is now machine-checked.

The point: the average over the (fixed, finite) pair set is taken **before** the `limsup` in `N`.
For nonnegative sequences, `limsup` of a finite average is bounded below only by
`π(w)^{-2} · max_{p,q} limsup`, which is vacuous.  If different pairs reach their near-extremal
correlation at **asynchronous** times, every pair can have `limsup = 1` while the average has
`sup_N ≤ π(w)^{-2} → 0`.

Formalized (`#print axioms` clean, only propext/choice/Quot.sound):
- `AvgShape G` — the `TwoPointWeightedAvg` quantifier shape on an abstract table;
  `twoPointWeightedAvg_iff_avgShape` is `Iff.rfl`, so the bet's leaf IS an instance.
- `avgShape_of_forall_tendsto` — pointwise ⟹ averaged (the surviving residue of the worry: the
  averaged leaf is the weaker statement, so Tao-type input still suffices).
- `badTable p q N = [ (unpair N).1 = pair p q ]` — at each `N` exactly one pair is on.
- `avgShape_badTable`, `not_tendsto_badTable`, and the headline
  **`avgShape_not_imply_pairwise`**: ∃ `G` with values in `[0,1]`, `AvgShape G`, and no pair
  tending to `0`.

## Scope (honest)
`badTable` is arbitrary, not arithmetic.  What is refuted is the *inference* "fixed finite pair
set ⟹ pointwise statement", which was the whole of the worry.  Whether the real table
`G p q N = ‖E_{n<N} ζ^{ω(pn+1)} conj ζ^{ω(qn+1)} W(n)‖` can be asynchronous is now THE question.

## Next attack (lap 2), in priority order
1. **Arithmetic asynchrony probe.**  For `b = 3, 5` compute `G p q N` over small primes and
   `N ≤ 10^6`–`10^7` (stdlib Python in `probes/`, with a hand-checked known answer) and look at
   whether the near-maximal `N` for different pairs are disjoint or synchronised.  If synchronised
   (e.g. all pairs peak at the same `N`, as a common small-prime obstruction would force), the
   asynchrony room is illusory and the leaf really is pointwise-hard — that would be a second,
   sharper decision.
2. **The growing-`w` re-plumb** (kickoff item 2): quantitative `KataiQuantAvg` with `w = w(N)`.
   Now strictly *more* attractive than before, because lap 1 shows the fixed-`w` form is not
   self-evidently hard: the re-plumb should be judged on whether it buys an MRT-style argument,
   not on rescuing the quantifier order.

## Confidence
- The ratified leaf `twoPointWeightedAvg_all` is TRUE: 80% (it follows from pointwise two-point
  Elliott for `ζ^ω` along `pn+1`,`qn+1` plus `WeightDecouple`, both widely believed).
- PROVABLE with known techniques: 20% — unchanged by this lap.  Lap 1 removed a reason to think
  it is *equivalent* to the open problem; it did not supply a route.
