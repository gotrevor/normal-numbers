# HANDOFF twopoint lap 5 — the lap-4 gap is now a quantitative REFUTATION

## Crux
`twoPointWeightedAvg_all` still `sorry`.  But the route-decisive question has changed: lap 4
found that `KataiOrthogonalityAvg` overstates BSZ/Kátai; lap 5 closes that argument.

## Advance — `src/NormalNumbers/TwoPointKataiGap.lean` (no `sorry`, axiom-clean)

**The missing comparison, proved elementarily.**  The refutation needed `π(w) ≫ L(w)²`,
`L(w) = Σ_{p≤w} 1/p`.  Proved with no PNT, no Mertens, no Chebyshev: for every `K ≥ 1`,

    L(w)  ≤  (K + 1)  +  √( π(w) / K ),

by splitting the primes at `K` (small ones: `≤ K+1` of them, each `≤ 1`) and Cauchy–Schwarz
(`sq_sum_le_card_mul_sum_sq`) on the tail against `Σ_{n > K} 1/n² ≤ 1/K` (telescoped by
`Nat.le_induction`).  Hence `L(w)²/π(w) ≤ 2(K+1)²/π(w) + 2/K` for *every* `K`, so
`tendsto_kataiPrimeRecip_sq_div_card : L(w)²/π(w) → 0` and
`tendsto_card_div_kataiPrimeRecip_sq : π(w)/L(w)² → ∞`.

**`avgShape_not_imply_kataiBudget`** — the refutation.  `hubTable` (every pair through the
prime `2` fully correlated) satisfies the `AvgShape` quantifier order *exactly* — the hypothesis
`KataiOrthogonalityAvg` / `PairMeanAvgZero` impose — and yet

    sumTable hubTable w N / L(w)²  →  ∞ ,

i.e. its pair sum is not merely unbounded but **swamps the `L(w)²` budget** that the honest
Cauchy–Schwarz allows.  So the averaged criterion as stated does not supply what the BSZ/Kátai
proof consumes, and its citation as a theorem of that literature is **not supported**.

## Status of the bet
The kickoff offered three success conditions.  This is the second: *a leaf is honestly shown to
be something other than advertised.*  Specifically —

- The ratified `twoPointWeightedAvg_all` is untouched and still very likely TRUE (88%).
- But `conjC1_of_delange_kataiAvg_twoPointWeightedAvg` — the reason it was the target — routes
  through a hypothesis that is **not** a known theorem.  The honest replacements are in
  `TwoPointKataiSharp.lean`: `KataiQuantSharp` (correct constants) with the leaf
  `PairSumSmallGrowing` (`pairSum ≪ L(w)²`).
- Ren's original fixed-`w` worry (lap 1) was refuted as an *argument*; the real defect was one
  level down, in the constants of the Kátai step, and it is worse than the worry suspected: not
  "no easier than pointwise", but "the averaged hypothesis is not the literature's".

## Confidence
- `twoPointWeightedAvg_all` TRUE: **88%**.
- It SUFFICES for C1 via a correctly-cited Kátai step: **8%** (down from 25%; lap 5 makes the
  obstruction a theorem rather than a suspicion).
- `PairSumSmallGrowing` (the honest leaf) provable with known techniques: **<5%** — it demands
  the pair average beat `L(w)²/π(w)²`, far past MRT.

## Next (lap 6)
Re-wire C1 onto the honest chain end-to-end so the development's cited hypotheses match the
literature: a new file deriving `ConjC1` from Delange + `KataiQuantSharp` + a named leaf
`TwoPointPairSumSmall b t`, mirroring `conjC1_of_delange_kataiQuant_twoPointSlowGrowing`.  Then
the honest open problem is visible in one place, and `twoPointWeightedAvg_all` can be recorded
(without being weakened) as insufficient-by-itself for that chain.
