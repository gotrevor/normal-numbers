# HANDOFF twopoint lap 6 — C1 re-wired onto hypotheses that match the literature

## Crux
`twoPointWeightedAvg_all` still `sorry` and untouched.  The run's real result is now assembled:
the C1 swing has an end-to-end chain whose every cited hypothesis is what the published proofs
actually give.

## Advance — `src/NormalNumbers/TwoPointHonestChain.lean` (no `sorry`, axiom-clean)

**`TwoPointPairSumSmall b t`** — the honest open leaf.  Along a slowly growing cutoff `w(N)`
(`w(N) → ∞`, `w(N)² ≤ N`):

    Σ_{p ≠ q ≤ w(N)} ‖E_{n<N} ζ^{ω(pn+1)} conj ζ^{ω(qn+1)} W(n)‖   =   o( L(w(N))² ) .

**`conjC1_of_delange_kataiQuantSharp_pairSumSmall`** — `ConjC1` from
Delange + `KataiQuantSharp` (true constants) + that leaf.

Supporting, all proved:
- `twoPointPairSum_eq` — the orbit-difference pair sum IS the weighted two-point pair sum, so the
  honest leaf measures the same arithmetic quantity as the ratified one.  Only the normalisation
  (`L(w)²` vs `π(w)²`) and the quantifier order differ.
- `shiftIndep_of_kataiQuantSharp`.
- `twoPointWeightedAvgSlowGrowing_of_pairSumSmall` — the honest leaf implies the ratified leaf's
  diagonal form, via `L(w)²/π(w) → 0`.  So it is strictly stronger, as the gap theorems predict.

## The run's result, in one paragraph
`TwoPointWeightedAvg` normalises the pair sum by `π(w)²`; the Kátai/BSZ Cauchy–Schwarz normalises
it by `L(w)² = (Σ_{p≤w} 1/p)²`; and `π(w)/L(w)² → ∞` (`tendsto_card_div_kataiPrimeRecip_sq`,
proved elementarily in lap 5).  `avgShape_not_imply_kataiBudget` exhibits a table meeting the
former and blowing the latter.  So the ratified leaf, even once proved, does not close C1 through
a correctly-cited Kátai step; `TwoPointPairSumSmall` is what would.

## Confidence
- `twoPointWeightedAvg_all` TRUE: **88%**.
- It suffices for C1 via a correctly-cited Kátai step: **8%**.
- `TwoPointPairSumSmall` provable with known techniques: **<5%**.  It needs the pair average to
  beat `L(w)²/π(w)²`, which is past everything in the MRT / large-sieve literature.

## Next (lap 7)
Attack `KataiQuantSharp` itself — it is the one remaining cited `Prop` in the honest chain that
is genuinely a theorem (Cauchy–Schwarz + Turán–Kubilius), so discharging it turns the chain's
only *literature* hypothesis into kernel-checked mathematics and leaves exactly one open leaf.
Start with the Turán–Kubilius variance bound `E_{n<N} (ω_w(n) − L(w))² ≪ L(w)` for `w² ≤ N`;
`PairDecoupleMertens.sum_omegaNat_AP_le_logLog` has related counting.
