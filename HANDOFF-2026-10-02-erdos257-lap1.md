# HANDOFF 2026-10-02 — Erdős #257 for A = k·S, lap 1 (CLOSED)

Branch `proof/erdos257`, HEAD `acceb1e6`.

## Done
All five frozen statements in `src/NormalNumbers/Erdos257.lean` proved; `#print axioms` =
[propext, Classical.choice, Quot.sound] for `kMulPrimes_infinite`, `erdos257_kMul`,
`erdos257_kMul_primes`, `erdos257_kMul_residueClass`, `erdos257_twoMul_normal`.
New lemmas: `subsetLambert_two_pow_eq` (Lambert identity), `isNormal_two_of_four`
(base change 4 → 2 via Wall + `visitCount_two_even`).

## Next
- `erdos257_twoMul_normal` takes C′ hypotheses (`SqrtFreshMassZero`, `DivergentRecip`) as
  arguments; exhibiting a concrete set satisfying them is upstream C′ work.
- Possible generalisation: `isNormal_two_of_four` → `IsNormal (b^K) x → IsNormal b x`.
