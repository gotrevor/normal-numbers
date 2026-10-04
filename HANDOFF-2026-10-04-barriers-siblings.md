# Handoff 2026-10-04: barrier-library siblings, all four proved

Lane: barrier library siblings (`src/NormalNumbers/Barriers/Siblings.lean`).  Statements and
definitions unchanged; all four frozen `sorry`s are discharged and promoted to `.proved` in
`src/NormalNumbers/Barriers.lean`.  `#print axioms` on each: `propext, Classical.choice,
Quot.sound`.

| Sibling | Declaration | Route |
|---|---|---|
| (a) | `exists_rat_isNormalUpTo_not_isNormal` | counter word `CounterWord.ctr` (block j = bits of j mod 2^K, period K·2^K); `card_offset` via the bijection `gwin`; rationality `realOfDigits_periodic`; non-normality `ExplicitPQ.not_isNormal_two_ratCast` |
| (b) | `exists_isLogNormal_not_isSimplyNormal` | `LogNormalWitness.exists_isNormal` (Borel in every base from DEL `ae_isNormal_of_secondMoment`, Lebesgue on [0,1], second moment = N); zero blocks [2^{2^J}, 2·2^{2^J}); `bad_weight_le` + `ratio_tendsto`; digit 1 at n = 2N_J for non-simple-normality |
| (c) | `exists_normal_prefix_limit_not_normal` | `z / 2^j`, z = Stoneham number |
| (d) | `tsum_two_pow_div_fermat` | telescoping, `hasSum_iff_tendsto_nat_of_nonneg` |

New reusable facts worth knowing: `LogNormalWitness.exists_isNormal` is the repo's first
unconditional normal number in every base `b ≥ 2` (previously only `3 ∤ b`).

Build: the host file table (virtiofs) runs out under parallel `lake build`
("Too many open files in system", also surfacing as ENOENT / "bad import").  Workaround used:
loop `lake build`, rebuilding each failed module alone, until green (see the lap journal).
