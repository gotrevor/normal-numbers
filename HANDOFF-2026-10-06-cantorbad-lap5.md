# HANDOFF 2026-10-06 cantorbad lap 5 (branch proof/cantor-bad-normal)

Target unchanged: `exists_mem_cantorSet_bad_isNormal_coprime_three`. The headline's only on-path sorry is
now `deadCharSigned_core` (`StageSaving` was demoted to a 20% node: at S'=0 it is open-strength).

## Proved this lap
- Locality: `norm_ee_sub_rhoS_le`, `norm_deadErr_le`, `norm_deadChar_le`, `nat_tail_ineq`,
  `deadChar_tail_le` (stages ≥ N b + |h| contribute ≤ 1/N per pair).
- `deadCharSigned` ⇐ `deadCharSigned_core` (stages < min S (Nb+|h|)) + the tail bound.
- `deadCharSigned_core` ⇐ `stageSaving`: per stage ≤ C N W(N), with W summable along sched.
- Refuted route in Lean: `cs_bootstrap_floor` (Cauchy–Schwarz bootstrap only gives a floor).

## Next
State Schmidt-1960 cosine-product power saving as a `Literature` Prop and try the S'=0 case of
`stageSaving` from it (known-answer probe).  The obstacle: Schmidt covers h bⁿ, not h(bⁿ−bᵐ).
The general-S' case needs decorrelation of lacunary sums at rationals p/q near K.

## Update (end of lap 5)
- Only on-path sorry: `hybridCassels` (E|S_N|² = O(N²W) for the hybrid law: resLaw for
  a = min S (Nb+|h|) stages, then uniform digits).  Chain proved: `stage_telescope` →
  `deadCharSigned_core` → `deadCharSigned` → `casselsRate_resLaw` → headline.
- `StageSaving` was demoted to a node: per-stage bounds are lossy and open-strength at S'=0.
- For a = Nb+|h| the hybrid law is resLaw up to the scale of ξ, so `hybridCassels` is the real
  problem, truncated.  The needed input is decorrelation of lacunary sums from rationals near K
  (Khalil–Lüthi / Bénard–He–Zhang counting plus Cassels at h(bⁿ−bᵐ) mod q).
