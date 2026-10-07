# HANDOFF 2026-10-07: repetition lap 1 (branch proof/cantor-repetition)

Supersedes older HANDOFFs for this worktree (operator kickoff: KICKOFF-2026-10-06-repetition.md).

## State
`liouvilleCantorFullProfile` is PROVED wiring.  Single open sorry in scope:
`ae_isNormal_rep_of_three_dvd` (b = 3ˢt, t>1).  Proved axiom-clean: construction `repReal`,
`repReal_mem_cantorSet`, `liouville_repReal`, `charFun_add`, `ae_isNormal_rep_of_coprime_three`,
`not_isNormal_rep_three_pow`, `ae_repProfile`, copy-zone algebra (`copyPairSum_eq_Bf`, `Bf_lip`,
`copyTerm_le`, `cycProd_*`, `cycProd_pair`), `copyZoneDecay_of`.

## Open nodes (Prop, not yet wired into the crux)
- `TOrbitCyclicDecay t` (55%): digits of c·tᵐ mod 3^A−1.  Probe scripts/rep_single.py.
- `BadGcdSparse b` (75%): naive Σ log gcd counting fails by the ω(3^A−1) factor.
- `CopyZoneDecay b` ⇐ both (proved).

## Next
1. Define the zone split of the second moment for repReal at b=3ˢt (free / copy / shadow) and
   prove the crux from: CopyZoneDecay, a free-zone Cassels bound, a shadow (Baker) bound.
   The copy-zone pair term of the true law carries a 3^{-A} twist and run-end truncation;
   bound by cycProd via `charFun_add`-style factorization over block coins.
2. Attack BadGcdSparse via orders mod prime powers of 3^A−1.
