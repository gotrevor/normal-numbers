# HANDOFF 2026-10-06 cantorbad lap 4 (branch proof/cantor-bad-normal, HEAD f675fc92)

Target unchanged: `exists_mem_cantorSet_bad_isNormal_coprime_three` (CantorBadNormal.lean).
Operator resolution (2026-10-05 22:55) CARRIED OUT.

## Done (all proved, build green)
- New law `resLaw` (`descentU/buildU/selU`): a dead stage takes the first alive block among
  fresh coin blocks `blk ω s t` (Nat.pair).  Measurable, Bad (`cpt_bad_of_alive`).
- Old crux is now the node `FourierPairRateChoose`; `DeadRateDecay` kept.
- Block independence: `MS`, `indep_MS`, `coin_blkVec`, `coin_deadRun`, `coin_selU`,
  `buildU_succ_uniform` (rejection sampling is uniform on the alive set).
- Finite-depth telescope: `integral_buildU[_succ]`, `alive_avg`, `prefChar_succ`, `prefChar_eq`,
  `norm_rhoS`, `norm_rhoProd`, `norm_fourier_sub_prefChar`, `cassels_Bf`, `cassels_muK`.
- Headline = `exists_of_law resLaw (casselsRate_resLaw ·)`; `casselsRate_resLaw` proved from
  the ONE remaining on-path sorry, the signed crux `deadCharSigned` (60%).
- `DeadCharCancelAbs` (40%): the absolute form, now a node; `deadCharSigned_of_abs` proved.
  It is too lossy, because it needs decay at the middle ternary digits of bⁿ.

## Next
See the cantorbad lap-4 block at the end of PENDING_WORK.md.  Write the S'-term as ∫|S_N|²dτ_{S'}
(τ signed: dead child minus uniform share; diagonal cancels).  Split S_N into low terms
(bⁿ < 3^{10S'}, O(1) change) and high terms.  For the high part, try a bootstrap over hybrid
laws (ν for S' stages, then Cantor) by induction on S'.
Off-path sorry: `fourierPairRate_descent_of_deadRateDecay` (old law).
