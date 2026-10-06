# HANDOFF 2026-10-06 cantorbad lap 2 (branch proof/cantor-bad-normal)

HEAD: see `git log -1` (after 7cf40bec). Working tree clean.
Target: `CantorBadNormal.exists_mem_cantorSet_bad_isNormal_coprime_three` (frozen, unchanged).

## State
- Headline proved from ONE sorry: `fourierPairRate_descent` (crux) in CantorBadNormal.lean.
- K ∩ BAD half sorry-free: exists_alive (card_dead_le ≤ 488 via card_le_of_buckets), descent_bad, cpt_mem_cyl.
- Reduction proved: secondMoment_le_fourier, casselsRate_of_fourierPairRate, ae_isNormal_of_casselsRate
  (any rate W summable along sched).
- Refutations in Lean: `perStage_deadCount_not_enough` (barrier `perStage_dead_not_enough`),
  `not_exists_timesThree_law_on_bad` (cited Literature.EFSTimesThreeNotBad, Maze row).

## Next
1. State the arithmetic sub-leaf: cancellation of Σ e(h(bᵏ−bˡ)p/q) over dead centres p/q near the path
   (martingale peel: |ν̂| ≤ Πρ + error terms built from dead children), see PENDING_WORK 2026-10-06.
2. Formalize the peel inequality as a proved lemma; leave the arithmetic cancellation as the named sorry.

## Gotchas
- `ulimit -n 65536` before `lake env lean` / `lake build` (else "Too many open files").
- Never wrap `git commit` in `timeout` (pre-commit build takes >2 min); never `pgrep -f "lake build"` loops (match themselves).
