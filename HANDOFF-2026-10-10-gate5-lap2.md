# HANDOFF 2026-10-10 — operator gate 5, lap 2

Branch `proof/uniformbadtail-threshold` (proof/uniformbad-threshold), HEAD b61d7612 (green).
Untracked, NOT mine (leave): scripts/cstar_models/tail5-review, test_tail5_review.py,
src/NormalNumbers/UniformBadTailProbeReview.lean, __pycache__.

## Key corrections this lap
- Kill test NOT fired: lap 1 omitted shift-2 PASS (4.50 at n<=7; base 5 3.71 at n<=8). Records fixed
  (Obstruction docstring, Maze row, ON-LINE-REQUEST correction).
- Good449 is NOT hereditary (~0.6-0.8% of Good cells have non-Good ancestors).
- Uniform AP kill bound (APKillGeneral449) very likely FALSE (ratio ~(hq)^-0.09); use Frostman form.

## Architecture (src/NormalNumbers/UniformBadTailMechanism.lean)
crux <- tailChargeBudget449_of_ratio (PROVED: loss <= c mass, c < 33 suffices; measured 0.23)
 <- strong induction on alive potential P(m)=alivePot 2 m:
   * alivePot_succ_le (PROVED, from node 4' RegularPotential2_449, all cells; measured R2 43.2-43.8)
   * regularPotential_iter (PROVED)
   * alivePot_le: P(m) <= mass(m+2) + extLoss m (PROVED)
   * extLoss_le_killedTot, killedTot_le_sum (PROVED: finite union over (b,n))
   * NEXT: per-(b,n) bound killedBy b n m <= C (2hq)^alpha R^j alivePot 2 (m-j) via node
     APKillFrostman449 (Frostman alpha ~0.90 measured, AP probes <= 2x coverage); interior windows
     vs edge kills of wider windows (one-sided 2^-6m nbhds of endpoint APs).  Then sum (numerics:
     ~3.7 vs c=6 at alpha=0.9; thin at 0.85), then induction -> crux.
 tailChargeBudget449_of_nodes (sorry, waived) is the older-form statement; update its hypotheses to
 the Frostman + node 4' set when the bookkeeping lands.
Probes/outputs: scripts/cstar_models/tail5_*.py, tail5_out/*.txt.  PENDING_WORK.md has the log.
