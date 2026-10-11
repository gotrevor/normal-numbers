# HANDOFF 2026-10-11 — operator gate 5, lap 3 (fresh-mind REVIEW lap)

Branch `proof/uniformbad-threshold`, lap work at HEAD 54c01a0a.  Build green (full default build, 10850 jobs).  Binding orders:
`DIRECTION.md` → CURRENT DIRECTIVE (gate 5 review lap 3), at the top of the branch section.

## What changed this lap
- **Lap-2 route refuted** (`src/NormalNumbers/UniformBadTailRefute.lean`, Maze row "Per-cell relative
  regularity nodes for the gate-5 tail bookkeeping").  Every per-cell node at its stated constants:
  `not_apKillFrostman449_eight` (+ `_six`, `_zero`), `not_apKillUniform449`,
  `not_regularPotential449_sixty`, `not_regularPotential2_449_45`.  Exact, exhaustive witnesses
  (integer arithmetic, no ambiguous comparisons); the finite facts are sorry'd with the exact rationals
  in their docstrings and waived in `BarrierAudit.lean`.  Proved: `not_apKillFrostman449_of_hull`,
  `apKillFrostman449_mono`, `not_apKillFrostman449_of_concentrated` (from the believed node
  `ConcentratedCells449`), and `tailChargeBudget449_of_upperGrowth_kill` (totals form of the crux).
- Mechanism: **concentrated cells**.  A window edge lands beside a binary-follower hull end, so a cell's
  whole positive mass sits in a sliver.  Any bound normalized by one cell's own mass fails there.
- **New lever: comb spreading** (`scripts/cstar_models/tail5_comb.py`).  A parent's 64 children lie at
  phases `x0 + iρ` on the base-3 circle, at most 3 per x-bin, so at most `e = 12` are non-Good or below
  `maxW/3` (exhaustive over all core-alive parents, `k ≤ 15`).  This gives survivor count
  `N' ≤ K·mass`, `K ≈ 5–6`, by a per-parent induction, with no regularity.
- **Crude counting screen** (`tail5_countbudget.py`): it misses the frozen budget by ~6× at γ ≈ 28.  The
  loss is long-window edges of bases 5–7.  It closes if bases 5–7 are dropped (that is fallback (a)).
- The operator trigger for fallback (a) fired (Frostman node refuted), so it is escalated:
  `ROUTE-ESCALATION-2026-10-11.md` and `ON-LINE-REQUEST.md`.  The box continues on the frozen crux.
- Housekeeping: Codex's `UniformBadTailProbeReview.lean` is now in the build; the host's queue-clear
  findings are archived; the 700 MB exact core dump `tail5_out/core/` is gitignored (regenerate with
  `tail5_dump.py 27`).

## Next (PENDING_WORK "Gate 5 lap 3", NEXT 1–3)
1. **Refined counting screen** (decisive).  Replace the crude constants with rigorous per-parent finite
   quantities: (i) W-weighted run sums `f(R)` (max over parents and contiguous child runs);
   (ii) layer-cake comparability `N' ≤ β(mass + loss) + e'·N'_prev`; (iii) exact per-ancestor window
   counts per `(b, φ0)`.  Does Σ h_ℓ/γ^ℓ ≤ (9/5)^6 − γ close?
2. If it closes: freeze the per-parent facts as nodes, prove the strong induction (comparability and
   charges together) in Lean, then certify the nodes by a gate-4-style B&B (max instead of min, including
   zone parent types).
3. If it does not: state the counting obstruction (Lean plus Maze row) and wait for the operator on (a).

Untracked, not mine: `.obsidian/workspace.json` changes (leave).
