# ROUTE ESCALATION 2026-10-11: gate 5, the operator's fallback trigger fired

**Trigger (operator answer 2026-10-10 22:45Z, ON-LINE-FINDINGS-2026-10-10-queue-clear.md):** "Fallback (a),
folding bases 5..7 into a gate-4-style core, reopens ONLY if the Frostman node is refuted or alpha
certifies below that threshold."

**Fired.**  `APKillFrostman449` is refuted at the stated constants for every `s ≤ 8`
(`TailReview.not_apKillFrostman449_eight`, `UniformBadTailRefute.lean`).  The witness is exact and
exhaustive: cell `(13, 808)` has all its positive Good level-25 mass in 4 of its 4096 descendants, so one
progression interval holds all of it.  The other per-cell nodes of the lap-2 bookkeeping fall the same way
(`not_apKillUniform449`, `not_regularPotential449_sixty`, `not_regularPotential2_449_45`).  The
mechanism (a window edge beside a binary-follower hull end, `ConcentratedCells449`) kills EVERY per-cell
relative bound: `not_apKillFrostman449_of_concentrated` (proved) gives `¬ APKillFrostman449 s C α` for
all `s, C, α > 0`.  There is no alpha threshold to pin.

**Assessment of fallback (a).**  (a) does NOT repair this obstruction.  Concentration comes from the
base-2/3 structure of the core, so any base `b ≥ 10` tail charged per cell meets it too.  What (a) does
change is the COUNTING route below: a crude worst-case count, which uses no regularity at all, misses the
frozen budget by ~6× with bases 5–7 in the tail, and closes (about 4.2 against 6 at γ = 28) without them.
But (a) also rebuilds gate 4 (a larger core state carrying base-5,6,7 phases, growth margin at 9/5 already
thin) and changes the meaning of the frozen crux's weights.

**Recommendation (the box proceeds on this unless the operator overrides):** stay on the frozen crux with
the COUNTING route.  The lever is comb spreading: a parent's 64 children spread over the base-3 phase circle,
so at most 12 are low-weight (exhaustive, `tail5_comb.py`), and the survivor count is at most about 6 times
the mass, with no regularity.  The open question is whether rigorous refinements (W-weighted run sums,
layer-cake comparability, exact window counts) recover the ~6× gap.  If they cannot, then (a) together with
counting is the fallback, and that is the operator's call.

Evidence: `PENDING_WORK.md` (gate 5 lap 3), `scripts/cstar_models/tail5_{concentrate2,hull,node1_witness,comb,countbudget}.py`.
