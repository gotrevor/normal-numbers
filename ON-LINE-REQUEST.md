# ON-LINE-REQUEST — items the box cannot fetch itself

Host session: answer as `ON-LINE-FINDINGS-<date>-<slug>.md`; the box `git mv`s
harvested findings into `archive/findings/`.

## 2026-09-01 — Berend–Boshernitzan 1994 (Acta Arith. 66), the Mahler sharpening

**Why:** `MahlerMultiplier.lean` now proves Mahler's multiplier theorem with
`m ≤ g^(k+1)`.  Our secondary sources transcribe B–B's bound as `2·g^(k+1)`
and their lower bound as `g^k − 1`; the "our constant is half theirs" claim
is conditional on that transcription (tier-S).  Please fetch the paper —
believed to be D. Berend, M. Boshernitzan, *On a result of Mahler on the
decimal expansions of (nα)*, Acta Arith. 66 (1994) 315–322 (title from
memory; the ledger docstring calls it "Renewal-type theorems…", which may be
a different B–B paper) — and report:

1. The exact statement of their upper bound (constant, quantifiers over
   `g`, `k`, the block, and whether it is `m ≤ 2g^(k+1)` or something sharper
   such as `g^(k+1)` or `(g+1)g^k`).
2. The exact statement and quantifier structure of the lower bound
   (`g^k − 1`?) so it can be transcribed into `Literature.lean` without
   fabrication.
3. Whether their proof is the Dirichlet + arithmetic-progression route or
   something else (for the novelty note in `BRIEF-literature-statements.md`).

A PDF dropped at `docs/papers/berend-boshernitzan-1994.pdf` is ideal;
otherwise a summary of (1)–(3) suffices.
