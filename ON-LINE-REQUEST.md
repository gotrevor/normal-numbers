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

## 2026-09-02 — Berend–Boshernitzan 1994, the LOWER bound (follow-up)

Same paper as the 2026-09-01 request (D. Berend, M. Boshernitzan, *On a result
of Mahler on the decimal expansion of (nα)*, Acta Arith. 66 (1994) 315–322).
New, sharper question, because this repo now proves a lower bound that beats the
`gᵏ − 1` our secondary sources attribute to them:

- We prove `M(g,k) ≥ t·(gᵏ − 1)` for **every** factorization `g = t·c` with
  `c ≥ 2` (so `(g/2)(gᵏ − 1)` for every even base; `8(10ᵏ − 1)` for base 10 with
  a finite witness).  Construction: `α = c · Σ g^(−i!)`.
- **Do B–B state a lower bound of this shape** (base-dependent, `≍ g^(k+1)` for
  composite `g`), or only `gᵏ − 1`?  Their §/theorem number and exact quantifiers
  are what we need.
- Do they state `M(g,k)` exactly for any `(g,k)` beyond `M(3,1) = 2`?  A single
  exact value for a COMPOSITE base would settle whether our bound is sharp.

Until answered, `MahlerLowerBoundGeneral.lean` states our own quantifiers and
attributes nothing.
