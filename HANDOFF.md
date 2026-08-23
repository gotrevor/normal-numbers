# HANDOFF — B5′ / W1 campaign: prove the 12 sorries in `src/NormalNumbers/CFCylinder.lean`

**Objective**: work package W1 of expedition B5′ (one witness real that is
absolutely normal + CF-normal + Khinchin-typical).  All 12 `src/` sorries
live in `CFCylinder.lean`; `src/` sorry-free = done (the self-stop gate).

**Read first**: `KHINCHIN.md` (the plan, W1–W6 + the decided W3 route),
`papers/becher-yuhjtman-2019-abs-normal-cf-normal.md` (the dependency map),
and the module docstrings of `CFDefs.lean` / `CFCylinder.lean`.

**Statement discipline** 🎯: the 12 statement shapes are FROZEN
(guard-by-name; anchors in the file are kernel-checked and must keep
passing).  Add as many private intermediate lemmas as you like — in
`CFCylinder.lean` or a new imported module — but do not weaken, reshape, or
re-hypothesize a frozen statement.  If one looks *wrong*, STOP on it, write
the evidence into this HANDOFF, and move to the others.

**Suggested order** (algebra first, measure last):

1. `cfK_drop_one_le` — direct from the `cfK` recursion; warm-up.
2. `cfK_append` (Euler gluing) — **the keystone**; induction on `w`, likely
   proving the pair `(cfK (w ++ u), cfK (w.drop 1 ++ u))` together or
   strengthening the IH.  Deliberately NOT the paper's `α_{r,s}` subset
   combinatorics.
3. `cfK_dropLast_le` — from gluing with `u = [last]`, or its own induction.
4. `cfK_mul_le_append`, `cfK_append_le` — one-liners from gluing +
   monotonicity (B–Y Lemma 3.1's proof, verbatim).
5. `fib_le_cfK` — two-step induction.
6. `cfVal_eq_div` — induction via the `pₙ/qₙ` recursions.  Worth proving the
   classical determinant identity `qₙ·pₙ₋₁ − pₙ·qₙ₋₁ = ±1` as an
   intermediate (needed again for `volume_cfCylinder`).  Mathlib grep
   candidates: `Mathlib/Algebra/ContinuedFractions/Determinant.lean`,
   `ContinuantsRecurrence.lean` (statement shapes unverified — check before
   leaning on them; self-contained induction is also fine).
7. `tailDensity_mem_Icc`, `cylMap_denom_ratio_le` — pure real algebra
   (`field_simp`/`nlinarith` territory); can be done any time.
8. `volume_cfCylinder` — **the meaty one, expect it to be half the
   campaign**.  Route: characterize `cfCylinder w` up to a countable junk
   set as the interval between `cfVal w` and `cfVal (bump-last w)` (parity
   decides orientation), via a digit-reading bridge: `cfDigit x 0 = k ⇔
   x ∈ (1/(k+1), 1/k]`, then induct with `cylMap`/`gaussMap` (this is the
   CF analog of `DigitInterval.lean`).  Endpoint/rational junk is countable
   hence null — work up to measure zero throughout.
9. `volume_cylinder_append_le`, `le_volume_cylinder_append` — from the
   volume formula + quasi-multiplicativity; mirror B–Y's own one-page
   Lemma 3.2 computation.

**Warnings** ⚠️: the digit-positivity hypotheses (`∀ a ∈ w, 1 ≤ a`) are
load-bearing — digit `0` is the junk marker for rationals/out-of-range (see
`CFDefs.lean` conventions).  Half-open vs open interval mismatches at
cylinder endpoints are null sets, not equalities — don't chase set-level
identities the statements don't need.

**Gates**: `lake build` green every commit (pre-commit hook enforces);
anchors keep passing; once all 12 are discharged, `#print axioms` each of
the 12 = exactly `propext`, `Classical.choice`, `Quot.sound`.
