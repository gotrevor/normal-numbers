# KICKOFF 2026-09-23 — casting out b−1: C1–C3 frozen, prove the bridges

Worktree `~/src/nn-casting`, branch `wip/casting-out`.  Engine Opus/low.  Work **only** in
`src/NormalNumbers/CastingOut.lean` (new helper files `src/NormalNumbers/CastingOut*.lean` are fine).
Never touch other files' statements, `papers/`, `agent-mail/`, `Maze.lean`, other KICKOFFs.

## Target

The file has **ratified statements** (Ren, 2026-09-23) and `sorry`s.  Prove every theorem
without changing any statement, definition or binder.  `ConjC1/C2/C3` are `def … : Prop`: they are
CONJECTURES, never prove or weaken them.  Done when the file is sorry-free.
Math: `CONJECTURES-2026-09-23-casting-out-and-rungs.md`; probe `probes/g4_casting_out.py`.

Suggested order (easiest first):
1. `windowDigitSum_modEq`: induction on `L`.  `⌊y·b^{k+1}⌋ = b·⌊y·b^k⌋ + digit k` for
   `y = fract x`, and `b ≡ 1 [ZMOD b−1]`; then `⌊fract x·b^k⌋ = ⌊x b^k⌋ − ⌊x⌋ b^k`.  See
   `DigitInterval.lean` (floor recursion) for existing lemmas.
2. `isDisjunctive_of_isRich`: positive lower density ⇒ nonempty ⇒ `isDisjunctive_iff_forall_occursAt`.
3. `isRich_of_isNormal`: the word frequency tends to `b^{−|w|} > 0`.  Bridge `OccursAt` counts to
   `countOccurrences` (grep `Counting.lean`, `Visits.lean` for the existing bridge).
4. `primeLambertAtBase_eq_lambertVal`: `omegaR_eq`.
5. `windowDigitSum_lambert_modEq`: from 1, with `⌊x·b^N⌋ = Σ_{m≤N} w m·b^{N−m} + carry N`
   (split the tsum; the head is a natural number).  `w m ≤ m` gives summability.
6. `normalCastLaw_closed`: roots-of-unity filter, or induction on `L` with the count recurrence;
   `native_decide` is fine for sanity checks at small b, L but the theorem is for all b, L.
7. `castLaw_of_isNormal`: the event is a finite union of length-`L` cylinders, each with
   frequency `b^{−L}` by normality; sum.
8. `not_castUniform_of_isNormal`: 7 + 6 at `r = 0` (the extra `b^{−L}(b−2)/(b−1) ≠ 0` for `b ≥ 3`)
   + uniqueness of limits.
9. `conjC1_conjC3_of_normal`: 7 and 3.
10. `erdosBorweinAtBase_eq_lambertVal`: Lambert series; mirror the ω identity in
   `PrimeLambertFour.lean` (`1/(bⁿ−1) = Σ_k b^{−nk}`, swap sums, count divisors).

## Tiers

Proof tier: `native_decide`, heartbeat boosts and deprecations are fine.  Build:
`lake build NormalNumbers.CastingOut` (warm tree; never run `lake exe cache get`).  Commit each
green step.
