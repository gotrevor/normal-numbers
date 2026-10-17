# Kickoff 2026-10-17: Bailey–Borwein's question, literally (every pair)

Branch `proof/bb-literal-pairs`, worktree `~/src/nn-bb-pairs`.  Target file
`src/NormalNumbers/StonehamPairsNormal.lean`: `isNormal_stonehamAlpha_add` and
`isNormal_stonehamAlpha_sub` (ratified; the `α₂,₃ + α₂,₉` corollary is already wired).  **Do not
change these statements, `VandeheyThm51`, or Theorem A's statements in `StonehamSumsNormal.lean`.**
New machinery goes in new files (`StonehamPairs*.lean`).  A parallel run (`nn-vandehey`) is
proving `VandeheyThm51` in `VandeheyKorobov*.lean` / `VandeheyProof.lean`: do not touch those.

## Source

`papers/2026-10-16-bailey-borwein-full-answer.md`: read the **Referee repairs** section first,
then (a) the characterization, (b) Lemma 3′ and "Why the literal BB pair is never silent".  The
literal pair is the simplest case of Theorem C: each class holds one or two families with
coefficients in {1} (sum) or {±1} (difference).

## Route

1. **Reuse the analytic half.**  Theorem A's normality proof is factored through
   `StonehamStateDenLinearLower` (`stonehamCombination_mean_tendsto_of_linearLower`, which already
   drops pairwise coprimality).  If a family only has a **power** lower bound (`n^ρ ≤ C · den`, ρ > 0;
   the referee found composite same-class g where only some primes ℓ | g stay loud), generalize the
   interface to that power form with an arbitrary constant, re-prove the block/mean lemma from it
   (§5 only needs `D → ∞` on pieces of length ≥ √N and `D ≤ L nʳ`, so ε = 1/(2r+1) still works), and
   keep the old linear lemma as a corollary.  Do not alter Theorem A's statements.
2. **Lemma 3′ for one or two families** (the arithmetic half):
   - (K) Teichmüller congruence `b^N ≡ ω^N mod ℓ^{v_ℓ(N)+1}` in finite-level form
     (`w = b^{ℓ^K} mod ℓ^{K+1}`); ℓ = 2 via `b^{2M} ≡ 1 mod 2^{v₂(2M)+2}`.
   - Polar part and periodic tail for the classes present.
   - Rate separation for two distinct primitive bases.
   - "Never silent" for coefficients {1} / {±1}: at the top digit, `Σ_{s<P} μ(J−s) g^s` with
     `|μ| ∈ {0,1,2}` is nonzero (referee repair 3: the case split is unnecessary).
   Conclude the (linear or power) denominator lower bound for both target families.
3. **Split by class structure** if it helps: different classes (c₁, c₂ multiplicatively
   independent) versus the same class (c₁ = g^{s₁}, c₂ = g^{s₂}).  The sum with c₁ = c₂ is
   `2·α_{b,c}`: use `isNormal_rat_mul_add` and the existing single-Stoneham normality.

## Stretch (after both targets are axiom-clean)

`StonehamThreeSevenPairwiseNormal` (`StonehamSumsBoundary.lean`): the parked premise of the Maze
row "joint normality is pairwise".  It is a same-prime (p = 7, b = 3) case of T-B′; if the step 2
machinery proves it, promote that row from `.parked` to kernel `.refuted`.

## If a statement is false

Do not weaken it.  Prove the negation next to it with the explicit witness, leave the original
sorried with a docstring note, and `box stuck`.  (The referee's exhaustive search found no
cancelling literal pair, so a counterexample would be a major finding.)

## Done when

`StonehamPairsNormal.lean` is sorry-free (host gate), the build is green, and all three theorems
print only `[propext, Classical.choice, Quot.sound]` (the `VandeheyThm51` binder is a hypothesis,
not an axiom).  The host gate is a per-file grep, so the axiom print is the real gate.  Remove the
two `BarrierAudit` waivers when proved.
