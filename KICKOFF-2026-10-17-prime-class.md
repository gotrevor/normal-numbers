# Kickoff 2026-10-17: joint normality of one prime Stoneham class (Theorem T-B′)

Branch `proof/prime-class`, worktree `~/src/nn-prime-class`.  Target file
`src/NormalNumbers/StonehamPrimeClass.lean`, ratified sorried statements:

- `not_isRationallyJointNormal_of_not_linearIndependent` (non-normal half, elementary)
- `isRationallyJointNormal_of_linearIndependent` (normal half)
- `isRationallyJointNormal_pair_iff` (pairs: `ord_p b ∤ 2(m₂ − m₁)`)
- `stonehamThreeSevenPairwiseNormal_holds` (the parked L2 premise in `StonehamSumsBoundary.lean`)

The iff and `stonehamThreeSeven_pairwise_not_joint_unconditional` are already wired.  **Do not
change these statements, `primeClassFamily`, `IsRationallyJointNormal`,
`IsPairwiseRationallyJointNormal`, or any statement in an existing file.**  New machinery goes in
new files (`StonehamPrimeClass*.lean`).  Existing results are inputs: `VandeheyProof.vandeheyThm51_holds`
is proved, so call it freely.

## Source

`papers/2026-10-16-bailey-borwein-full-answer.md`: read **Referee repairs** first (repair 1 is the
analytic route for a single class), then (a) the characterization specialised to g = p prime,
(b) Lemma 3′, and the L2 witness in "Elementary witnesses".  With g = p prime the twist
`ω^{−m′u^j}` is trivial (u = 1), so each class phase reduces to the value of a polynomial in ω.

## Route

1. **Algebra layer.**  Translate `LinearIndependent ℚ (fun i => ζ ^ m i)` (ζ a complex primitive
   `d`-th root, `d = orderOf (b : ZMod p)`) into a finite-level statement about
   `w = b^{p^K} mod p^{K+1}` (the finite Teichmüller substitute, Lemma 3′ (K)): a rational
   combination `Σ qᵢ X^{mᵢ}` vanishes at ζ iff `Φ_d ∣ Σ qᵢ X^{mᵢ}` iff it vanishes at ω in `ℤ_p`
   (equivalently, `p^{K}` divides the cleared integer `Σ qᵢ' w^{mᵢ}` for all large K).  Mathlib
   has `IsPrimitiveRoot.minpoly`/`cyclotomic` irreducibility over ℚ; the `ℤ_p` side can stay
   finite-level.  For p = 2, d = 1 (ζ = 1): handle via `b^{2M} ≡ 1 mod 2^{v₂(2M)+2}`.
2. **Non-normal half.**  If `Σ qᵢ ζ^{mᵢ} = 0` with `q ≠ 0`, the scaled combination has a bounded
   state denominator on pieces of positive upper density, so `{bⁿx}` sits within `C₀/n` of
   `(1/C!)ℤ/ℤ` there, contradicting uniform distribution.  Template: the L2 witness
   (`not_isRationallyJointNormal_stonehamThreeSeven`) and L1 in `StonehamSumsBoundary.lean`; the
   general version needs the coefficient choice `q ↦ q·g^{…}` across sᵢ (the sᵢ are irrelevant
   because `α_{B,p^s}` is the sub-series of `α_{B,p}` over `k ≡ 0 mod s`, and the Mahler identity
   `α_{b^{mp},p} = p·α_{b^m,p} − b^{−mp}` moves `m` by powers of `p`).
3. **Normal half.**  Independence ⇒ the class is never silent ⇒ power denominator lower bound
   (`StonehamStateDenPowerLower`, `StonehamPairsAnalytic.lean`) ⇒ normal via
   `StonehamSumsNormal.stonehamCombination_mean_tendsto_of_powerLower` (already r families; the
   pair wrapper `isNormal_stonehamAlpha_pair_of_powerLower` is the template).  The
   one-class completion bound of referee repair 1 avoids F3, but F3 is proved, so either route is
   fine.
4. **Pairs.**  For `r = 2`: `ζ^{m₁}, ζ^{m₂}` dependent iff `ζ^{m₂−m₁} ∈ ℚ` iff `ζ^{m₂−m₁} = ±1`
   iff `d ∣ 2(m₂ − m₁)`.  Derive from the iff.
5. **L2 premise.**  `ord_7 3 = 6` (decide), and 6 divides none of `2·1, 2·2, 2·1`; unfold
   `IsPairwiseRationallyJointNormal` into the three pair instances (note its `a ≠ 0 ∨ c ≠ 0`
   form versus `q ≠ 0`).

Steps 1, 2, 4, 5 are independent of 3: land them first.

## If a statement is false

Do not weaken it.  Prove the negation next to it with the explicit witness, leave the original
sorried with a docstring note, and `box stuck`.  (Probe evidence: J1–J8 ranks and 900 blind
trials matched T-B′ with 0 mismatches; a counterexample would be a major finding.)

## Done when

`StonehamPrimeClass.lean` is sorry-free (host gate), the build is green, and all six theorems print
only `[propext, Classical.choice, Quot.sound]`.  The host gate is a per-file grep, so the axiom
print is the real gate.  Remove the four `BarrierAudit` waivers when proved.  Record each landed
theorem in `STATUS.md` and the Maze row "joint normality is pairwise" (`.parked` → kernel
`.refuted`) once `stonehamThreeSevenPairwiseNormal_holds` is axiom-clean.
