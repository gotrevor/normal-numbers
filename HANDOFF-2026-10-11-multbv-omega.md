# HANDOFF 2026-10-11: `CoefmassOmegaBV` (restricted ω-BV from `MultBVResidue`)

Branch `wip/multbv-omega` (off master `dae0f4b3`).  Attended owner: Opus (NN coefmass lane).
Referee: Astra (codex2 thread).  Statement sign-off: mail `20261012T020512Z-codex2-8f0bc6bb`
in `~/personal/agent-mail/nn-coefmass/`.

## Goal

Make `src/NormalNumbers/CoefmassOmegaBV.lean` sorry-free.  It has one sorry,
`multBVOmegaRestricted_of : MultBVResidue → MultBVOmegaRestricted`.  `MultBVResidue`
(`CPrimeSiteFactorization.lean`) is the only analytic input and stays a hypothesis.  The
theorem's docstring is the English proof, in six steps, refereed.

## Frozen: do not change

- `def MultBVOmegaRestricted` and the signature of `multBVOmegaRestricted_of` (both moved
  byte-identical from `CoefmassInputs.lean` at `dae0f4b3`).
- `MultBVResidue`, `apDiscrepancy`, `omegaMultLe` (`CPrimeSiteFactorization.lean`), and
  `PhaseFactor.omegaLe`.
- Add helper lemmas freely, in this file or a new `CoefmassOmegaBV*.lean`.  Never weaken a
  statement.  If a statement looks false, stop and write the evidence here instead of editing it.
- No new `axiom`.  No `native_decide`.  No new `maxHeartbeats` above 400000 without a comment.

## Order of work (suggested)

1. **Local algebra and convolution (step 1).**  Define `h` (multiplicative, via
   `Nat.factorization`) and prove `g n = Σ_{b ∣ n} h b * f (n / b)` for `n ≥ 1`.  A clean route
   is via `ArithmeticFunction`: `h * f` is multiplicative (`ArithmeticFunction.IsMultiplicative.mul`),
   so equality with `g` reduces to prime powers
   (`ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers`); both names checked in the
   pinned Mathlib.  Then prove the bound `‖h b‖ ≤ H b`.
2. **Majorant sums (step 2).**  Prove `Σ_{b ≤ X} H b / b ≤ C₁`, and the Rankin tail
   `Σ_{T < b ≤ X} H b / b ≤ C_ε T^{−1/2+ε}`.  An elementary route: every squarefull `b` is
   `u² v³`, and `2^{ω(b)} ≤ d(b)`.  The TSW run's Rankin lemma `smoothCount_rankin`
   (`CoefmassTSWDirect.lean`) and the Euler-product lemma it used are worth reading first.
3. **Discrepancy identity (step 3).**  A finite rearrangement.  Most of the work is the
   `c · b⁻¹ mod e` reindexing (`ZMod.unitOfCoprime`, checked) and the bijection between the sup over
   units and itself.
4. **Assembly (steps 4–6).**  Split `b ≤ √x` / `b > √x`; handle small `x` by enlarging `C`.

## Done when

`lean-treadmill --done-when sorry-free:src/NormalNumbers/CoefmassOmegaBV.lean`, and
`#print axioms multBVOmegaRestricted_of` shows only `propext, Classical.choice, Quot.sound`.
When the sorry closes, remove its waiver in `BarrierAudit.lean` (entry
``PrimeModel.SiteFactor.multBVOmegaRestricted_of``); the audit fails the build otherwise.

## Status

Skeleton only (Opus, attended).  Not launched; launch needs Trevor's go.
