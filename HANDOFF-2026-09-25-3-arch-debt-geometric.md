# HANDOFF 2026-09-25 session 3 — the C3 archimedean debt driven from Siegel-strength to geometry

**Branch** `wip/c3-mrt`  **HEAD** `0701e3a`  **Working tree** clean  **`lake build`** green (9442 jobs)
No `sorry` added this session; every new statement is `#print axioms`-clean (`propext`,
`Classical.choice`, `Quot.sound` only).  All work is in `src/NormalNumbers/C3MrtArchFaithful.lean`
plus `PENDING_WORK.md` (per-lap detail) and a one-line audit fix in `C3MrtTTDefect.lean`.

## What this session did

The operator's scoped objective — the RESTATEMENT run, items (a)-(c) — was **already complete** at
session start (`25149e0`, `HANDOFF-2026-09-25-tt-interface-restated.md`).  I verified it end to end
and closed the one real gap (5 of the 14 defect/guard/bridge statements were not kernel-audited);
see lap-107 note below.  The `box done` gate then correctly refused (open obligations remain), so
the rest of the session was crux work on the archimedean side, per `DIRECTION.md`.

**Net effect: the archimedean obligation went from one opaque `FaithfulArchLower` to three named
statements, of which two are settled in character and the third is no longer analytic.**

    conjC3_of_geom_input_pairing :
      (∀ A > 0, ∀ b ≥ 3, ∀ K, KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K) →
      UniformResonantMass → CharPrimeSumLogQ D → BlockPhasePairing d → ConjC3     (d < 1)

* `UniformResonantMass` — the route's analytic input *before* the defect was found.  Not new debt.
* `CharPrimeSumLogQ D` — a **`log`**-sized bound on the twisted prime sum in the narrow range.
  Classical and **Siegel-free** at `t = 0` (`L(1,χ) ≫ q^{-1/2}`).
* `BlockPhasePairing d` — purely geometric: on every initial segment of every dyadic block, the
  `χ`-surviving primes admit an injective self-map whose twist phases are separated.

## The laps (detail in PENDING_WORK.md)

| lap | advance |
|---|---|
| 107 | Completed the `#print axioms` audit of the defect/restatement surface (5 unprinted guards). |
| 108 | `NonPrincipalLocalBound` — narrow non-principal debt with **no `X`** on the right.  `depthRoot_zero_emod` + `exists_uniform_narrow_const`: the `h'`-uniformity `FaithfulArchLower` demands is now a THEOREM (`ee` is 1-periodic ⇒ ≤ `b` values ⇒ `Finset.sup'`). |
| 109 | `TwistedPrimeSumSmall` unifies the narrow-non-principal and wide debts (same object, different corner).  `twistedPrimeSum_principal_zero` guards that the excluded corner must be excluded. |
| 110 | **The multiplier `z` eliminated.**  `1 − w^b = (1−w)(1+…+w^{b−1})` ⇒ `1 − Re(w^b) ≤ b²(1 − Re w)` ⇒ `ttPretentiousSumChar_pow_le`.  Debt becomes `OneNonPretentious` (constant function `1`; base-free, so ONE statement serves every base) + the corner `RootOrderCase`. |
| 111 | **De-escalation.**  In TT's range `log q ≤ (1/125)·log log X`, so a `log`-sized bound suffices (`CharPrimeSumLogQ`), which at `t = 0` is classical.  This **corrected** lap 110's claim that the real-character corner is the Siegel-zero case: the conductor is not the obstruction. |
| 112 | **Refuted:** the wide range cannot be closed by `|log L(1+it,χ)| ≤ log log(q(2+|t|)) + O(1)` — for any polynomial twist range that equals `log log X + O(1)`, the same size as the total prime mass, so `κ = 0`.  The `log log` scale collapses.  Reduced instead to a per-dyadic-block saving (`WideBlockSaving`). |
| 113 | **Abel transfer** (`norm_sum_smul_le_of_partial_bound`): an initial-segment saving transfers to the `1/p`-weighted sum with the SAME constant (two `sum_range_by_parts` give identical weight combinations).  Debt becomes reciprocal-free: `WideBlockPartial`. |
| 114 | **The pairing bound** (`norm_sum_le_of_pairing`): an injective self-map of a finite set is a permutation, so `2∑u_p = ∑(u_p + u_{σ p})` and separation `Re(u_p conj u_{σ p}) ≤ d < 1` gives `‖∑u_p‖ ≤ (√(2+2d)/2)#S`.  Debt becomes `BlockPhasePairing` — geometric. |

## Next steps (in order)

1. **Construct the matching** for `BlockPhasePairing`.  Consecutive `log p` gaps in a dyadic block
   are `≍ 2^{-j}`, so `t·(log p_{i+1} − log p_i) ≍ |t| 2^{-j}`.
   * Branch `|t| 2^{-j} ≳ 1`: neighbouring primes are already phase-separated; `σ` = shift by one
     within maximal runs is an injective self-map.  **Needs no prime counting — do this first.**
   * Branch `|t| 2^{-j} ≪ 1`: pair `p_i ↔ p_{i+k}` with `k ≍ 2^j/|t|`; needs only `#block ≥ 2k`,
     i.e. a Chebyshev lower bound.
2. `CharPrimeSumLogQ` at `t = 0` from `L(1,χ) ≫ q^{-1/2}`.  Mathlib has only the qualitative
   `DirichletCharacter.LFunction_apply_one_ne_zero`, so this needs the elementary
   `f = 1 ∗ χ ≥ 0` argument, or it stays a cited classical bound.
3. `RootOrderCase` / `OneNonPretentious` (lap 110's route) is an ALTERNATIVE to laps 111-114's
   route, not a prerequisite.  Both reach `FaithfulArchLower`; keep both, they are cheap.

## Do NOT re-attempt (refuted this session, with reasons in PENDING_WORK.md)

* Discharging the non-principal narrow range from mathlib's L-function non-vanishing — it is
  qualitative, with no uniformity in `q` or `t`.
* Restricting to `p ≡ 1 (mod q)` for the non-principal saving — gives `κ/φ(q)`, which dies.
* The root-of-unity averaging `∑_{j<b} z^j = 0` — gives the average over `j`, not the saving at
  `j = 1`, and the bad case lands back on `q`-uniform prime equidistribution.
* Any `log log(q(2+|t|))` upper bound for the wide range — scale-degenerate (lap 112).

Forbidden drift from `DIRECTION.md` is unchanged and was respected: no `K ≥ 3`-from-`K = 2`
attempt, no re-attack on TT's exceptional set, no new fixed-`K` `Tendsto` statements, no
`QuantDepthElliottGen` revival, and nothing existing was weakened, renamed or deleted.
