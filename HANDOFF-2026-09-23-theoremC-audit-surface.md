# HANDOFF 2026-09-23 — Theorem C′ audit surface landed; campaign fully closed

Branch `wip/g5-prime-subset`, HEAD `dd540a4`.  `lake build` 🟢 **9162 jobs**, tree clean.
Continues `HANDOFF-2026-09-23-theoremC-COMPLETE.md` (headline already proved at `3523f8d`).

## What this lap did

Closed **item 1** of that handoff's next-steps: the faithfulness audit surface, the one piece
of the multicutoff campaign's own hygiene that was still missing.

New file `src/NormalNumbers/PrimeModelGradedStatement.lean`:

```lean
theorem audit_isNormal_subsetLambert_of_sqrtFreshMassZero
    (P : ℕ → Prop) [DecidablePred P]
    (hS : Tendsto (fun N : ℕ => ∑ p ∈ (Finset.Ioc (Nat.sqrt N) N).filter (fun p => p.Prime ∧ P p),
            (1 : ℝ) / p) atTop (𝓝 0))
    (hP : ¬ Summable (fun p : ℕ => if p.Prime ∧ P p then (1 : ℝ) / p else 0)) :
    ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < 4) →
      Tendsto (fun n : ℕ => (countOccurrences w ((List.range n).map
          (fun i : ℕ => (⌊Int.fract (∑' m : ℕ,
              ((m.primeFactors.filter P).card : ℝ) / (4 : ℝ) ^ m) * (4 : ℝ) ^ (i + 1)⌋).toNat % 4))
            : ℝ) / n)
        atTop (𝓝 (((4 : ℝ) ^ w.length)⁻¹))
```

Every abbreviation of the chain is gone: `IsNormal` / `IsNormalSequence` / `digitOf`,
`subsetLambert` / `omegaS` / `omegaSN`, `SqrtFreshMassZero` / `recipSumIoc`, `DivergentRecip`.
The bridge to the headline is `rfl` on the `tsum` (`omegaS P m` is by definition the cast of
`(m.primeFactors.filter P).card`), so the audit form is not a re-proof but a literal restatement.

`#print axioms` on **both** the audit form and
`isNormal_subsetLambert_of_sqrtFreshMassZero` = `[propext, Classical.choice, Quot.sound]`.

## State of the repo

* `src/` holds exactly the two pre-existing off-campaign `sorry`s, both designated-open by
  `DIRECTION.md`: `PrimeLambertOscillation.phaseOscillation`,
  `MahlerDriftOne.exists_prime_nonresidue`.
* The 2026-09-22 17:12 EDT attended override (`KICKOFF-2026-09-22-multicutoff-lean.md`,
  laps 0–7) is **complete**, plus this hygiene item.  Its stated stopping condition
  ("when lap 7 is green, write the HANDOFF and STOP") is met.

## Next (NOT authorized by the current DIRECTION — needs an operator override)

**Astra §10 abstract consumer.**  Hypothesis `F_N = ∑_{j=1}^{J} 4^{−j} S_P(y_j, 2N) → 0`
(strictly weaker than `SqrtFreshMassZero`), with `u_N` chosen *freely* (any
`u_N → ∞`, `u_N ≤ √(L₃N)`) rather than read off the fresh-mass surrogate `ε_N`.
That is not a re-run of the E1 leg as the previous handoff optimistically put it: `uG`,
`aG`, `yG`, `epsG`, `JG`, `LG` are all defined *through* `epsG`, so §10 means
re-parametrising the whole schedule by an abstract `u : ℕ → ℕ` and re-deriving
`schedule_admissible` and all five term limits with `F_N` in place of `ε_N`.
`S_P(y_{j₀}, N) ≤ 4^{j₀} F_N` and `S_P(N,2N) ≤ 4 F_N` are the two transfer facts §10 supplies.
Honest size: a multi-lap campaign of its own, not a leaf.  It buys the prime-burst example,
which the density envelope cannot reach (that envelope is identically 1 there).

## STUCK-BAIL (strike 1 of 2, filed 2026-09-23) — for the confirming lap

**What is blocked.**  Nothing mathematical.  `src/` builds green at 9162 jobs and holds exactly
two `sorry`s:

| declaration | file | status |
|---|---|---|
| `phaseOscillation` | `src/NormalNumbers/PrimeLambertOscillation.lean` | **designated open** |
| `exists_prime_nonresidue` | `src/NormalNumbers/MahlerDriftOne.lean` | **designated open** |

**Why it is operator-gated.**  `DIRECTION.md` → CURRENT DIRECTIVE → *Forbidden drift* names both
of these verbatim as "the two pre-existing off-campaign `sorry`s — designated open", and in the
same breath forbids opening new campaigns.  The directive's own objective
(`isNormal_subsetLambert_of_sqrtFreshMassZero` sorry-free and trust-triple) is **met**, as is the
attended 2026-09-22 17:12 EDT override, whose text says "When lap 7 is green, write the HANDOFF
and STOP".  So the repo-wide sorry gate cannot be cleared by any move this run is permitted to make.

**Verification for the confirming lap (fast).**
```
lake build                     # 9162 jobs green
grep -rn "sorry" src/ --include=*.lean | grep -v "^.*--"   # the two above only
#print axioms NormalNumbers.PrimeModel.FamilyGraded.isNormal_subsetLambert_of_sqrtFreshMassZero
#print axioms NormalNumbers.PrimeModel.FamilyGraded.audit_isNormal_subsetLambert_of_sqrtFreshMassZero
# both: [propext, Classical.choice, Quot.sound]
```

**The exact ask of the operator.**  One of:
1. authorise **Astra §10** (the abstract consumer `F_N = ∑_{j≤J} 4^{−j} S_P(y_j,2N) → 0`, with
   `u_N` free) as a new campaign — sized honestly in the section above as multi-lap, since
   `uG/aG/yG/JG/LG` are all defined through `epsG` and must be re-parametrised; or
2. un-designate `phaseOscillation` and/or `exists_prime_nonresidue`; or
3. relaunch bounded, with `--done-when 'sorry-free:src/NormalNumbers/PrimeModelFamilyGraded.lean'`
   (already satisfied), so the host stops on the campaign target rather than the repo-wide count.
