# HANDOFF — pointer only

## ⛔ STUCK-BAIL 2026-09-27 (strike 1 of 2) — read this first

**WHAT is blocked:** nothing mathematical.  The scoped objective of this run is **met**:
`NormalNumbers.JointLambert.exists_joint_prime_candidates` in
`src/NormalNumbers/JointLambertPrimeSelection.lean` is proved, sorry-free, `lake build`
green, `#print axioms` = `[propext, Classical.choice, Quot.sound]`.  What is blocked is the
**repo-wide sorry gate**, which keeps declining `box done`.

**WHY it is outside a lap's power (operator-gated):** every remaining `sorry` in `src/`
predates this run and is designated-open / explicitly forbidden —
`SwingC2.lean` (4, audit surface), `SwingC1Log.lean` (2), `SwingC3Rotation.lean` (1),
`PairDecoupleProve.lean` (1, *deliberately* a `sorry` because it is a **conjecture**, not a
formalization gap), plus `MahlerDriftOne` / `PrimeLambertOscillation` named designated-open
in `DIRECTION.md`.  The operator override at the top of `DIRECTION.md` says **"Work only on
prime selection and necessary helpers, no side quests"** and **"Stop when
`exists_joint_prime_candidates` is proved"**.  So no lap of this run may legally touch any
of them: the gate is unsatisfiable here by construction, not merely hard.

**Fast verification for the confirming lap** (three commands, no proof work):
```
grep -n 'sorry' src/NormalNumbers/JointLambertPrimeSelection.lean   # only docstring prose
lake build                                                          # green
echo '#print axioms NormalNumbers.JointLambert.exists_joint_prime_candidates'
```

**EXACTLY what is needed from the operator:** either accept the scoped completion and close
the run, or authorize a new scope.  The next on-path target is already written up: the
elementary paper-§3 divisor-average estimate
`∑_{m<M} τ(u+mA) ≤ 2M(1 + ½ log Y) + 2√Y` for `(u,A) = 1` — the **shared binary tail
majorant**, needing no analytic input, which combines with the `≥ M/(16k⁴)` prime-candidate
count proved this lap to give one commonly-good index by pigeonhole.

Full detail, including how the target is proved: `HANDOFF-joint-lambert.md`; next attack:
`PENDING_WORK.md`.

---


This file is a **thin pointer**, never a second durable overview.

* **Durable overview + axiom ledger** → `STATUS.md`
* **Binding orders (altitude-lap owned, OUTRANKS every handoff)** → `DIRECTION.md` → CURRENT DIRECTIVE
* **Latest strategic synthesis** → `REFLECTION-2026-09-16-campaignB.md`
* **Newest dated baton** → `HANDOFF-2026-09-23-theoremC-reach-and-crosscheck.md`
* **Open items / attack path** → `PENDING_WORK.md` (top section)
* **Frozen plan + estimates** → `ROADMAP.md`

Discover the newest dated baton by glob rather than trusting this line:
`ls HANDOFF-*.md | sort | tail -1`.

---

## ⛔ STUCK-BAIL CONFIRMED (strike 2, filed 2026-09-23) — run halts for the operator

**Full detail + the exact asks:** `HANDOFF-2026-09-23-theoremC-reach-and-crosscheck.md`.

**State.**  `lake build` 🟢 9166 jobs.  `DIRECTION.md` → CURRENT DIRECTIVE objective —
`isNormal_subsetLambert_of_sqrtFreshMassZero` (Theorem C′) sorry-free and trust-triple — is
**MET**, re-verified this run together with its audit surface and the lap-0 deliverables.
`src/` holds exactly the two `sorry`s the directive designates open
(`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_prime_nonresidue`).

**On strike 1 (`b78b343`).**  Its facts were correct; its conclusion that nothing workable
remained was not.  This run landed five additive, sorry-free, trust-triple nodes inside the
ratified kickoff spec — Astra §10's `F_N → 0` from C′'s hypothesis, the double-exponential
block criterion **and its converse** (so the block condition is a *reformulation* of
`SqrtFreshMassZero`, and Astra §10's prime-burst example is already covered by C′), and an
independent NL→Lean faithfulness cross-check whose three discrepancies are now all proved
equivalences.  That in-spec ground is now genuinely worked out.

**WHAT IS NEEDED FROM THE OPERATOR** — any one of:
1. authorise the **Astra §10 consumer** with permission to generalise
   `PrimeModelFamilyGraded.lean` **in place** over a supplied `u : ℕ → ℕ` (feasibility is now
   known good: `hS` enters through exactly five derived facts, so the file is an interface,
   not a weave — but `u_N` is read off `epsG`, and "no existing statement changes" would
   otherwise force a parallel ~1800-line file);
2. authorise a **Mertens campaign** (two-sided `∑_{p≤x} 1/p = log log x + O(1)`, absent from
   mathlib), which is the sole blocker for every strictness/sharpness question about the
   hypothesis;
3. **un-designate** `phaseOscillation` and/or `exists_prime_nonresidue`.


